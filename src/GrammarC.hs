module GrammarC where

import Data.Function
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Char
import qualified Data.Set as S

import Debug.Trace

import qualified PGF2
import qualified PGF2.Internal as I

--------------------------------------------------------------------------------
-- grammar types

-- name

type Name = String
type Cat  = PGF2.Cat -- i.e. String
type SeqId = Int

-- concrete category

data ConcrCat = CC (Maybe Cat) I.FId -- i.e. Int
  deriving ( Ord, Eq )

instance Show ConcrCat where
  show (CC (Just cat) fid) = cat ++ "_" ++ show fid 
  show (CC Nothing fid)    = "_" ++ show fid 

-- tree

data Tree
  = App{ top :: Symbol, args :: [Tree] }
 deriving ( Eq, Ord )

-- symbol

data Symbol
  = Symbol
  { name :: Name
  , seqs :: [SeqId]
  , typ  :: ([Cat], Cat)
  , ctyp :: ([ConcrCat],ConcrCat)
  }
 deriving ( Eq, Ord )

arity :: Symbol -> Int
arity = length . fst . ctyp

hole :: ConcrCat -> Symbol
hole c = Symbol ("(" ++ show c ++ ")") [] ([], "") ([],c)

isHole :: Symbol -> Bool
isHole (Symbol "()" _ _ _) = True
isHole _                   = False

-- grammar

data Grammar
  = Grammar
  {
    parse        :: String -> [Tree]
  , readTree     :: String -> Tree
  , linearize    :: Tree -> String
  , tabularLin   :: Tree -> [(String,String)]
  , concrCats    :: [(PGF2.Cat,I.FId,I.FId,[String])]
  , coercions    :: [(ConcrCat,ConcrCat)]
  , startCat     :: Cat
  , symbols      :: [Symbol]
  , concrSeqs    :: SeqId -> [Either String (Int,Int)] 
  , feat         :: FEAT
  }

--------------------------------------------------------------------------------
-- analyzing contexts

contextsFor :: Grammar -> ConcrCat -> ConcrCat -> [Tree -> Tree]
contextsFor gr top hole =
  concat
  [ map (path2context . snd) paths
  | (c,paths) <- M.toList $ fix improve start
  , c == top
  ]
 where
  -- all non-empty categories
  goodCats =
    [ c
    | c <- S.toList $ S.fromList $
           hole :
           [ c
           | f <- symbols gr
           , let (as,b) = ctyp f
           , c <- b:as
           ] ++
           [ c
           | (b,a) <- coercions gr -- !now flipped
           , c <- [a,b]
           ]
    , any ((>0) . featCard gr c) [0..25] -- 15 is arbitrary
    ]

  -- all symbols with only good arguments
  goodSyms =
    [ f
    | f <- symbols gr
    , all (\t -> t `elem` goodCats) (fst (ctyp f))
    ]
 
  -- length of string vector for the hole type
  arHole =
    head $
    [ length (seqs f)
    | f <- symbols gr
    , snd (ctyp f) == hole
    ] ++
    error ("no symbol found with result type " ++ show hole)

  -- initial table we start our fixpoint iteration with
  start =
    M.fromList
    [ (c, if c == hole
            then [([S.fromList [i] | i <- [0..arHole-1]],[])]
            else [])
    | c <- goodCats
    ]

  improve tab =
    M.fromList
    [ (c,paths `imprs`
           ( [ (apply (f,i) str, (f,i):fis)
             | f <- goodSyms
             , snd (ctyp f) == c
             , (t,i) <- fst (ctyp f) `zip` [0..]
             , (str,fis) <- tab M.! t
             ] ++
             [ (str, fis)
             | (b,a) <- coercions gr -- !now flipped
             , b == c
             , Just fs <- [M.lookup a tab]
             , (str,fis) <- fs
             ]     
           ))
    | (c,paths) <- M.toList tab
    ]
   where
    apply (f,i) str =
      [ S.fromList
        [ s
        | Right (x,y) <- concrSeqs gr sq
        , x == i
        , s <- S.toList (str !! y)
        ]
      | sq <- seqs f
      ]

    paths `imprs` paths' =
      foldr impr paths $ M.toList $ M.fromList $ reverse $ map snd $ sort $
        [ (size p,q) | q@(_,p) <- paths' ]
     where
      (str',path') `impr` paths
        | any (`covers` str') (map fst paths) =
          paths
        
        | otherwise =
          (str',path') : filter (not . (str' `covers`) . fst) paths

      str1 `covers` str2 =
        and [ s2 `S.isSubsetOf` s1 | (s1,s2) <- str1 `zip` str2 ]

      size = sum . map (\f -> arity f - 1) . map fst

  path2context []          x = x
  path2context ((f,i):fis) x =
    App f
    [ if j == i
        then path2context fis x
        else head (featAll gr t)
    | (t,j) <- fst (ctyp f) `zip` [0..]
    ]

  fix f x | fx == x   = x
          | otherwise = fix f fx
         where
          fx = f x

--------------------------------------------------------------------------------
-- name

mkName, mkCat :: String -> Name
mkName = id
mkCat  = id

-- tree

instance Show Tree where
  show = showTree --CCats

showTree :: Tree -> String
showTree (App a []) = show a
showTree (App f xs) = unwords (show f : map showTreeArg xs)
  where showTreeArg (App a []) = show a
        showTreeArg t = "(" ++ showTree t ++ ")"

showTreeCCats :: Tree -> String
showTreeCCats (App a []) = showCC a
showTreeCCats (App f xs) = unwords (showCC f : map showTreeArg xs)
 where 
  showTreeArg (App a []) = showCC a
  showTreeArg t = "(" ++ showTreeCCats t ++ ")"

showCC :: Symbol -> String
showCC a = show a ++ ":" ++ intercalate "→" args
 where
  (xs,y) = ctyp a
  args = map show $ xs ++ [y]

catOf :: Tree -> Cat
catOf (App f _) = snd (typ f)

-- symbol

instance Show Symbol where
  show f = name f --CId is just a String in PGF2

-- grammar

toGrammar :: PGF2.PGF -> Grammar
toGrammar pgf =
  let gr =
        Grammar
        {
         parse = \s ->
            case PGF2.parse lang (PGF2.startCat pgf) s of 
              PGF2.ParseOk es_fs -> map (mkTree.fst) es_fs
              PGF2.ParseFailed i s -> error s
              PGF2.ParseIncomplete -> error "Incomplete parse"

        , readTree = \s ->
            case PGF2.readExpr s of
              Just t  -> mkTree t
              Nothing -> error "readTree: no parse"

        , linearize = \t -> 
            PGF2.linearize lang (mkExpr t)

        , tabularLin = \t ->
            PGF2.tabularLinearize lang (mkExpr t)

        , startCat =
            mkCat (PGF2.startCat pgf)

        , concrCats = 
            I.concrCategories lang

        , symbols = 
            symbs

        , coercions = 
            coerces

        , concrSeqs = 
            map cseq2Either . I.concrSequence lang

        , feat =
            mkFEAT gr
        }
   in gr
 where
  symbs = [ Symbol { 
               name = nm,
               seqs = sqs,
               ctyp = (cArgTypes, cResType),
               typ = (map abstrCat cArgTypes, abstrCat cResType) } --this takes care of coercions

             | (cat,bg,end,_) <- I.concrCategories lang
             , resFid <- [bg..end] 
             , I.PApply funId pargs <- I.concrProductions lang resFid
             , let cArgTypes = [ CC (getGFCat fid) fid | I.PArg _ fid <- pargs ]
             , let cResType = CC (getGFCat resFid) resFid 
             , let (nm,sqs) = I.concrFunction lang funId ]

  cseq2Either (I.SymKS tok) = Left tok
  cseq2Either (I.SymCat x y) = Right (x,y)
  cseq2Either x = Left (show x)

  lang = snd $ head $ M.assocs $ PGF2.languages pgf  

  coerces = [ ( CC Nothing afid
              , CC ccat cfid )
              | afid <- [0..I.concrTotalCats lang]
              , I.PCoerce cfid  <- I.concrProductions lang afid 
              , let ccat = getGFCat cfid ] --can there be multiple coercions, like X -> Y -> Z?

  mkCat  tp  = cat where (_, cat, _) = PGF2.unType tp

  mkExpr (App n []) | not (null s) && all isDigit s =
    PGF2.mkInt (read s)
   where
    s = show n

  mkExpr (App f xs) =
    PGF2.mkApp (name f) [ mkExpr x | x <- xs ]

  abstrCat :: ConcrCat -> Cat
  abstrCat c@(CC Nothing _)  = let Just ccat = lookup c coerces 
                                in abstrCat ccat
  abstrCat (CC (Just cat) _) = cat
  
  getGFCat :: I.FId -> Maybe Cat
  getGFCat fid = 
    let cats = nub [ cat | (cat,bg,end,xs) <- I.concrCategories lang
                         , fid `elem` [bg..end] ]
     in case cats of 
          [] -> Nothing -- means it's coercion
          (x:xs) -> Just x
   
  mkAmbTree :: PGF2.Expr -> AmbTree
  mkAmbTree t =
    case PGF2.unApp t of
      Just (f,xs) -> AmbApp (lookupSymbs f) [ mkAmbTree x | x <- xs ]
      _           -> error (PGF2.showExpr [] t)



  at2tree :: AmbTree -> Tree
  at2tree at = 
    case (iterate reduce) at !! 100 of
      AmbApp [x] ts -> App x [ at2tree t | t <- ts ]
      AmbApp []   _ -> error "mkTree: empty tree"
      AmbApp (x:_) ts -> trace ("\n*** mkTree: ambiguous tree " ++ show x ++ " ***\n") $
                        App x [ at2tree t | t <- ts ]
 
   where 
    reduce at = AmbApp (reduceSymbol at) [ reduce t | t <- aargs at ]

  mkTree :: PGF2.Expr -> Tree
  mkTree = at2tree . mkAmbTree


  lookupSymbs :: Name -> [Symbol]
  lookupSymbs name = lookupAll (map symb2table symbs) name
 
  symb2table s@(Symbol nm _ _ _) = (nm,s)

  lookupAll :: (Eq a) => [(a,b)] -> a -> [b]
  lookupAll kvs key = [ v | (k,v) <- kvs, k==key ]

  coerce :: ConcrCat -> [ConcrCat]
  coerce ccat = case lookupAll coerces ccat of
                    [] -> [ccat]
                    xs -> xs
  

  reduceSymbol :: AmbTree -> [Symbol]
  reduceSymbol f@(AmbApp xs args) =
    if all (\a -> length (atop a) == 1) args
      then 
       let reduced = [ symbol
                       | symbol <- atop f
                       , let argTypes = map coerce $ fst (ctyp symbol) 
                       , let resTypes = map coerce $ [ snd $ ctyp s | (AmbApp [s] _) <- args ] 
                       , and [ intersect a r /= [] 
                               | (a,r) <- zip argTypes resTypes ]
                     ]
        in case reduced of
                  [x] -> [x]
                  _   -> xs
      else xs

data AmbTree = AmbApp { atop :: [Symbol], aargs :: [AmbTree] } 

readGrammar :: FilePath -> IO Grammar
readGrammar file =
  do pgf <- PGF2.readPGF file
     return (toGrammar pgf)


  

  --mkType cat = PGF2.mkType [] cat []



  -- Symbol f [] ([mkCat x | (_,_,x) <- xs],y) [????]

   --where
   -- Just ft    = PGF2.functionType pgf f -- functionType :: PGF -> Fun -> Maybe Type
   -- (xs, y, _) = PGF2.unType ft
   -- foo = "* " ++ show xs ++ ", " ++ y ++ " *"

-- FEAT-style generator magic

type FEAT = [ConcrCat] -> Int -> (Integer, Integer -> [Tree])

-- compute how many trees there are of a given size and type
featCard :: Grammar -> ConcrCat -> Int -> Integer
featCard gr c n = featCardVec gr [c] n

-- generate the i-th tree of a given size and type
featIth :: Grammar -> ConcrCat -> Int -> Integer -> Tree
featIth gr c n i = head (featIthVec gr [c] n i)

-- generate all trees (infinitely many) of a given type
featAll :: Grammar -> ConcrCat -> [Tree]
featAll gr c = [ featIth gr c n i | n <- [0..], i <- [0..featCard gr c n-1] ]

-- compute how many tree-vectors there are of a given size and type-vector
featCardVec :: Grammar -> [ConcrCat] -> Int -> Integer
featCardVec gr cs n = fst (feat gr cs n)

-- generate the i-th tree-vector of a given size and type-vector
featIthVec :: Grammar -> [ConcrCat] -> Int -> Integer -> [Tree]
featIthVec gr cs n i = snd (feat gr cs n) i

mkFEAT :: Grammar -> FEAT
mkFEAT gr = catList
 where
  catList' :: FEAT
  catList' [] 0 = (1, \0 -> [])
  catList' [] _ = (0, error "indexing in an empty sequence")

  catList' [c] s =
    parts $ 
          [ (n, \i -> [App f (h i)])
          | s > 0 
          , f <- symbols gr
          , let (xs,y) = ctyp f
          , y == c
          , let (n,h) = catList xs (s-1)
          ] ++
          [ catList [x] s -- put (s-1) if it doesn't terminate
          | s > 0 
          , (y,x) <- coercions gr -- !now flipped
          , y == c
          ]

  catList' (c:cs) s =
    parts [ (nx*nxs, \i -> hx (i `mod` nx) ++ hxs (i `div` nx))
          | k <- [0..s]
          , let (nx,hx)   = catList [c] k
                (nxs,hxs) = catList cs (s-k)
          ]

  catList :: FEAT
  catList = memoList (memoNat . catList')
   where
    -- all possible categories of the grammar
    cats = S.toList $ S.fromList $
           [ x | f <- symbols gr
               , let (xs,y) = ctyp f
               , x <- y:xs ] ++
           [ z | (y,x) <- coercions gr -- !now flipped
               , z <- [x,y] ]

    memoList f = \cs -> case cs of
                    []   -> fNil
                    a:as -> fCons a as
     where
      fNil  = f []
      fCons = (tab M.!)
      tab   = M.fromList [ (c, memoList (f . (c:))) | c <- cats ]

    memoNat f = (tab!!)
     where
      tab = [ f i | i <- [0..] ]

  parts []          = (0, error "indexing outside of a sequence")
  parts ((n,h):nhs) = (n+n', \i -> if i < n then h i else h' (i-n))
   where
    (n',h') = parts nhs

--------------------------------------------------------------------------------
-- compare two grammars

diffCats :: Grammar -> Grammar -> [(Cat,[Int],[String],[String])]
diffCats gr1 gr2 = 
  [ (acat1,[difFid c1, difFid c2],labels1  \\ labels2,labels2 \\ labels1)
    | c1@(acat1,sfid1,efid1,labels1) <- concrCats gr1
    , c2@(acat2,sfid2,efid2,labels2) <- concrCats gr2
    , difFid c1 /= difFid c2 -- different amount of concrete categories
      || labels1 /= labels2 -- or the labels are different
    , acat1==acat2 ]

 where
  difFid (_,i,j,_) = 1 + (j-i)


