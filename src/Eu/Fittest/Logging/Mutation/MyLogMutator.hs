{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

module Eu.Fittest.Logging.Mutation.MyLogMutator where

import Eu.Fittest.Logging.XML.XMLparser
import Eu.Fittest.Logging.XML.Event
import Eu.Fittest.Logging.XML.AppEvent
import Eu.Fittest.Logging.XML.LowEvent
import Eu.Fittest.Logging.XML.Value
import Eu.Fittest.Logging.XML.EventLog

import Debug.Trace

-- general Haskell imports
import Data.List
import Data.Maybe
import Data.Char
import Control.Monad.Random
import Control.Monad
import Control.Applicative
import Safe

import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen

type Mutant a = Rand StdGen a

deleteNth :: Int -> [a] -> [a]
deleteNth i as = let (las, ras) = splitAt i as
                 in  las ++ tailDef [] ras

replaceNth :: Int -> a -> [a] -> [a]
replaceNth i a as = let (las, ras) = splitAt i as
                    in  las ++ [a] ++ tailDef [] ras

getNRandsFromList :: Int -> Int -> IO [Int]
getNRandsFromList n len  = getNRandsFromList' n len [] where
  getNRandsFromList' :: Int -> Int -> [Int] -> IO [Int]
  getNRandsFromList' 0 len gs = return gs
  getNRandsFromList' n len gs
    | n <= len = do k <- randomRIO (0, len - 1)
                    if (k `elem` gs)
                      then getNRandsFromList' n len gs
                      else getNRandsFromList' (n-1) len (k:gs)
    | otherwise = getNRandsFromList' len len []
            

-- | precondition i < j
swapTwoInList :: [a] -> (Int, Int) -> [a]
swapTwoInList as (i,j) =
  let (las, ai:ras) = splitAt i as
      (lras, aj:rras)  = splitAt (j-i-1) ras
  in  las ++ [aj] ++ lras ++ [ai] ++ rras   

chooseNeighbour :: [a] -> Int -> Int
chooseNeighbour as i
  | i < length as = if (i == (length as) - 1) then i-1 else i+1
  | otherwise     = error "index is out of the list boudaries"

isGivenEvent :: String -> Event_ -> Bool
isGivenEvent ename (AE apev) = (fromJust $ getAppEventTargetID apev) == ename

replaceEventName :: String -> Event_ -> Event_
replaceEventName ntarget (AE (AppEvent_ t (Obj_ et (id:(FieldValTy_ fn target ft):fss)) st))
  = (AE (AppEvent_ t (Obj_ et (id:(FieldValTy_ fn (show ntarget) ft):fss)) st))

isGivenVaraible :: String -> Field_ -> Bool
isGivenVaraible var fld = fieldName fld == var

getStateVarValue :: String -> Value_ -> Field_
getStateVarValue vname (Obj_ _ (_:vars)) = fromJust $ find (isGivenVaraible vname) vars
  
replaceStateVarValue :: Field_ -> Event_ -> Event_
replaceStateVarValue new_value (AE app_ev@(AppEvent_ _ _ obj@(Obj_ st_flag (id:vars)))) =
  let vname  = fieldName new_value
      var_id = fromJust $ findIndex (isGivenVaraible vname) vars
      vars'  = replaceNth var_id new_value vars
  in  AE app_ev{aeSmodel=obj{ofields=(id:vars')}} 
      
swapTwoInListWith :: (a -> a -> a) -> [a] -> (Int, Int) -> [a]
swapTwoInListWith pr as (i,j) =
  let (las, ai:ras) = splitAt i as
      (lras, aj:rras)  = splitAt (j-i-1) ras
  in  las ++ [pr ai aj] ++ lras ++ [pr aj ai] ++ rras   
                       
-- | RLE: removes N arbitrarily chosen log entries
-- | precondition: N <= |log|   
removeNEntries :: Int -> [Event_] -> Mutant [Event_]
removeNEntries 0 evs = return evs
removeNEntries i evs = do
  k <- getRandomR (0, (length evs) - 1)
  let evs' = deleteNth k evs
  removeNEntries (i-1) evs'

-- | RLET: removes N arbitrarily chosen log entries of a specified type
-- | precondition: N <= |log|   
removeNTypeEntries :: String -> Int -> [Event_] -> IO [Event_]
removeNTypeEntries typ i evs = do
  let idsOfGivenType = findIndices (isGivenEvent typ) evs
          
      genRemoveIds :: [Int] -> Int -> [Int] -> IO [Int]
      genRemoveIds [] i gs = return gs
      genRemoveIds rs i gs =
        if i > 0
        then do k <- randomRIO (0, (length rs) - 1)
                let rs' = deleteNth k rs
                genRemoveIds rs' (i-1) (rs!!k:gs)
        else return gs        
        
      removeNTypeEntries' :: [Int] -> [Event_] -> Int -> IO [Event_]
      removeNTypeEntries' rs es i = do
        ks <- genRemoveIds rs i []
        let es' = filter (\(n,_) -> n `notElem` ks) $ zip [0..] es
        return $ map snd es'    
  removeNTypeEntries' idsOfGivenType evs i 

removeLogSubstring :: [Event_] -> IO [Event_]
removeLogSubstring evs = do
  k <- randomRIO (0, (length evs) - 1)
  l <- randomRIO (k+1, (length evs) - 1)
  let evs' = filter (\(i,e) -> i `elem` [k .. l]) $ zip [0..] evs
  return $ map snd evs'


-- | STE: swap two arbitrarily chosen log entries given number of times   
swapTwoLogEntries :: Int -> [Event_] ->  IO [Event_]
swapTwoLogEntries 0 evs = return evs
swapTwoLogEntries i evs = do
  [ki,kj] <- getNRandsFromList 2 (length evs)
  swapTwoLogEntries (i-1) (swapTwoInList evs (ki,kj))

-- | STAE: swap two adjacent arbitrarily chosen log entries given number of times   
swapTwoAdjLogEntries :: Int -> [Event_] ->  IO [Event_]
swapTwoAdjLogEntries 0 evs = return evs
swapTwoAdjLogEntries i evs = do
  [ki] <- getNRandsFromList 1 (length evs)
  swapTwoLogEntries (i-1) (swapTwoInList evs (ki, chooseNeighbour evs ki))
    
-- | STEv: swap two arbitrarily chosen events given number of times   
swapTwoEvents :: Int -> [Event_] ->  IO [Event_]
swapTwoEvents 0 evs = return evs
swapTwoEvents i evs = do
  [ki,kj] <- getNRandsFromList 2 (length evs)
  let projEvent (AE (AppEvent_ t1 ev1 st1)) (AE (AppEvent_ _ ev2 _)) = (AE (AppEvent_ t1 ev2 st1)) 
  swapTwoLogEntries (i-1) (swapTwoInListWith projEvent evs (ki,kj))


-- | STAEv: swap two adjacent arbitrarily chosen events given number of times   
swapTwoAdjEvents :: Int -> [Event_] ->  IO [Event_]
swapTwoAdjEvents 0 evs = return evs
swapTwoAdjEvents i evs = do
  [ki] <- getNRandsFromList 1 (length evs)
  let projEvent (AE (AppEvent_ t1 ev1 st1)) (AE (AppEvent_ _ ev2 _)) = (AE (AppEvent_ t1 ev2 st1)) 
  swapTwoLogEntries (i-1) (swapTwoInListWith projEvent evs (ki, chooseNeighbour evs ki))


-- | STSt: swap two arbitrarily chosen states given number of times   
swapTwoStates :: Int -> [Event_] ->  IO [Event_]
swapTwoStates 0 evs = return evs
swapTwoStates i evs = do
  [ki,kj] <- getNRandsFromList 2 (length evs)
  let projState (AE (AppEvent_ t1 ev1 st1)) (AE (AppEvent_ _ _ st2)) = (AE (AppEvent_ t1 ev1 st2)) 
  swapTwoLogEntries (i-1) (swapTwoInListWith projState evs (ki,kj))


-- | STASt: swap two adjacent arbitrarily chosen states given number of times   
swapTwoAdjStates :: Int -> [Event_] ->  IO [Event_]
swapTwoAdjStates 0 evs = return evs
swapTwoAdjStates i evs = do
  [ki] <- getNRandsFromList 1 (length evs)
  let projState (AE (AppEvent_ t1 ev1 st1)) (AE (AppEvent_ _ _ st2)) = (AE (AppEvent_ t1 ev1 st2)) 
  swapTwoLogEntries (i-1) (swapTwoInListWith projState evs (ki, chooseNeighbour evs ki))

-- | STVa: swap values of a variable in two states
swapTwoVals :: String -> [Event_] -> IO [Event_]
swapTwoVals var evs = do
  [ki,kj] <- getNRandsFromList 2 (length evs)
  let kiSt  = aeSmodel $ unAppEvent $ evs!!ki
      kjSt  = aeSmodel $ unAppEvent $ evs!!kj
      kiVar = getStateVarValue var kiSt
      kjVar = getStateVarValue var kjSt
  return $ foldr (\(i, e) es ->  replaceNth i e es) evs $ zip [ki, kj] $ (zipWith replaceStateVarValue [kjVar, kiVar]) [evs!!ki, evs!!kj]

-- | STAVa: swap values of a variable in two adjacent states
swapTwoValsAdjSt :: String -> [Event_] -> IO [Event_]
swapTwoValsAdjSt var evs = do
  [ki] <- getNRandsFromList 1 (length evs)
  let kj    = chooseNeighbour evs ki
      kiSt  = aeSmodel $ unAppEvent $ evs!!ki
      kjSt  = aeSmodel $ unAppEvent $ evs!!kj
      kiVar = getStateVarValue var kiSt
      kjVar = getStateVarValue var kjSt
  return $ foldr (\(i, e) es ->  replaceNth i e es) evs $ zip [ki, kj] $ (zipWith replaceStateVarValue [kjVar, kiVar]) [evs!!ki, evs!!kj]
  
  
-- | REvN: replace one event with given name
replaceOneEventName ::  String -> String -> [Event_] -> IO [Event_]
replaceOneEventName ev1 ev2  evs = do
  let idsOfGivenType = findIndices (isGivenEvent ev1) evs
  [ki] <- getNRandsFromList 1 (length idsOfGivenType)
  let evs' = replaceNth (idsOfGivenType!!ki) (replaceEventName ev2 (evs!!(idsOfGivenType!!ki))) evs
  return evs'

-- | RAEvN: replace all events with given name
replaceAllEventName ::  String -> String -> [Event_] -> IO [Event_]
replaceAllEventName ev1 ev2  evs = do
  let idsOfGivenType = findIndices (isGivenEvent ev1) evs
      evs' = foldr (\i evs_ -> replaceNth i (replaceEventName ev2 (evs_!!i)) evs_) evs idsOfGivenType
  return evs'    

-- | The list of state variable mutators, which are dependent on the variable's type  
incValByOne :: String -> Value_ -> Value_
incValByOne  = undefined

decValByOne :: String -> Value_ -> Value_
decValByOne = undefined


-- | CRVa & randomly change a variable's value
varRandomChange :: Int -> String -> [Event_] -> IO [Event_]
varRandomChange ie var evs = do
  let ithEventVarVal = getStateVarValue var $ aeSmodel $ unAppEvent $ evs!!ie
  updFld <- randFieldChange ithEventVarVal
  let updEv = replaceStateVarValue updFld (evs!!ie)
  return $ replaceNth ie updEv evs

randFieldChange :: Field_ -> IO Field_
randFieldChange (FieldValTy_ nm val tp) = do
  valNew <- generate $ case tp of
    "int"     -> liftM show (arbitrary :: Gen Int)
    "String"  -> (vectorOf (length val) arbitrary) :: Gen String
    otherwise -> error "undefined type of the field"
  return (FieldValTy_ nm valNew tp)
randFieldChange obj@(FieldObj_ nm (Obj_ on flds))
  | (length flds) == 1 = return obj
  | otherwise          = do fi     <- randomRIO (1, (length flds) - 1)
                            fiNew <- randFieldChange (flds!!fi)
                            let flds' = replaceNth fi fiNew flds
                            return $ FieldObj_ nm (Obj_ on flds')
randFieldChange (FieldXref_ _ _) = error "unobserved case of FieldXref_ in randFieldChange"
   
instance Arbitrary Field_ where
  arbitrary = undefined

type EvSetCardinal = Int
type VrSetCardinal = Int
type MutSetCardinal = (EvSetCardinal, VrSetCardinal)



-- newtype Events a = Events {unEvents :: [Event_]}

-- class Mutations e where
--   genMutations :: (e -> e) -> Events e -> [Events e]

-- instance Mutations Event_ where
--   genMutations mOp (Events (ev:evs)) =
--     (Events $ (mOp ev):evs)
--     :
--     [Events $ ev:(unEvents evs') | evs' <- genMutations mOp (Events evs)]  

-- instance Mutations Field_ where
--   genMutations mOp (Events (ev:evs)) =
--     (Events $ (mOp ev):evs)
--     :

class Mutations ce e | ce -> e where
  genMutations :: (e -> (String, e)) -> ce -> [(String, ce)]

data Events = Events {unEvents :: [Event_]}
            deriving Show

-- instance Mutations Events Event_ where
--     genMutations mOp (Events (ev:evs)) =
--       (Events $ (mOp ev):evs)
--       :
--       [Events $ ev:(unEvents evs') | evs' <- genMutations mOp (Events evs)]  

-- instance Mutations Events Field_ where
--   genMutations mOp (Events [])       = []
--   genMutations mOp (Events (ev:evs)) =
--     [Events (ev':evs) | ev' <- genMutations mOp ev, ev /= ev']
--     ++
--     [Events (ev:(unEvents evs')) | evs' <- genMutations mOp (Events evs)]


instance Mutations [Event_] Field_ where
  genMutations mOp ([])     = []
  genMutations mOp (ev:evs) =
    [(fst ev', (snd ev'):evs) | ev' <- genMutations mOp ev, ev /= (snd ev')]
    ++
    [(fst evs', (ev:(snd evs'))) | evs' <- genMutations mOp evs]


instance Mutations Event_ Field_ where
  genMutations mOp (AE ae@(AppEvent_ t ev o@(Obj_ on fields))) =
    case fields of
      (i:f:flds) -> [(fst f', AE (AppEvent_ t ev (Obj_ on (i:(snd f'):flds)))) | f' <- genMutations mOp f, f /= (snd f')]
                    ++
                    [(fst flds', AE (AppEvent_ t ev (Obj_ on (i:f:(tail $ ofields $  aeSmodel $ unAppEvent $ snd flds'))))) | flds' <- genMutations mOp (AE (AppEvent_ t ev (Obj_ on (i:flds))))]
      [id]       -> [] 


instance Mutations Value_ Field_ where
  genMutations mOp (Obj_ on f) = case f of
    (id:fld:flds) -> [(fst fld', Obj_ on (id:(snd fld'):flds))
                     | fld' <- genMutations mOp fld, snd fld' /= fld]
                     ++
                     [(fst flds', Obj_ on (id:fld:(tailDef [] $ ofields $ snd flds')))
                     | flds' <- genMutations mOp (Obj_ on (id:flds))]
    [id]          -> []


instance Mutations Field_ Field_ where
  genMutations mOp f@(FieldValTy_ _ _ _ ) = [mOp f]
  genMutations mOp f@(FieldObj_ nm v)     =
    (if ((fst $ mOp f) == "SKP") then [] else [mOp f])
    ++
    [(fst v', FieldObj_ nm (snd v')) | v' <- genMutations mOp v, snd v' /= v]

    -- case v of
    -- (id:fld:flds) -> (if (fst $ mOp f) == "SKP" then [] else [mOp f])
    --                  ++
    --                  (trace ("\n1: --> " ++ (show $ genMutations mOp fld)) [(fst fld', FieldObj_ nm (Obj_ on (id:(snd fld'):flds))) | fld' <- genMutations mOp fld, fld /= snd fld'])
    --                  ++
    --                  (trace ("\n2: --> " ++ (show $ genMutations mOp (FieldObj_ nm (Obj_ on (id:flds))))) ([(fst flds', FieldObj_ nm (Obj_ on (id:fld:(tailDef [] $ ofields $ getFldObjVal $ snd flds'))))| flds' <- genMutations mOp (FieldObj_ nm (Obj_ on (id:flds)))]))
    -- [id]          ->  []

testMut :: Field_ -> (String, Field_)
testMut f@(FieldValTy_ n v t) | t == "int" = ("MIN", FieldValTy_ n "-1" t)
testMut f = ("SKP", f)
                                           

getFldObjVal :: Field_ -> Value_
getFldObjVal (FieldObj_ _ v) = v

type MutationType = String
type Mutation = (MutationType, [Event_])

genAllMutants :: [Event_] -> [Mutation]
genAllMutants evs = getAllPrFieldMutations evs
                    ++
                    getAllArrFieldMutations evs
                    ++
                    genAllLEMutations evs

mopRemoveLE :: Int -> [Event_] -> Mutation
mopRemoveLE i evs = ("RLE", deleteNth i evs)

mopSwapEvents :: Int -> Int -> [Event_] -> Mutation
mopSwapEvents i j evs =
  let projEvent (AE (AppEvent_ t1 ev1 st1)) (AE (AppEvent_ _ ev2 _)) = (AE (AppEvent_ t1 ev2 st1))
  in  ("SEV", swapTwoInListWith projEvent evs (i,j))    
  
mopSwapStates :: Int -> Int -> [Event_] -> Mutation
mopSwapStates i j evs =
  let projState (AE (AppEvent_ t1 ev1 st1)) (AE (AppEvent_ _ _ st2)) = (AE (AppEvent_ t1 ev1 st2)) 
  in ("SST", swapTwoInListWith projState evs (i,j))

mopSwapLE :: Int -> Int -> [Event_] -> Mutation
mopSwapLE i j evs = ("SLE", swapTwoInList evs (i, j))

genAllLEMutations :: [Event_] -> [Mutation]
genAllLEMutations evs =
  [mopRemoveLE i evs
  | i <- [0 .. len]]
  ++ concat
  [[ mopSwapEvents i j evs
   , mopSwapStates i j evs
   , mopSwapLE i j evs]
  | i <- [0 .. len], j <- [0 .. len], i < j]
  where
    len = (length evs) - 1
    
mopIncInt :: Field_ -> (String, Field_)
mopIncInt fl@(FieldValTy_ nm vl "int") = ("INC", FieldValTy_ nm (show ((read vl :: Int) + 1)) "int")
mopIncInt f = ("SKP", f)
      
mopDecInt :: Field_ -> (String, Field_)
mopDecInt fl@(FieldValTy_ nm vl "int") = ("DEC", FieldValTy_ nm (show ((read vl :: Int) - 1)) "int")
mopDecInt f = ("SKP", f)

mopAbsInt :: Field_ -> (String, Field_)
mopAbsInt fl@(FieldValTy_ nm vl "int") = ("ABS", FieldValTy_ nm (show $ abs (read vl :: Int)) "int")
mopAbsInt f = ("SKP", f)

mopAsgZero :: Field_ -> (String, Field_)
mopAsgZero fl@(FieldValTy_ nm vl "int") = ("ZER", FieldValTy_ nm "0" "int")
mopAsgZero f = ("SKP", f)

mopMinus :: Field_ -> (String, Field_)
mopMinus fl@(FieldValTy_ nm vl "int") = ("MIN", FieldValTy_ nm (show $ negate (read vl :: Int)) "int")
mopMinus f = ("SKP", f)

mopEmptyStr :: Field_ -> (String, Field_)
mopEmptyStr fl@(FieldValTy_ nm vl "String") = ("EPS", FieldValTy_ nm "\"\"" "String")
mopEmptyStr f = ("SKP", f)

mopRevStr :: Field_ -> (String, Field_)
mopRevStr fl@(FieldValTy_ nm vl "String") = ("RVS", FieldValTy_ nm (reverse vl)  "String")
mopRevStr f = ("SKP", f)

mopNegBool :: Field_ -> (String, Field_)
mopNegBool fl@(FieldValTy_ nm vl "Boolean") = ("NBL", FieldValTy_ nm (show $ not (read vl :: Bool)) "Boolean") 
mopNegBool f = ("SKP", f)

getAllPrFieldMutations :: [Event_] -> [Mutation]
getAllPrFieldMutations evs = concatMap (flip genMutations evs)
                             [ mopIncInt
                             , mopDecInt
                             , mopAbsInt
                             , mopAsgZero
                             , mopMinus
                             , mopEmptyStr
                             , mopRevStr
                             -- , mopNegBool
                             ]

mopEmptyArr :: Field_ -> (String, Field_)
mopEmptyArr ar@(FieldObj_ fn (Obj_ "Array" elems)) = ("EAR", FieldObj_ fn (Obj_ "Array" [head elems]))
mopEmptyArr f = ("SKP", f)

mopRevArr :: Field_ -> (String, Field_)
mopRevArr ar@(FieldObj_ fn (Obj_ "Array" (id:elems))) = ("RAR", FieldObj_ fn (Obj_ "Array" (id:(reverse elems))))
mopRevArr f = ("SKP", f)

mopSwapElem :: Field_ -> (String, Field_)
mopSwapElem = undefined

mopDropOneArr :: Field_ -> (String, Field_)
mopDropOneArr ar@(FieldObj_ fn (Obj_ "Array" (id:elems)))
  | not $ null elems = ("DAR", FieldObj_ fn (Obj_ "Array" (id:(init elems))))
mopDropOneArr f = ("SKP", f)                       

getAllArrFieldMutations :: [Event_] -> [Mutation]
getAllArrFieldMutations evs = concatMap (flip genMutations evs)
                              [ mopEmptyArr
                              , mopRevArr
                              , mopDropOneArr]
                              -- mopSwapElem

-- | Primitive field mutation operators:
-- | - `int` type: incVal, decVal, absVal, asgnZero, minus
-- | - `string` type: emptyStr, reverse
-- | - `bool` type: negate
-- | Array field mutation operators: 
-- | - emptyArr, remArrElem, swapTwoArrElem
-- | Log-Entry mutation operators:
-- |  - swapTwoEvents, swapTwoStates
-- |  - removeLogEntry

-- [AE {unAppEvent = AppEvent_ {aeStamp = Just (-120,1379620599408), aeEvent = Obj_ {ocname = "eu.fittest.actionscript.automation::RecordEvent", ofields = [FieldValTy_ "I" "0" "ID",FieldValTy_ "targetID" "\"Image4\"" "String",FieldValTy_ "type" "\"click\"" "String",FieldObj_ "args" (Obj_ {ocname = "Array", ofields = [FieldValTy_ "I" "1" "ID"]})]}, aeSmodel = Obj_ {ocname = "AppAbstractState", ofields = [FieldValTy_ "I" "2" "ID",FieldValTy_ "selectedProduct" "-1" "int",FieldObj_ "catalogContents" (Obj_ {ocname = "Array", ofields = [FieldValTy_ "I" "3" "ID",FieldValTy_ "elem" "1" "int"]})]}}},AE {unAppEvent = AppEvent_ {aeStamp = Just (-120,1379620600201), aeEvent = Obj_ {ocname = "eu.fittest.actionscript.automation::RecordEvent", ofields = [FieldValTy_ "I" "0" "ID",FieldValTy_ "targetID" "\"Image4\"" "String",FieldValTy_ "type" "\"click\"" "String",FieldObj_ "args" (Obj_ {ocname = "Array", ofields = [FieldValTy_ "I" "1" "ID"]})]}, aeSmodel = Obj_ {ocname = "AppAbstractState", ofields = [FieldValTy_ "I" "2" "ID",FieldValTy_ "selectedProduct" "-1" "int",FieldObj_ "catalogContents" (Obj_ {ocname = "Array", ofields = [FieldValTy_ "I" "3" "ID",FieldValTy_ "elem" "2" "int"]})]}}}]
  
