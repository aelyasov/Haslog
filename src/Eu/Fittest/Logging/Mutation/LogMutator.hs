{- 

Author: Wishnu Prasetya

Copyright 2011 Utrecht University

The use of this sofware is free under the Modified BSD License.

-}

{- | 
   This module provides functions to mutate a FITTEST log. The mutations are 
   introduced randomly; but a fixed random-generator is used to that each
   run is deterministic (applying it to the same log will always yields
   the same mutants). 
-}

module Eu.Fittest.Logging.Mutation.LogMutator

where

import Data.Char
import System.Random
import Control.Monad.State.Lazy
import Control.Monad.Identity
import System.FilePath
-- import Control.Applicative

import Eu.Fittest.Logging.XML.XMLparser
import Eu.Fittest.Logging.XML.Event
import Eu.Fittest.Logging.XML.AppEvent
import Eu.Fittest.Logging.XML.LowEvent
import Eu.Fittest.Logging.XML.Value
import Eu.Fittest.Logging.XML.EventLog


import Debug.Trace

-- a pseudo random generator  ; deterministic
myRandomGen :: StdGen
myRandomGen = mkStdGen 3991 -- 2999

--
-- Representing a set of mutants, each is a value of type a. Internally,
-- it is a function that takes a random generator, and potentially uses it
-- to actually generate the mutant. The random generator is threaded in
-- a state monad.
--
type Mutants a = State StdGen [(MutationType,a)] -- same as: StateT StdGen Identity [a]

type MutationType = String

unspecifiedType :: MutationType
unspecifiedType = ""

appendMtype :: MutationType -> MutationType -> MutationType
appendMtype []  ty2 = ty2
appendMtype ty1 []  = ty1
appendMtype ty1 ty2 = ty1 ++ "_" ++ ty2 


-- to get the actual/concrete mutants
getMutants :: Mutants a -> [(String,a)]
getMutants ms = evalState ms myRandomGen

-- just an example just for testing:
{-
int1Mutant10 :: Mutants Int
int1Mutant10 = do {
      rndgen <- get ;
      (x,g') <- return (randomR (0,9) rndgen) ;
      put g' ;
      return [x]
  }
-}

-- ==================================================================
-- a set of mutants combinators
-- ==================================================================
  
  
-- union of two mutants    
(<+>) :: Mutants a -> Mutants a -> Mutants a
ms1 <+> ms2 = do {
    s1 <- ms1 ;
    s2 <- ms2 ;
    return (s1 ++ s2)
   }

allMutants mutants = foldr (<+>) (return []) mutants   
  
-- try the first mutants, if empty use the second   
orelse :: Mutants a -> Mutants a -> Mutants a
ms1 `orelse` ms2 = do {
    s1 <- ms1 ;
    if null s1 then ms2 else return s1
   }   
   
firstNonEmptyMutants mutants = foldr orelse (return []) mutants   

-- randomly select one or the other mutants
(<|>) :: Mutants a -> Mutants a -> Mutants a
ms1 <|> ms2 = do {
      rndg <- get ;
      (choice,rndg') <- return (randomR (0,1) rndg) ;
      put rndg' ;
      if choice==(0::Int) then ms1 else ms2
   }

(<*>) :: Mutants (a -> b) -> Mutants a -> Mutants b
m1 <*> m2 = do mv1 <- return $ getMutants m1
               rndg <- get
               mv2 <- return $ evalState m2 rndg
               return [(t2, v1 v2)| (t1,v1) <- mv1, (t2,v2) <- mv2]

choose [] = return []
choose (ms:rest) = foldr (<|>) (return []) (ms:rest)  `orelse` ms   
   
-- transform the mutants
(<$>) :: ((MutationType,a)->(MutationType,b)) -> Mutants a -> Mutants b
f <$> ms = do { s <- ms ; return (map f s) }

-- transform the mutants; the mutant-types are left unchanged
($>) :: (a->b) -> Mutants a -> Mutants b
f $> ms = (\(mty,m) -> (mty,f m)) <$> ms

-- re-types the mutants
retype :: (MutationType->MutationType) -> Mutants a -> Mutants a
f `retype` ms = (\(mty,m) -> (f mty,m)) <$> ms

-- ==================================================================
-- Mutator, and a set of mutator combinators
-- ==================================================================

type Mutator a = a -> Mutants a

failMutator :: Mutator a
failMutator x = return []

skipMutator :: Mutator a
skipMutator x = return [(unspecifiedType,x)]


-- Apply a mutator to all elements of a vector. If it fails on an element,
-- the element is not mutated. If the mutator produces multiple value, we
-- construct the cross product of all combinations. (be careful, may explode)
--
vmutateAll :: Mutator a -> Mutator [a]
vmutateAll ms vector = worker vector
   where
   worker [] = skipMutator []
   worker (x:s) = do { xs <- ms x `orelse` skipMutator x ;
                       z  <- worker s ;
                       return [ (ty1 `appendMtype` ty2, y':t) | (ty1,y')<-xs, (ty2,t)<- z ] 
                     }
 
-- Apply a mutator to a random element of a vector. We only select an element
-- where the mutator would succeed. If the mutator cannot succeed on any element,
-- the whole mutator fails.
vmutateOne :: Mutator a -> Mutator [a]
vmutateOne ms [] = skipMutator []
vmutateOne ms vector = 
   let
   ms' x k = (\x'->(x',k)) $> ms x   
   in
   do {
      z <- sequence [ms' x k | (x,k) <- zip vector [0..]] ;
      successes <- return (filter (not . null) z) ;
      if null successes 
         then return []
         else do {
            selected <- oneOf successes ;
            return [ (ty,update vector k x') | (ty,(x',k)) <- selected ]
         }
      
   }

-- list update helper:
update []    k x = []
update (y:s) k x 
   | k<=0      = (x:s)
   | otherwise =  y : update s (k-1) x 
   

-- ==================================================================
-- primitive mutators, on values
-- ==================================================================

oneOf :: [a] -> State StdGen a
oneOf candidates = do { rndg <- get ;
                        (k,rndg') <- return (randomR (0,(length candidates)-1) rndg) ;
                        put rndg' ;                      
                        return (candidates !! k) }

                        
mutateBool :: Mutator String
mutateBool s = let
               b :: Bool
               b = read s                
               in
               show $> skipMutator (not b)
 
mutateInt :: Mutator String
mutateInt s = let
              i :: Integer
              i = read s
              candidates = case i of
                   0  -> [-1,1]
                   -1 -> [0,1]
                   _  -> [0,-1]                   
              in
              show $>
              do { k <- oneOf candidates ;
                   skipMutator k }


mutateNumber :: Mutator String
mutateNumber s = let
              n :: Double
              n = read s
              candidates 
                 | n == 0.0   = [-1.0, 0.001]      
                 | n == -1.0  = [0.0, 0.001]
                 | otherwise  = [-1.0, 0.0]                 
              in
              show $>
              do { k <- oneOf candidates ;
                   skipMutator k }
                                
mutateString :: Mutator String
mutateString s = let
              z :: String
              z = read s
              candidates = case z of
                 ""   -> ["0","x0x"]
                 "0"  -> ["x0x", ""]
                 _    -> ["","0"]
                 
              in
              show $>
              do { k <- oneOf candidates ;
                   skipMutator k }                   


mutateValue__ :: String -> Mutator String
mutateValue__ ty s =
     let
     ty' = map toLower ty
     val' | ty' == "int"    = mutateInt s
          | ty' == "string" = mutateString s
          | ty' `elem` ["bool","boolean"] = mutateBool s
          | ty' `elem` ["float","double","number"] = mutateNumber s
          | otherwise = return []
    in
    val'             
                   
-- ==================================================================
-- Object/Value mutator. 
-- ==================================================================
                                              
-- Implements a random mutator of a value. In case the value is an object,
-- the mutator will randomly select one of the fields to mutate. Null and
-- undefined are currently not mutated.
--           
mutateValue :: Mutator Value_ 
mutateValue v@(SingleVal_ { vVal=val, vTy=ty }) 
    =
    if (isNull v || isUndefined v) 
       then return []
       else (\val' -> SingleVal_ { vVal=val', vTy=ty }) $> mutateValue__ ty val
       
mutateValue o@(Obj_ { ocname=cname, ofields=fields }) 
   =   
   (\fields'-> Obj_ { ocname=cname, ofields = fields' })
   $>
   vmutateOne mutateField fields
   
  
-- check if a field is mutable. xid is not mutable. And for now, these 
-- are also not mutable: xref field, null, undefined.
--
isMutableField :: Field_ -> Bool
isMutableField (FieldValTy_  "I" _ "ID") = False
isMutableField (FieldXref_ _ _)          = False
isMutableField (FieldObj_ _ obj)         = not (isNull obj || isUndefined obj)
isMutableField  _  = True


-- mutate a field, if it is mutable. Else fails.
mutateField :: Mutator Field_
mutateField f = if isMutableField f then worker f else return []
  where
  worker (FieldValTy_ name val ty) = (\val'-> FieldValTy_ name val' ty) $> mutateValue__ ty val
  worker (FieldObj_ name obj)      = (\obj'-> FieldObj_ name obj')      $> mutateValue obj
  

-- ==================================================================
-- App-event mutator. Only mutates the state.
-- ==================================================================

-- Randomly mutate the state after a high-level event:
appEventMutator :: Mutator AppEvent_
appEventMutator (AppEvent_  timestamp eventInfo state) 
    =
    const "AEpoststateMut" 
    `retype`
    ((\state'-> AppEvent_ timestamp eventInfo state') $> mutateValue state) 

    
-- ==================================================================
-- Low-event mutator. Currently only mutate FE and FX events.
-- ==================================================================

lowEventMutator :: Mutator LowEvent_
lowEventMutator (FE_ timestamp funcName className targetObj args) = 
   const "FEobjMut"
   `retype`
   ((\objs'-> FE_ timestamp funcName className (head objs') (tail objs'))
      $>
      vmutateOne mutateValue (targetObj : args)) 
lowEventMutator (FX_ timestamp funcName className targetObj retObj) = 
   const "FXobjMut"
   `retype`
   ((\[o',r']-> FX_ timestamp funcName className o' r')
      $>
      vmutateOne mutateValue [targetObj, retObj]) 
   
   
-- mutate an event
eventMutator :: Mutator Event_
eventMutator (AE e) = AE $> appEventMutator e
eventMutator (LE e) = LE $> lowEventMutator e
   
-- ==================================================================
-- App-event-pairs mutators. 
-- ==================================================================
   
-- rotate the events in an event pair:
swapEvent :: Mutator [Event_]
swapEvent [AE (AppEvent_  t1 e1 s1), AE (AppEvent_  t2 e2 s2)] 
   =
   const "SwapAppEvent2Mut"
   `retype`
   skipMutator [AE (AppEvent_  t1 e2 s1), AE (AppEvent_  t2 e1 s2)]
   
   
-- either swap the events in the pair, or mutate the state of the first event, or fail    
pairMutator :: Mutator [Event_]
pairMutator p@[e1,e2]
   =
  -- swapEvent p `orelse` ((:[e2]) $> eventMutator e1) `orelse` failMutator p
  swapEvent p <|> ((:[e2]) $> eventMutator e1) <|> failMutator p
 
logMutator :: Mutator [Event_] -> Mutator [Event_]  
logMutator pairMutator log = do {
     mutants <- sequence (map mutator (trace ("<<< segments: " ++ (show segments)) segments)) ;
     return . concat . filter (not . null) $ trace ("<<< mutants: " ++ (show mutants)) mutants
   }
   where
   log'  = tail log
   log'' = tail (tail log)
   segments = zip3 log log' log''
   mutator (a,b,c) = (a:) $> pairMutator [b,c]


deleteLogEntryMutator :: Mutator [Int]
deleteLogEntryMutator lentrs =
  do rndg      <- get 
     let (k, rndg') = randomR (0, (length lentrs) - 1) rndg
         (lbefore, lafter) = splitAt k lentrs
     put rndg'                       
     skipMutator (lbefore ++ tail lafter)

deleteNLogEntryMutator :: Int -> Mutator [Int]
deleteNLogEntryMutator 0 lentrs = skipMutator lentrs
deleteNLogEntryMutator i lentrs = 
  do rndg <- get
     let (k, rndg') = randomR (0, (length lentrs) - 1) rndg
         (lbefore, lafter) = splitAt k lentrs
     put rndg'                      
     deleteNLogEntryMutator (i-1) (lbefore ++ tail lafter)  

-- ==================================================================
-- Parse a FITTEST XML log, and generate mutations
-- ==================================================================

generateMutations :: Mutator [Event_] -> Int -> String -> IO()
generateMutations logMutator k fileName = do {
    contents <- parseXMLlog fileName ;
    mutants <-  return . take k . zip [0..] . getMutants . logMutator $ trace (show contents) contents ;
    (baseName,ext) <- return . splitExtension $ fileName ;
    sequence_ [ saveIt i ty (ppXMLEventLog z) | (i,(ty,z)) <- trace (show mutants) mutants ]
  }
  where
  (basename,ext) = splitExtension fileName 
  saveIt k ty segment = Prelude.writeFile (basename ++ "_M" ++ show k ++ "_" ++ ty ++ ext) segment
    
--
-- As an example, try: generateMutations (logMutator pairMutator) 5 somelog.xml
--

      
test1 = getMutants $
        do [(_,t)] <- deleteLogEntryMutator [1,2,3,4]
           t' <- deleteLogEntryMutator t
           trace (show t') $ return t'