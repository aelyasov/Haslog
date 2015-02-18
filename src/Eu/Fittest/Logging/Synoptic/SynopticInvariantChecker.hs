{- 

Author: Alexander Elyasov

Copyright 2014 Utrecht University

The use of this sofware is free under the Modified BSD License.

-}

{- | 

   This module provides a function to check Synoptic temporal invariaints
   against new logs
   
-}

module Eu.Fittest.Logging.Synoptic.SynopticInvariantChecker(
         checkSynopticInvs
     )
    
where


checkSynopticInvs :: FilePath -> FilePath -> IO ()
checkSynopticInvs invFile logFile = do
  invars <- readFile invFile >>= return . parseInvs
  logEvs <- readFile logFile >>= return . parseLog
  mapM_ (\inv -> if checkTProp inv logEvs
                 then return ()
                 else print $ "Invariant Violation (" ++ show inv ++ ") on input file " ++ logFile 
                     ) invars
    where
      parseLog = lines
      parseInvs = map str2tprop . map words . lines
      str2tprop [x,"AlwaysFollowedBy(t)",y] = x :->: y
      str2tprop [x,"AlwaysPrecedes(t)",y]   = x :<-: y
      str2tprop [x,"NeverFollowedBy(t)",y]  = x :/->: y


data TProp a = a :->: a  -- always followed by
             | a :<-: a  -- always precedes
             | a :/->: a -- never followed by
               deriving Show

checkFollowedBy :: TProp String -> [String] -> Bool
checkFollowedBy ("INITIAL" :->: b) as = b `elem` as
checkFollowedBy (a :->: b) [] = True
checkFollowedBy p@(a :->: b) as = let (xs, ys) = span (/=a) as
                                  in  if (null ys)
                                      then True
                                      else (b `elem` (tail ys)) && checkFollowedBy p (tail ys)

checkPrecedes :: TProp String -> [String] -> Bool
checkPrecedes (a :<-: b) as = checkFollowedBy (b :->: a) $ reverse as

checkNeverFollowedBy :: TProp String -> [String] -> Bool
checkNeverFollowedBy (a :/->: b) [] = True
checkNeverFollowedBy p@(a :/->: b) as = let (xs, ys) = span (/=a) as
                                       in  if (null ys)
                                           then True
                                           else (b `notElem` (tail ys)) && checkNeverFollowedBy p (tail ys)

checkTProp :: TProp String -> [String] -> Bool
checkTProp p = case p of
 (a :->: b)  -> checkFollowedBy p 
 (a :<-: b)  -> checkPrecedes p
 (a :/->: b) -> checkNeverFollowedBy p
