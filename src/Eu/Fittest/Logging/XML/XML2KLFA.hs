{- 

Author: Alexander Elyasov

Copyright 2014 Utrecht University

The use of this sofware is free under the Modified BSD License.

-}

{- | 

   This module provides a function to convert a FITTEST XML log file, 
   to KLFA log (.csv).
   
-}

module Eu.Fittest.Logging.XML.XML2KLFA(
         xml2klfa
     )
    
where
    
import Eu.Fittest.Logging.XML.XMLparser
import Eu.Fittest.Logging.XML.ToFITTESTRawLog
import Eu.Fittest.Logging.XML.AppEvent
import Eu.Fittest.Logging.XML.Event
import Eu.Fittest.Logging.XML.Value
-- import qualified Data.ByteString.Lazy as B
import System.FilePath
import Data.List

import Debug.Trace

xml2klfa :: FilePath -> FilePath -> IO ()
xml2klfa filename1 filename2 = do
  events <- parseXMLlog filename1
  let klfalog        = events2klfa events
      klfastr        = unlines $ map (\(e, args) -> concat $ intersperse "," ("0":e:args)) klfalog
      (baseName,ext) = splitExtension filename1 
      klfaFileName   = if null filename2
                       then baseName ++ ".csv"
                       else filename2
  writeFile klfaFileName klfastr

type EName = String

type EArg = String

events2klfa :: [Event_] -> [(EName, [EArg])]
events2klfa = map convAppEvent . map unAppEvent where
    convAppEvent (AppEvent_ _ (Obj_ _ event') _) = convEvent event'

    convEvent evt = (convEvtName evt, convEvtArgs evt)

    convEvtName (_:(FieldValTy_ _ etarget _):(FieldValTy_ _ etype _):_) = (read etype :: String) ++ (read etarget :: String)

    convEvtArgs (_:_:_:(FieldObj_ _ (Obj_ _ (_:eargs))):[]) = map convEvtArg eargs

    convEvtArg (FieldValTy_ _ earg _) = earg
    convEvtArg _                      = error "the convertion for event types is not defined"  
  
-- example
exLog = xml2klfa "test_eps" "test_eps.csv" 
