{- 

Author: Alexander Elyasov

Copyright 2014 Utrecht University

The use of this sofware is free under the Modified BSD License.

-}

{- | 

   This module provides a function to convert a FITTEST XML log file, 
   to Synoptic log (.csv).
   
-}

module Eu.Fittest.Logging.XML.XML2Synoptic(
         xml2synoptic
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

xml2synoptic :: FilePath -> FilePath -> IO ()
xml2synoptic filename1 filename2 = do
  events <- parseXMLlog filename1
  let synlog         = events2synoptic events
      synstr         = unlines  synlog
      (baseName,ext) = splitExtension filename1 
      synFileName    = if null filename2
                       then baseName ++ ".syn"
                       else filename2
  writeFile synFileName synstr

type EName = String


events2synoptic :: [Event_] -> [EName]
events2synoptic = map convAppEvent . map unAppEvent where
    convAppEvent (AppEvent_ _ (Obj_ _ event') _) = convEvent event'

    convEvent evt = convEvtName evt

    convEvtName (_:(FieldValTy_ _ etarget _):(FieldValTy_ _ etype _):_) = (read etype :: String) ++ (read etarget :: String)
  
-- example
exLog = xml2synoptic "test_eps" "test_eps.csv"
