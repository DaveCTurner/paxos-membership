module Main where

import Lib
import System.IO
import Control.Monad.Writer
import Text.Printf
import System.Process
import Data.List

xLeader, x1, x2 :: Int
x1      = 1000
xLeader = 1500
x2      = 2000

tellCoords :: Int -> Int -> Int -> Int -> Writer String ()
tellCoords x1 y1 x2 y2 = tell $ printf "\t %d %d %d %d\n" x1 y1 x2 y2

tellTimeline :: Int -> Int -> String -> Writer String ()
tellTimeline n x label = do
  tell "2 1 0 1 0 7 50 -1 -1 0.000 0 0 -1 0 0 2\n"
  tellCoords x y x (y + timelineLen)
  tell "2 1 0 1 0 7 50 -1 -1 0.000 0 0 -1 0 0 2\n"
  tellCoords (x - halfHeaderWidth) y (x + halfHeaderWidth) y
  tell $ printf "4 1 0 50 -1 0 9 0.0000 2 135 540 %d %d %s\\001\n"
    x (y-80) label

  where
  halfHeaderWidth = 200
  y = timelineStart n

tellRPC :: Int -> Int -> Int -> (Int -> Writer String ()) -> Writer String Int
tellRPC xHandler yStart halfRTT tellLabel = do
  tell "2 1 0 1 0 7 50 -1 -1 0.000 0 0 7 1 0 2\n"
  tell "\t1 1 1.00 60.00 60.00\n"
  tellCoords xLeader yStart xHandler (yStart + halfRTT)
  tellLabel (yStart + halfRTT)
  tell "2 1 0 1 0 7 50 -1 -1 0.000 0 0 7 1 0 2\n"
  tell "\t1 1 1.00 60.00 60.00\n"
  tellCoords xHandler (yStart + halfRTT + procTime)
             xLeader  (yStart + 2 * halfRTT + procTime)
  return $ yStart + 2 * halfRTT + 2 * procTime

timelineSpacing :: Int
timelineSpacing = 500

timelineLen :: Int
timelineLen = 5300

timelineStart n = (timelineLen + timelineSpacing) * n

labelOffset :: Int
labelOffset = 60

procTime :: Int
procTime = 50

propSpacing :: Int
propSpacing = 230

tellPrepare :: Int -> String -> Writer String Int
tellPrepare = tellPrepare' 0

tellPrepare' :: Int -> Int -> String -> Writer String Int
tellPrepare' extraLabelOffset yStart ballot = tellRPC x1 yStart 570 $ \labelY -> tell $ printf
  "4 2 0 50 -1 0 9 0.0000 2 180 1890 950 %d $\\\\mathbf{prepare}(%s)$\\001\n"
  (labelY + labelOffset + extraLabelOffset) ballot

tellPropose :: Int -> String -> String -> Writer String Int
tellPropose yStart inst ballot = tellRPC x2 yStart 350 $ \labelY -> tell $ printf
  "4 0 0 50 -1 0 9 0.0000 2 180 2160 2050 %d $\\\\mathbf{proposed}_{%s}(%s)$\\001\n"
  (labelY + labelOffset) inst ballot

tellNewEra :: Int -> Writer String ()
tellNewEra y = do
  tell $ printf "2 1 1 1 0 7 50 -1 -1 4.000 0 0 -1 0 0 2\n"
  tellCoords (x1 - 500) y' (x2 + 500) y'

  tell $ printf "4 2 0 50 -1 0 9 0.0000 2 180 1890 935 %d era $e$\\001\n" (y' - 80)
  tell $ printf "4 2 0 50 -1 0 9 0.0000 2 180 1890 935 %d era $e+1$\\001\n" (y' + 160)

  where y' = y - div procTime 2

main :: IO ()
main = forM_
    [ ("stoppable.fig",  tellStoppable)
    , ("stoppable2.fig", tellStoppable2)
    , ("smooth.fig",     tellSmooth)
    , ("dynamic.fig",    tellDynamic)
    ] $ \(fileName, tellSequenceDiagram) -> do

  writeFile fileName $ execWriter $ do
    tell $ unlines
      [ "#FIG 3.2  Produced by xfig version 3.2.5c"
      , "Landscape"
      , "Center"
      , "Metric"
      , "A4      "
      , "100.00"
      , "Single"
      , "-2"
      , "1200 2"
      ]

    let timelines = [(xLeader, "$\\\\ell$"), (x1, "$a_1$"), (x2, "$a_2$")]
    forM_ timelines $ uncurry $ tellTimeline 0
    tellSequenceDiagram 0

  callCommand ("fig2eps --nogv " ++ fileName)
  callCommand ("fig2pdf --nogv " ++ fileName)

tellSmooth firstPrepareStartTime = do
  firstPrepareFinishTime <- tellPrepare firstPrepareStartTime "b"

  finishTimes <- forM [0..3] $ \n -> tellPropose (firstPrepareFinishTime + propSpacing * n)
    (showIPlus n) "b"

  let secondPrepareStartTime = last finishTimes
  secondPrepareFinishTime <- tellPrepare secondPrepareStartTime "b'"

  tellNewEra $ last finishTimes

  forM_ [4..13] $ \n -> let
    proposeStartTime = firstPrepareFinishTime + propSpacing * n
    in tellPropose proposeStartTime
          (printf "i+%d" n)
          (if proposeStartTime >= secondPrepareFinishTime then "b'" else "b")

tellStoppable firstPrepareStartTime = do
  firstPrepareFinishTime <- tellPrepare firstPrepareStartTime  "b"

  finishTimes <- forM [0..3] $ \n -> tellPropose (firstPrepareFinishTime + propSpacing * n)
    (showIPlus n) "b"

  tellNewEra $ last finishTimes

  let secondPrepareStartTime = last finishTimes
  secondPrepareFinishTime <- tellPrepare secondPrepareStartTime "b'"

  forM_ [4..6] $ \n -> tellPropose (secondPrepareFinishTime + propSpacing * (n - 4))
    (showIPlus n) "b'"

showIPlus :: Int -> String
showIPlus 0 = "i"
showIPlus n = printf "i+%d" n

tellStoppable2 firstPrepareStartTime = do
  firstPrepareFinishTime <- tellPrepare firstPrepareStartTime "b"

  let startIndex n
          | n == 1    = 2
          | n == 2    = 3
          | n == 3    = 1
          | otherwise = n

  finishTimes <- forM [0..3] $ \n -> tellPropose
    (firstPrepareFinishTime + propSpacing * startIndex n)
    (showIPlus n) "b"

  tellNewEra $ maximum finishTimes

  let secondPrepareStartTime = last finishTimes
  secondPrepareFinishTime <- tellPrepare' 220 secondPrepareStartTime "b'"

  forM_ [4..6] $ \n -> tellPropose (secondPrepareFinishTime + propSpacing * (n - 4))
    (showIPlus n) "b'"

tellDynamic firstPrepareStartTime = do
  firstPrepareFinishTime <- tellPrepare firstPrepareStartTime "b"

  finishTimeses <- forM [0,1] $ \n0 -> let
    go n y
      | n < 6 = do
          finishTime <- tellPropose y (showIPlus n) "b"
          (:) finishTime <$> go (n+2) finishTime
      | otherwise = return []
    in go n0 (firstPrepareFinishTime + propSpacing * n0)

  let finishTimes = sort $ concat finishTimeses

  secondPrepareFinishTime <- tellPrepare' (-200) (finishTimes !! 3) "b'"
  tellNewEra $ finishTimes !! 5
  tellPropose  secondPrepareFinishTime                (showIPlus 6) "b'"
  tellPropose (secondPrepareFinishTime + propSpacing) (showIPlus 7) "b'"
  return ()

