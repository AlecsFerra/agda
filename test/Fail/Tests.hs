
module Fail.Tests where

import qualified Data.ByteString as BS
import Data.Monoid ((<>))
import qualified Data.Text as T
import Data.Text.Encoding

import System.Directory
import System.Exit
import System.FilePath
import System.IO.Temp

import Test.Tasty
import Test.Tasty.Silver
import Test.Tasty.Silver.Advanced
  (readFileMaybe, goldenTest1, goldenTestIO1, GDiff (..), GShow (..))

import Utils

import Agda.Utils.Functor ((<&>), for)
import Test.Tasty.Silver.Filter (RegexFilter (RFInclude))

testDir :: FilePath
testDir = "test" </> "Fail"

tests :: IO TestTree
tests = do
  inpFiles <- getAgdaFilesInDir NonRec testDir
  return $ testGroup "Fail" $ concat $
    -- A list written with ':' to quickly switch lines
    [ mkFailTest issue7678Dir (issue7678Dir </> "Issue7678.agda") ] :
    map (mkFailTest testDir) inpFiles :
    -- Some of the customized tests fail with agda-quicker
    -- (because they refer to the name of the Agda executable),
    -- so put them last.
    customizedTests :
    []
  where
  issue7678Dir = testDir </> "Issue7678"
  customizedTests =
    [ testGroup "customised" $
        issue7953 :
        issue6465 :
        issue5508 :
        issue4671 :
        issue2649 :
        nestedProjectRoots :
        []
    ]

data TestResult
  = TestResult T.Text -- the cleaned stdout
  | TestUnexpectedSuccess ProgramResult

mkFailTest ::
     FilePath -- ^ Directory
  -> FilePath -- ^ Input file (Agda file).
  -> TestTree
mkFailTest testDir agdaFile =
  goldenTestIO1
    testName
    readGolden
    (printTestResult <$> doRun)
    (textDiffWithTouch agdaFile)
    (pure . ShowText)
    (Just updGolden)
  where
  testName   = asTestName testDir agdaFile
  baseName   = dropAgdaExtension agdaFile
  varFile    = baseName <.> "vars"
  flagFile   = baseName <.> "flags"
  goldenFile = baseName <.> "err"

  readGolden = readTextFileMaybe goldenFile
  updGolden  = writeTextFile goldenFile

  doRun = do
    let agdaArgs = [ "-v0", "-vwarning:1", "-i" ++ testDir, "-itest/", agdaFile
                   , "--ignore-interfaces", "--no-libraries"
                   , "--double-check"
                   ]
    runAgdaWithOptions testName agdaArgs (Just flagFile) (Just varFile)
      <&> expectFail

-- | A test for case-insensitivity of the file system.
caseInsensitiveFileSystem :: IO Bool
caseInsensitiveFileSystem = fst <$> caseInsensitiveFileSystem4671

-- | A test for case-insensitivity of the file system, using data of test 4671.
caseInsensitiveFileSystem4671 :: IO (Bool, FilePath)
caseInsensitiveFileSystem4671 = do
  b <- doesFileExist goldenFileInsens'
  return (b, if b then goldenFileInsens else goldenFileSens)
  where
    dir = testDir </> "customised"
    goldenFileSens    = dir </> "Issue4671.err.case-sensitive"
    goldenFileInsens  = dir </> "Issue4671.err.case-insensitive"
    goldenFileInsens' = dir </> "Issue4671.err.cAsE-inSensitive" -- case variant, to test file system


-- | Filtering out fail-tests that require Agda built with -fdebug.

fdebugTestFilter :: [RegexFilter]
fdebugTestFilter =
-- This list was crafted using
--    grep -RP '(?<!-- ){-# OPTIONS.* -v' | grep Fail/
--  and screening the results (e.g. for comments)
  [ disable "Fail/Issue3590-2"
  , disable "Fail/IndexInference"
  , disable "Fail/DebugWith"
  , disable "Fail/ImpossibleVerbose"
  , disable "Fail/ConstructorHeadedPointlessForRecordPatterns"
  , disable "Fail/Issue3590-1"
  , disable "Fail/Issue1303"
  , disable "Fail/ImpossibleVerboseReduceM"
  , disable "Fail/Issue2018debug"
  , disable "Fail/Issue1963DisplayWithPostfixCopattern"
  , disable "Fail/Optimised-open"
  , disable "Fail/Optimised-open"
  , disable "Fail/Issue4175"
  ]
  where disable = RFInclude

-- | We need to load an agda file in a subdirectory to trigger issue #7953.
issue7953 :: TestTree
issue7953 =
  goldenTest1
    name
    (readTextFileMaybe goldenFile)
    doRun
    textDiff
    ShowText
    (writeTextFile goldenFile)
  where
    name       = "Issue7953"
    dir        = testDir </> "customised"
    goldenFile = dir </> name <.> "err"
    doRun = do
      runAgdaWithOptions name agdaArgs Nothing Nothing
        <&> printTestResult . expectFail
      where
        agdaArgs =
          [ "-v0"
          , "--no-default-libraries"
          , "-i" ++ dir
          -- , "-i" ++ dir </> name
          , dir </> name </> "Test.agda"
          ]

issue6465 :: TestTree
issue6465 =
  goldenTest1
    name
    (readTextFileMaybe goldenFile)
    doRun
    textDiff
    ShowText
    (writeTextFile goldenFile)
  where
    name       = "Issue6465"
    dir        = testDir </> "customised"
    goldenFile = dir </> name <.> "err"
    doRun = do
      let agdaArgs file =
            [ "-v0"
            , "--no-default-libraries"
            , "-i" ++ dir
            , "-i" ++ dir </> name
            , dir </> file
            ]
      runAgdaWithOptions
        name (agdaArgs (name <.> "agda")) Nothing Nothing
        <&> printTestResult . expectFail

issue4671 :: TestTree
issue4671 =
  goldenTest1
    "Issue4671"
    (readTextFileMaybe =<< goldenFile)
    doRun
    textDiff
    ShowText
    (\ res -> goldenFile >>= (`writeTextFile` res))
  where
    dir = testDir </> "customised"
    goldenFile = snd <$> caseInsensitiveFileSystem4671
      -- Query case-variant to detect case-sensitivity of the FS.
      -- Note: since we expect the .err file to exists, we cannot
      -- use this test to interactively create a non-existing golden value.

    doRun = do
      let agdaArgs file = [ "-v0", "--no-libraries", "-i" ++ dir, dir </> file ]
      runAgdaWithOptions "Issue4671" (agdaArgs "Issue4671.agda") Nothing Nothing
        <&> printTestResult . expectFail

issue5508 :: TestTree
issue5508 =
  goldenTest1
    "iSSue5508"
    (readTextFileMaybe =<< goldenFile)
    doRun
    textDiff
    ShowText
    (\ res -> goldenFile >>= (`writeTextFile` res))
  where
    dir = testDir </> "customised"
    goldenFile = caseInsensitiveFileSystem <&> (dir </>) . \case
      True  -> "iSSue5508.err.case-insensitive"
      False -> "iSSue5508.err.case-sensitive"
      -- Query case-variant to detect case-sensitivity of the FS.
      -- Note: since we expect the .err file to exists, we cannot
      -- use this test to interactively *create* a non-existing golden value.
      -- However, it can be updated...

    doRun = do
      let agdaArgs file = [ "-v0", "--no-libraries", "-i" ++ dir, dir </> file ]
      runAgdaWithOptions "iSSue5508" (agdaArgs "iSSue5508.agda") Nothing Nothing
        <&> printTestResult . expectFail

issue2649 :: TestTree
issue2649 =
  goldenTest1
    "Issue2649"
    (readTextFileMaybe goldenFile)
    doRun
    textDiff
    ShowText
    (writeTextFile goldenFile)
  where
    dir = testDir </> "customised"
    goldenFile = dir </> "Issue2649.err"
    doRun = do
      let agdaArgs file = ["--no-libraries", "-i" ++ dir, dir </> file ]
      _  <- runAgdaWithOptions "Issue2649-1" (agdaArgs "Issue2649-1.agda") Nothing Nothing
      _  <- runAgdaWithOptions "Issue2649-2" (agdaArgs "Issue2649-2.agda") Nothing Nothing
      runAgdaWithOptions "Issue2649"   (agdaArgs "Issue2649.agda")   Nothing Nothing
        <&> printTestResult . expectFail

nestedProjectRoots :: TestTree
nestedProjectRoots =
  goldenTest1
    "NestedProjectRoots"
    (readTextFileMaybe goldenFile)
    doRun
    textDiff
    ShowText
    (writeTextFile goldenFile)
  where
    dir = testDir </> "customised"
    goldenFile = dir </> "NestedProjectRoots.err"
    doRun = do
      let agdaArgs file = ["--no-libraries", "-i" ++ dir </> "Imports", dir </> file]
      let run extra = do
            runAgdaWithOptions "NestedProjectRoots"
              (extra ++ [ "-i" ++ dir ] ++ agdaArgs "NestedProjectRoots.agda")
              Nothing Nothing
              <&> printTestResult . expectFail
      -- Run without interfaces; should fail.
      r1 <- run [ "--ignore-interfaces" ]
      -- Create interface file
      r2 <- runAgdaWithOptions "Imports.A"
              ("-v 0" : agdaArgs ("Imports" </> "A.agda")) Nothing Nothing
              <&> expectOk
      -- Run again with interface; should still fail.
      r3 <- run []
      return $ r1 `T.append` r2 `T.append` r3

expectOk :: (ProgramResult, AgdaResult) -> T.Text
expectOk (res, ret) = case ret of
  AgdaSuccess{} -> stdOut res
  AgdaFailure{} -> "AGDA_UNEXPECTED_FAILURE\n\n" <> printProgramResult res

expectFail :: (ProgramResult, AgdaResult) -> TestResult
expectFail (res, ret) = case ret of
  AgdaSuccess{} -> TestUnexpectedSuccess res
  -- If it's a type error, we do not print the exit code
  AgdaFailure _ (Just TCMError) -> TestResult $ stdOut res
  -- Otherwise, we print all the output
  AgdaFailure{}                 -> TestResult $ printProgramResult res


printTestResult :: TestResult -> T.Text
printTestResult = \case
  TestResult t            -> t
  TestUnexpectedSuccess p -> "AGDA_UNEXPECTED_SUCCESS\n\n" <> printProgramResult p
