{-# LANGUAGE PatternGuards #-}
-- |
-- Module      : Scion.Types.Notes
-- Copyright   : (c) Thomas Schilling 2009
-- License     : BSD-style
--
-- Maintainer  : nominolo@googlemail.com
-- Stability   : experimental
-- Portability : portable
--
-- Notes, i.e., warnings, errors, etc.
--
module Scion.Types.Notes
  ( Location, LocSource(..), mkLocation, mkNoLoc
  , locSource, isValidLoc, noLocText, viewLoc
  , locStartCol, locEndCol, locStartLine, locEndLine
  , AbsFilePath(toFilePath), mkAbsFilePath
  , Note(..), NoteKind(..), Notes
  , ghcSpanToLocation, ghcErrMsgToNote, ghcWarnMsgToNote
  , ghcMessagesToNotes, trimFile
  )
where

import qualified ErrUtils as GHC ( ErrMsg(..), WarnMsg, Messages )
import qualified SrcLoc as GHC
import qualified FastString as GHC ( unpackFS )
import qualified Outputable as GHC ( showSDoc, ppr, showSDocForUser )
import qualified Bag ( bagToList )

import qualified Data.MultiSet as MS
import System.FilePath

infixr 9 `thenCmp`

-- * Notes

-- | A note from the compiler or some other tool.
data Note
  = Note { noteKind :: NoteKind
         , noteLoc :: Location
         , noteMessage :: String
         } deriving (Eq, Ord, Show)

-- | Classifies the kind (or severity) of a note.
data NoteKind
  = ErrorNote
  | WarningNote
  | InfoNote
  | OtherNote
  deriving (Eq, Ord, Show)

type Notes = MS.MultiSet Note

-- * Absolute File Paths

-- | Represents a 'FilePath' which we know is absolute.
--
-- Since relative 'FilePath's depend on the a current working directory we
-- normalise all paths to absolute paths.  Use 'mkAbsFilePath' to create
-- absolute file paths.
newtype AbsFilePath = AFP { toFilePath :: FilePath } deriving (Eq, Ord)
instance Show AbsFilePath where show (AFP s) = show s

-- | Create an absolute file path given a base directory.
--
-- Throws an error if the first argument is not an absolute path.
mkAbsFilePath :: FilePath -- ^ base directory (must be absolute)
              -> FilePath -- ^ absolute or relative 
              -> AbsFilePath
mkAbsFilePath baseDir dir
  | isAbsolute baseDir = AFP $ normalise $ baseDir </> dir
  | otherwise =
      error "mkAbsFilePath: first argument must be an absolute path"

-- * Scion's 'Location' data type

-- | Scion's type for source code locations (regions).
--
-- We use a custom location type for two reasons:
--
--  1. We enforce the invariant, that the file path of the location is an
--     absolute path.
--
--  2. Independent evolution from the GHC API.
--
-- To save space, the 'Location' type is kept abstract and uses special
-- cases for notes that span only one line or are only one character wide.
-- Use 'mkLocation' and 'viewLoc' as well as the respective accessor
-- functions to construct and destruct nodes.
--
-- If no reasonable can be given, use the 'mkNoLoc' function, but be careful
-- not to call 'viewLoc' or any other accessor function on such a
-- 'Location'.
--
data Location
  = LocOneLine { 
      locSource :: LocSource,
      locLine :: {-# UNPACK #-} !Int,
      locSCol :: {-# UNPACK #-} !Int,
      locECol :: {-# UNPACK #-} !Int
    }
  | LocMultiLine {
      locSource  :: LocSource,
      locSLine :: {-# UNPACK #-} !Int,
      locELine :: {-# UNPACK #-} !Int,
      locSCol  :: {-# UNPACK #-} !Int,
      locECol  :: {-# UNPACK #-} !Int
    }
  | LocPoint {
      locSource :: LocSource,
      locLine :: {-# UNPACK #-} !Int,
      locCol  :: {-# UNPACK #-} !Int
    }
  | LocNone { noLocText :: String }
  deriving (Eq, Show)

-- | The \"source\" of a location.
data LocSource
  = FileSrc AbsFilePath
  -- ^ The location refers to a position in a file.
  | OtherSrc String
  -- ^ The location refers to something else, e.g., the command line, or
  -- stdin.
  deriving (Eq, Ord, Show)

instance Ord Location where compare = cmpLoc

-- | Construct a source code location from start and end point.
--
-- If the start point is after the end point, they are swapped
-- automatically.
mkLocation :: LocSource
           -> Int -- ^ start line
           -> Int -- ^ start column
           -> Int -- ^ end line
           -> Int -- ^ end column
           -> Location
mkLocation file l0 c0 l1 c1
  | l0 > l1             = mkLocation file l1 c0 l0 c1
  | l0 == l1 && c0 > c1 = mkLocation file l0 c1 l1 c0
  | l0 == l1  = if c0 == c1
                  then LocPoint file l0 c0
                  else LocOneLine file l0 c0 c1
  | otherwise = LocMultiLine file l0 l1 c0 c1

-- | Construct a source location that does not specify a region.  The
-- argument can be used to give some hint as to why there is no location
-- available.  (E.g., \"File not found\").
mkNoLoc :: String -> Location
mkNoLoc msg = LocNone msg

-- | Remove file name to save on size.
--
-- TODO: Why do we need this?  To save memory?  That could be fixed
-- more sharing.  Or to display things more compactly?  A different
-- display function would be better.
--
trimFile :: Location -> Location
trimFile l@(LocNone _) = l
trimFile l 
  | FileSrc _ <- locSource l = l{ locSource = FileSrc $ AFP "" }
  | otherwise                = l

-- | Test whether a location is valid, i.e., not constructed with 'mkNoLoc'.
isValidLoc :: Location -> Bool
isValidLoc (LocNone _) = False
isValidLoc _           = True

noLocError :: String -> a
noLocError f = error $ f ++ ": argument must not be a noLoc"

-- | Return the start column.  Only defined on valid locations.
locStartCol :: Location -> Int
locStartCol l@LocPoint{} = locCol l
locStartCol LocNone{}  = noLocError "locStartCol"
locStartCol l = locSCol l

-- | Return the end column.  Only defined on valid locations.
locEndCol :: Location -> Int
locEndCol l@LocPoint{} = locCol l
locEndCol LocNone{}  = noLocError "locEndCol"
locEndCol l = locECol l

-- | Return the start line.  Only defined on valid locations.
locStartLine :: Location -> Int
locStartLine l@LocMultiLine{} = locSLine l
locStartLine LocNone{}  = noLocError "locStartLine"
locStartLine l = locLine l

-- | Return the end line.  Only defined on valid locations.
locEndLine :: Location -> Int
locEndLine l@LocMultiLine{} = locELine l
locEndLine LocNone{}  = noLocError "locEndLine"
locEndLine l = locLine l

{-# INLINE viewLoc #-}
-- | View on a (valid) location.
--
-- It holds the property:
--
-- > prop_viewLoc_mkLoc s l0 c0 l1 c1 =
-- >     viewLoc (mkLocation s l0 c0 l1 c1) == (s, l0, c0, l1, c1)
--
viewLoc :: Location
        -> (LocSource, Int, Int, Int, Int)
           -- ^ source, start line, start column, end line, end column.
viewLoc (LocNone txt)=(OtherSrc txt,-1,-1,-1,-1)
viewLoc l = (locSource l, locStartLine l, locStartCol l,
             locEndLine l, locEndCol l)

-- | Comparison function for two 'Location's.
cmpLoc :: Location -> Location -> Ordering
cmpLoc LocNone{} _ = LT
cmpLoc _ LocNone{} = GT
cmpLoc l1 l2 =
    (f1 `compare` f2) `thenCmp`
    (sl1 `compare` sl2) `thenCmp`
    (sc1 `compare` sc2) `thenCmp`
    (el1 `compare` el2) `thenCmp`
    (ec1 `compare` ec2)
 where
   (f1, sl1, sc1, el1, ec1) = viewLoc l1
   (f2, sl2, sc2, el2, ec2) = viewLoc l2

-- | Lexicographic composition two orderings.  Compare using the first
-- ordering, use the second to break ties.
thenCmp :: Ordering -> Ordering -> Ordering
thenCmp EQ x = x
thenCmp x _  = x
{-# INLINE thenCmp #-}

-- * Converting from GHC types.

-- | Convert a 'GHC.SrcSpan' to a 'Location'.
--
-- The first argument is used to normalise relative source locations to an
-- absolute file path.
ghcSpanToLocation :: FilePath -- ^ Base directory
                  -> GHC.SrcSpan
                  -> Location
ghcSpanToLocation baseDir sp
  | GHC.isGoodSrcSpan sp =
      mkLocation mkLocFile
                 (GHC.srcSpanStartLine sp)
                 (GHC.srcSpanStartCol sp)
                 (GHC.srcSpanEndLine sp)
                 (GHC.srcSpanEndCol sp)
  | otherwise =
      mkNoLoc (GHC.showSDoc (GHC.ppr sp))
 where
   mkLocFile =
       case GHC.unpackFS (GHC.srcSpanFile sp) of
         s@('<':_) -> OtherSrc s
         p -> FileSrc $ mkAbsFilePath baseDir p

ghcErrMsgToNote :: FilePath -> GHC.ErrMsg -> Note
ghcErrMsgToNote = ghcMsgToNote ErrorNote

ghcWarnMsgToNote :: FilePath -> GHC.WarnMsg -> Note
ghcWarnMsgToNote = ghcMsgToNote WarningNote

-- Note that we don *not* include the extra info, since that information is
-- only useful in the case where we don not show the error location directly
-- in the source.
ghcMsgToNote :: NoteKind -> FilePath -> GHC.ErrMsg -> Note
ghcMsgToNote note_kind base_dir msg =
    Note { noteLoc = ghcSpanToLocation base_dir loc
         , noteKind = note_kind
         , noteMessage = show_msg (GHC.errMsgShortDoc msg)
         }
  where
    loc | (s:_) <- GHC.errMsgSpans msg = s
        | otherwise                    = GHC.noSrcSpan
    unqual = GHC.errMsgContext msg
    show_msg = GHC.showSDocForUser unqual

-- | Convert 'GHC.Messages' to 'Notes'.
--
-- This will mix warnings and errors, but you can split them back up
-- by filtering the 'Notes' based on the 'noteKind'.
ghcMessagesToNotes :: FilePath -- ^ Base path for normalising paths.
                               -- See 'mkAbsFilePath'.
                   -> GHC.Messages -> Notes
ghcMessagesToNotes base_dir (warns, errs) =
    MS.union (map_bag2ms (ghcWarnMsgToNote base_dir) warns)
             (map_bag2ms (ghcErrMsgToNote base_dir) errs)
  where
    map_bag2ms f = MS.fromList . map f . Bag.bagToList
