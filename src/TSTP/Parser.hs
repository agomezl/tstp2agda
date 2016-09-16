{-# OPTIONS_GHC -w #-}
{-# OPTIONS -fglasgow-exts -cpp #-}
module TSTP.Parser where

import Data.Char
import Data.Data
import Data.Ratio
import Control.Monad
import Data.List as L
import TSTP.Lexer
import TSTP.Base
import Data.Set as S
import Data.TSTP
import System.IO
import System.IO.Unsafe
import Control.Monad.Identity
import qualified Data.Array as Happy_Data_Array
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.5

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
happyIn4 :: ([F]) -> (HappyAbsSyn )
happyIn4 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn4 #-}
happyOut4 :: (HappyAbsSyn ) -> ([F])
happyOut4 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut4 #-}
happyIn5 :: (F) -> (HappyAbsSyn )
happyIn5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn5 #-}
happyOut5 :: (HappyAbsSyn ) -> (F)
happyOut5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut5 #-}
happyIn6 :: (F) -> (HappyAbsSyn )
happyIn6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn6 #-}
happyOut6 :: (HappyAbsSyn ) -> (F)
happyOut6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut6 #-}
happyIn7 :: (F) -> (HappyAbsSyn )
happyIn7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn7 #-}
happyOut7 :: (HappyAbsSyn ) -> (F)
happyOut7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut7 #-}
happyIn8 :: (F) -> (HappyAbsSyn )
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn ) -> (F)
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
happyIn9 :: (Source) -> (HappyAbsSyn )
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn ) -> (Source)
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
happyIn10 :: (Role) -> (HappyAbsSyn )
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> (Role)
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
happyIn11 :: (Formula) -> (HappyAbsSyn )
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> (Formula)
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyIn12 :: (Formula) -> (HappyAbsSyn )
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn ) -> (Formula)
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
happyIn13 :: (Formula) -> (HappyAbsSyn )
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> (Formula)
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
happyIn14 :: (Formula) -> (HappyAbsSyn )
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> (Formula)
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
happyIn15 :: (Formula) -> (HappyAbsSyn )
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> (Formula)
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
happyIn16 :: ([Formula]) -> (HappyAbsSyn )
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn ) -> ([Formula])
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
happyIn17 :: (Formula) -> (HappyAbsSyn )
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn ) -> (Formula)
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
happyIn18 :: ([Formula]) -> (HappyAbsSyn )
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> ([Formula])
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
happyIn19 :: (Formula) -> (HappyAbsSyn )
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> (Formula)
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyIn20 :: (Formula) -> (HappyAbsSyn )
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn ) -> (Formula)
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
happyIn21 :: ([V]) -> (HappyAbsSyn )
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn ) -> ([V])
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
happyIn22 :: (Formula) -> (HappyAbsSyn )
happyIn22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn ) -> (Formula)
happyOut22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut22 #-}
happyIn23 :: (Formula) -> (HappyAbsSyn )
happyIn23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn ) -> (Formula)
happyOut23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut23 #-}
happyIn24 :: (Formula) -> (HappyAbsSyn )
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> (Formula)
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyIn25 :: ([Formula]) -> (HappyAbsSyn )
happyIn25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn25 #-}
happyOut25 :: (HappyAbsSyn ) -> ([Formula])
happyOut25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut25 #-}
happyIn26 :: (Formula) -> (HappyAbsSyn )
happyIn26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn26 #-}
happyOut26 :: (HappyAbsSyn ) -> (Formula)
happyOut26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut26 #-}
happyIn27 :: (Formula) -> (HappyAbsSyn )
happyIn27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn27 #-}
happyOut27 :: (HappyAbsSyn ) -> (Formula)
happyOut27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut27 #-}
happyIn28 :: (Quant) -> (HappyAbsSyn )
happyIn28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn28 #-}
happyOut28 :: (HappyAbsSyn ) -> (Quant)
happyOut28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut28 #-}
happyIn29 :: (BinOp) -> (HappyAbsSyn )
happyIn29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn29 #-}
happyOut29 :: (HappyAbsSyn ) -> (BinOp)
happyOut29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut29 #-}
happyIn30 :: (Formula) -> (HappyAbsSyn )
happyIn30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn30 #-}
happyOut30 :: (HappyAbsSyn ) -> (Formula)
happyOut30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut30 #-}
happyIn31 :: (Formula) -> (HappyAbsSyn )
happyIn31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn31 #-}
happyOut31 :: (HappyAbsSyn ) -> (Formula)
happyOut31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut31 #-}
happyIn32 :: (Formula) -> (HappyAbsSyn )
happyIn32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn32 #-}
happyOut32 :: (HappyAbsSyn ) -> (Formula)
happyOut32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut32 #-}
happyIn33 :: (Formula) -> (HappyAbsSyn )
happyIn33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn33 #-}
happyOut33 :: (HappyAbsSyn ) -> (Formula)
happyOut33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut33 #-}
happyIn34 :: (Formula) -> (HappyAbsSyn )
happyIn34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn34 #-}
happyOut34 :: (HappyAbsSyn ) -> (Formula)
happyOut34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut34 #-}
happyIn35 :: (InfixPred) -> (HappyAbsSyn )
happyIn35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn35 #-}
happyOut35 :: (HappyAbsSyn ) -> (InfixPred)
happyOut35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut35 #-}
happyIn36 :: (InfixPred) -> (HappyAbsSyn )
happyIn36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn36 #-}
happyOut36 :: (HappyAbsSyn ) -> (InfixPred)
happyOut36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut36 #-}
happyIn37 :: (InfixPred) -> (HappyAbsSyn )
happyIn37 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn37 #-}
happyOut37 :: (HappyAbsSyn ) -> (InfixPred)
happyOut37 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut37 #-}
happyIn38 :: (Formula) -> (HappyAbsSyn )
happyIn38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn38 #-}
happyOut38 :: (HappyAbsSyn ) -> (Formula)
happyOut38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut38 #-}
happyIn39 :: (Term) -> (HappyAbsSyn )
happyIn39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn39 #-}
happyOut39 :: (HappyAbsSyn ) -> (Term)
happyOut39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut39 #-}
happyIn40 :: (Term) -> (HappyAbsSyn )
happyIn40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn40 #-}
happyOut40 :: (HappyAbsSyn ) -> (Term)
happyOut40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut40 #-}
happyIn41 :: (Term) -> (HappyAbsSyn )
happyIn41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn41 #-}
happyOut41 :: (HappyAbsSyn ) -> (Term)
happyOut41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut41 #-}
happyIn42 :: (AtomicWord) -> (HappyAbsSyn )
happyIn42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn42 #-}
happyOut42 :: (HappyAbsSyn ) -> (AtomicWord)
happyOut42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut42 #-}
happyIn43 :: (AtomicWord) -> (HappyAbsSyn )
happyIn43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn43 #-}
happyOut43 :: (HappyAbsSyn ) -> (AtomicWord)
happyOut43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut43 #-}
happyIn44 :: (Term) -> (HappyAbsSyn )
happyIn44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn44 #-}
happyOut44 :: (HappyAbsSyn ) -> (Term)
happyOut44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut44 #-}
happyIn45 :: (Term) -> (HappyAbsSyn )
happyIn45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn45 #-}
happyOut45 :: (HappyAbsSyn ) -> (Term)
happyOut45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut45 #-}
happyIn46 :: (Term) -> (HappyAbsSyn )
happyIn46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn46 #-}
happyOut46 :: (HappyAbsSyn ) -> (Term)
happyOut46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut46 #-}
happyIn47 :: (Term) -> (HappyAbsSyn )
happyIn47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn47 #-}
happyOut47 :: (HappyAbsSyn ) -> (Term)
happyOut47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut47 #-}
happyIn48 :: (String) -> (HappyAbsSyn )
happyIn48 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn48 #-}
happyOut48 :: (HappyAbsSyn ) -> (String)
happyOut48 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut48 #-}
happyIn49 :: (String) -> (HappyAbsSyn )
happyIn49 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn49 #-}
happyOut49 :: (HappyAbsSyn ) -> (String)
happyOut49 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut49 #-}
happyIn50 :: (Term) -> (HappyAbsSyn )
happyIn50 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn50 #-}
happyOut50 :: (HappyAbsSyn ) -> (Term)
happyOut50 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut50 #-}
happyIn51 :: (String) -> (HappyAbsSyn )
happyIn51 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn51 #-}
happyOut51 :: (HappyAbsSyn ) -> (String)
happyOut51 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut51 #-}
happyIn52 :: (String) -> (HappyAbsSyn )
happyIn52 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn52 #-}
happyOut52 :: (HappyAbsSyn ) -> (String)
happyOut52 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut52 #-}
happyIn53 :: (V) -> (HappyAbsSyn )
happyIn53 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn53 #-}
happyOut53 :: (HappyAbsSyn ) -> (V)
happyOut53 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut53 #-}
happyIn54 :: ([Term]) -> (HappyAbsSyn )
happyIn54 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn54 #-}
happyOut54 :: (HappyAbsSyn ) -> ([Term])
happyOut54 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut54 #-}
happyIn55 :: (GTerm) -> (HappyAbsSyn )
happyIn55 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn55 #-}
happyOut55 :: (HappyAbsSyn ) -> (GTerm)
happyOut55 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut55 #-}
happyIn56 :: (Source) -> (HappyAbsSyn )
happyIn56 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn56 #-}
happyOut56 :: (HappyAbsSyn ) -> (Source)
happyOut56 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut56 #-}
happyIn57 :: (Source) -> (HappyAbsSyn )
happyIn57 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn57 #-}
happyOut57 :: (HappyAbsSyn ) -> (Source)
happyOut57 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut57 #-}
happyIn58 :: (Source) -> (HappyAbsSyn )
happyIn58 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn58 #-}
happyOut58 :: (HappyAbsSyn ) -> (Source)
happyOut58 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut58 #-}
happyIn59 :: (Rule) -> (HappyAbsSyn )
happyIn59 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn59 #-}
happyOut59 :: (HappyAbsSyn ) -> (Rule)
happyOut59 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut59 #-}
happyIn60 :: ([Parent]) -> (HappyAbsSyn )
happyIn60 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn60 #-}
happyOut60 :: (HappyAbsSyn ) -> ([Parent])
happyOut60 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut60 #-}
happyIn61 :: (Parent) -> (HappyAbsSyn )
happyIn61 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn61 #-}
happyOut61 :: (HappyAbsSyn ) -> (Parent)
happyOut61 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut61 #-}
happyIn62 :: ([GTerm]) -> (HappyAbsSyn )
happyIn62 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn62 #-}
happyOut62 :: (HappyAbsSyn ) -> ([GTerm])
happyOut62 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut62 #-}
happyIn63 :: (Source) -> (HappyAbsSyn )
happyIn63 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn63 #-}
happyOut63 :: (HappyAbsSyn ) -> (Source)
happyOut63 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut63 #-}
happyIn64 :: (IntroType) -> (HappyAbsSyn )
happyIn64 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn64 #-}
happyOut64 :: (HappyAbsSyn ) -> (IntroType)
happyOut64 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut64 #-}
happyIn65 :: (Source) -> (HappyAbsSyn )
happyIn65 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn65 #-}
happyOut65 :: (HappyAbsSyn ) -> (Source)
happyOut65 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut65 #-}
happyIn66 :: (Source) -> (HappyAbsSyn )
happyIn66 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn66 #-}
happyOut66 :: (HappyAbsSyn ) -> (Source)
happyOut66 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut66 #-}
happyIn67 :: (Maybe String) -> (HappyAbsSyn )
happyIn67 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn67 #-}
happyOut67 :: (HappyAbsSyn ) -> (Maybe String)
happyOut67 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut67 #-}
happyIn68 :: (Source) -> (HappyAbsSyn )
happyIn68 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn68 #-}
happyOut68 :: (HappyAbsSyn ) -> (Source)
happyOut68 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut68 #-}
happyIn69 :: (Theory) -> (HappyAbsSyn )
happyIn69 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn69 #-}
happyOut69 :: (HappyAbsSyn ) -> (Theory)
happyOut69 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut69 #-}
happyIn70 :: (Source) -> (HappyAbsSyn )
happyIn70 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn70 #-}
happyOut70 :: (HappyAbsSyn ) -> (Source)
happyOut70 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut70 #-}
happyIn71 :: (String) -> (HappyAbsSyn )
happyIn71 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn71 #-}
happyOut71 :: (HappyAbsSyn ) -> (String)
happyOut71 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut71 #-}
happyIn72 :: ([Info]) -> (HappyAbsSyn )
happyIn72 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn72 #-}
happyOut72 :: (HappyAbsSyn ) -> ([Info])
happyOut72 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut72 #-}
happyIn73 :: ([Info]) -> (HappyAbsSyn )
happyIn73 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn73 #-}
happyOut73 :: (HappyAbsSyn ) -> ([Info])
happyOut73 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut73 #-}
happyIn74 :: ([Info]) -> (HappyAbsSyn )
happyIn74 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn74 #-}
happyOut74 :: (HappyAbsSyn ) -> ([Info])
happyOut74 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut74 #-}
happyIn75 :: (Info) -> (HappyAbsSyn )
happyIn75 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn75 #-}
happyOut75 :: (HappyAbsSyn ) -> (Info)
happyOut75 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut75 #-}
happyIn76 :: (Info) -> (HappyAbsSyn )
happyIn76 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn76 #-}
happyOut76 :: (HappyAbsSyn ) -> (Info)
happyOut76 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut76 #-}
happyIn77 :: (Info) -> (HappyAbsSyn )
happyIn77 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn77 #-}
happyOut77 :: (HappyAbsSyn ) -> (Info)
happyOut77 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut77 #-}
happyIn78 :: (Info) -> (HappyAbsSyn )
happyIn78 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn78 #-}
happyOut78 :: (HappyAbsSyn ) -> (Info)
happyOut78 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut78 #-}
happyIn79 :: (Info) -> (HappyAbsSyn )
happyIn79 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn79 #-}
happyOut79 :: (HappyAbsSyn ) -> (Info)
happyOut79 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut79 #-}
happyIn80 :: (Info) -> (HappyAbsSyn )
happyIn80 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn80 #-}
happyOut80 :: (HappyAbsSyn ) -> (Info)
happyOut80 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut80 #-}
happyIn81 :: (Info) -> (HappyAbsSyn )
happyIn81 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn81 #-}
happyOut81 :: (HappyAbsSyn ) -> (Info)
happyOut81 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut81 #-}
happyIn82 :: (Status) -> (HappyAbsSyn )
happyIn82 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn82 #-}
happyOut82 :: (HappyAbsSyn ) -> (Status)
happyOut82 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut82 #-}
happyIn83 :: (Info) -> (HappyAbsSyn )
happyIn83 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn83 #-}
happyOut83 :: (HappyAbsSyn ) -> (Info)
happyOut83 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut83 #-}
happyIn84 :: (Info) -> (HappyAbsSyn )
happyIn84 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn84 #-}
happyOut84 :: (HappyAbsSyn ) -> (Info)
happyOut84 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut84 #-}
happyIn85 :: (Info) -> (HappyAbsSyn )
happyIn85 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn85 #-}
happyOut85 :: (HappyAbsSyn ) -> (Info)
happyOut85 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut85 #-}
happyIn86 :: ([AtomicWord]) -> (HappyAbsSyn )
happyIn86 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn86 #-}
happyOut86 :: (HappyAbsSyn ) -> ([AtomicWord])
happyOut86 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut86 #-}
happyIn87 :: (GTerm) -> (HappyAbsSyn )
happyIn87 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn87 #-}
happyOut87 :: (HappyAbsSyn ) -> (GTerm)
happyOut87 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut87 #-}
happyIn88 :: (GData) -> (HappyAbsSyn )
happyIn88 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn88 #-}
happyOut88 :: (HappyAbsSyn ) -> (GData)
happyOut88 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut88 #-}
happyIn89 :: (GData) -> (HappyAbsSyn )
happyIn89 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn89 #-}
happyOut89 :: (HappyAbsSyn ) -> (GData)
happyOut89 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut89 #-}
happyIn90 :: ([GTerm]) -> (HappyAbsSyn )
happyIn90 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn90 #-}
happyOut90 :: (HappyAbsSyn ) -> ([GTerm])
happyOut90 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut90 #-}
happyIn91 :: ([GTerm]) -> (HappyAbsSyn )
happyIn91 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn91 #-}
happyOut91 :: (HappyAbsSyn ) -> ([GTerm])
happyOut91 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut91 #-}
happyIn92 :: (AtomicWord) -> (HappyAbsSyn )
happyIn92 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn92 #-}
happyOut92 :: (HappyAbsSyn ) -> (AtomicWord)
happyOut92 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut92 #-}
happyIn93 :: (AtomicWord) -> (HappyAbsSyn )
happyIn93 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn93 #-}
happyOut93 :: (HappyAbsSyn ) -> (AtomicWord)
happyOut93 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut93 #-}
happyIn94 :: (String) -> (HappyAbsSyn )
happyIn94 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn94 #-}
happyOut94 :: (HappyAbsSyn ) -> (String)
happyOut94 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut94 #-}
happyIn95 :: (String) -> (HappyAbsSyn )
happyIn95 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn95 #-}
happyOut95 :: (HappyAbsSyn ) -> (String)
happyOut95 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut95 #-}
happyIn96 :: (Rational) -> (HappyAbsSyn )
happyIn96 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn96 #-}
happyOut96 :: (HappyAbsSyn ) -> (Rational)
happyOut96 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut96 #-}
happyIn97 :: (Integer) -> (HappyAbsSyn )
happyIn97 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn97 #-}
happyOut97 :: (HappyAbsSyn ) -> (Integer)
happyOut97 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut97 #-}
happyIn98 :: (Rational) -> (HappyAbsSyn )
happyIn98 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn98 #-}
happyOut98 :: (HappyAbsSyn ) -> (Rational)
happyOut98 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut98 #-}
happyIn99 :: (String) -> (HappyAbsSyn )
happyIn99 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn99 #-}
happyOut99 :: (HappyAbsSyn ) -> (String)
happyOut99 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut99 #-}
happyIn100 :: (String) -> (HappyAbsSyn )
happyIn100 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn100 #-}
happyOut100 :: (HappyAbsSyn ) -> (String)
happyOut100 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut100 #-}
happyIn101 :: (Token) -> (HappyAbsSyn )
happyIn101 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn101 #-}
happyOut101 :: (HappyAbsSyn ) -> (Token)
happyOut101 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut101 #-}
happyIn102 :: (Token) -> (HappyAbsSyn )
happyIn102 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn102 #-}
happyOut102 :: (HappyAbsSyn ) -> (Token)
happyOut102 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut102 #-}
happyIn103 :: (Token) -> (HappyAbsSyn )
happyIn103 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn103 #-}
happyOut103 :: (HappyAbsSyn ) -> (Token)
happyOut103 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut103 #-}
happyIn104 :: (Token) -> (HappyAbsSyn )
happyIn104 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn104 #-}
happyOut104 :: (HappyAbsSyn ) -> (Token)
happyOut104 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut104 #-}
happyIn105 :: (Token) -> (HappyAbsSyn )
happyIn105 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn105 #-}
happyOut105 :: (HappyAbsSyn ) -> (Token)
happyOut105 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut105 #-}
happyIn106 :: (Token) -> (HappyAbsSyn )
happyIn106 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn106 #-}
happyOut106 :: (HappyAbsSyn ) -> (Token)
happyOut106 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut106 #-}
happyIn107 :: (Token) -> (HappyAbsSyn )
happyIn107 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn107 #-}
happyOut107 :: (HappyAbsSyn ) -> (Token)
happyOut107 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut107 #-}
happyIn108 :: (Token) -> (HappyAbsSyn )
happyIn108 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn108 #-}
happyOut108 :: (HappyAbsSyn ) -> (Token)
happyOut108 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut108 #-}
happyIn109 :: (Token) -> (HappyAbsSyn )
happyIn109 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn109 #-}
happyOut109 :: (HappyAbsSyn ) -> (Token)
happyOut109 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut109 #-}
happyIn110 :: (Token) -> (HappyAbsSyn )
happyIn110 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn110 #-}
happyOut110 :: (HappyAbsSyn ) -> (Token)
happyOut110 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut110 #-}
happyIn111 :: (Token) -> (HappyAbsSyn )
happyIn111 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn111 #-}
happyOut111 :: (HappyAbsSyn ) -> (Token)
happyOut111 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut111 #-}
happyIn112 :: (Token) -> (HappyAbsSyn )
happyIn112 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn112 #-}
happyOut112 :: (HappyAbsSyn ) -> (Token)
happyOut112 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut112 #-}
happyIn113 :: (Token) -> (HappyAbsSyn )
happyIn113 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn113 #-}
happyOut113 :: (HappyAbsSyn ) -> (Token)
happyOut113 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut113 #-}
happyIn114 :: (Token) -> (HappyAbsSyn )
happyIn114 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn114 #-}
happyOut114 :: (HappyAbsSyn ) -> (Token)
happyOut114 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut114 #-}
happyIn115 :: (Token) -> (HappyAbsSyn )
happyIn115 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn115 #-}
happyOut115 :: (HappyAbsSyn ) -> (Token)
happyOut115 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut115 #-}
happyIn116 :: (Token) -> (HappyAbsSyn )
happyIn116 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn116 #-}
happyOut116 :: (HappyAbsSyn ) -> (Token)
happyOut116 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut116 #-}
happyIn117 :: (Token) -> (HappyAbsSyn )
happyIn117 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn117 #-}
happyOut117 :: (HappyAbsSyn ) -> (Token)
happyOut117 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut117 #-}
happyIn118 :: (Token) -> (HappyAbsSyn )
happyIn118 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn118 #-}
happyOut118 :: (HappyAbsSyn ) -> (Token)
happyOut118 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut118 #-}
happyIn119 :: (Token) -> (HappyAbsSyn )
happyIn119 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn119 #-}
happyOut119 :: (HappyAbsSyn ) -> (Token)
happyOut119 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut119 #-}
happyIn120 :: (Token) -> (HappyAbsSyn )
happyIn120 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn120 #-}
happyOut120 :: (HappyAbsSyn ) -> (Token)
happyOut120 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut120 #-}
happyIn121 :: (Token) -> (HappyAbsSyn )
happyIn121 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn121 #-}
happyOut121 :: (HappyAbsSyn ) -> (Token)
happyOut121 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut121 #-}
happyIn122 :: (Token) -> (HappyAbsSyn )
happyIn122 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn122 #-}
happyOut122 :: (HappyAbsSyn ) -> (Token)
happyOut122 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut122 #-}
happyIn123 :: (Token) -> (HappyAbsSyn )
happyIn123 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn123 #-}
happyOut123 :: (HappyAbsSyn ) -> (Token)
happyOut123 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut123 #-}
happyIn124 :: (Token) -> (HappyAbsSyn )
happyIn124 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn124 #-}
happyOut124 :: (HappyAbsSyn ) -> (Token)
happyOut124 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut124 #-}
happyIn125 :: (Token) -> (HappyAbsSyn )
happyIn125 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn125 #-}
happyOut125 :: (HappyAbsSyn ) -> (Token)
happyOut125 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut125 #-}
happyIn126 :: (Token) -> (HappyAbsSyn )
happyIn126 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn126 #-}
happyOut126 :: (HappyAbsSyn ) -> (Token)
happyOut126 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut126 #-}
happyIn127 :: (String) -> (HappyAbsSyn )
happyIn127 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn127 #-}
happyOut127 :: (HappyAbsSyn ) -> (String)
happyOut127 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut127 #-}
happyIn128 :: (String) -> (HappyAbsSyn )
happyIn128 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn128 #-}
happyOut128 :: (HappyAbsSyn ) -> (String)
happyOut128 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut128 #-}
happyIn129 :: (String) -> (HappyAbsSyn )
happyIn129 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn129 #-}
happyOut129 :: (HappyAbsSyn ) -> (String)
happyOut129 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut129 #-}
happyIn130 :: (String) -> (HappyAbsSyn )
happyIn130 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn130 #-}
happyOut130 :: (HappyAbsSyn ) -> (String)
happyOut130 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut130 #-}
happyIn131 :: (String) -> (HappyAbsSyn )
happyIn131 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn131 #-}
happyOut131 :: (HappyAbsSyn ) -> (String)
happyOut131 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut131 #-}
happyIn132 :: (String) -> (HappyAbsSyn )
happyIn132 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn132 #-}
happyOut132 :: (HappyAbsSyn ) -> (String)
happyOut132 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut132 #-}
happyIn133 :: (Integer) -> (HappyAbsSyn )
happyIn133 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn133 #-}
happyOut133 :: (HappyAbsSyn ) -> (Integer)
happyOut133 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut133 #-}
happyIn134 :: (Integer) -> (HappyAbsSyn )
happyIn134 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn134 #-}
happyOut134 :: (HappyAbsSyn ) -> (Integer)
happyOut134 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut134 #-}
happyIn135 :: (Rational) -> (HappyAbsSyn )
happyIn135 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn135 #-}
happyOut135 :: (HappyAbsSyn ) -> (Rational)
happyOut135 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut135 #-}
happyIn136 :: (Token) -> (HappyAbsSyn )
happyIn136 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn136 #-}
happyOut136 :: (HappyAbsSyn ) -> (Token)
happyOut136 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut136 #-}
happyIn137 :: (Token) -> (HappyAbsSyn )
happyIn137 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn137 #-}
happyOut137 :: (HappyAbsSyn ) -> (Token)
happyOut137 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut137 #-}
happyIn138 :: (Token) -> (HappyAbsSyn )
happyIn138 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn138 #-}
happyOut138 :: (HappyAbsSyn ) -> (Token)
happyOut138 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut138 #-}
happyIn139 :: (Token) -> (HappyAbsSyn )
happyIn139 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn139 #-}
happyOut139 :: (HappyAbsSyn ) -> (Token)
happyOut139 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut139 #-}
happyIn140 :: (Token) -> (HappyAbsSyn )
happyIn140 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn140 #-}
happyOut140 :: (HappyAbsSyn ) -> (Token)
happyOut140 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut140 #-}
happyIn141 :: (Token) -> (HappyAbsSyn )
happyIn141 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn141 #-}
happyOut141 :: (HappyAbsSyn ) -> (Token)
happyOut141 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut141 #-}
happyIn142 :: (Token) -> (HappyAbsSyn )
happyIn142 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn142 #-}
happyOut142 :: (HappyAbsSyn ) -> (Token)
happyOut142 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut142 #-}
happyIn143 :: (Token) -> (HappyAbsSyn )
happyIn143 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn143 #-}
happyOut143 :: (HappyAbsSyn ) -> (Token)
happyOut143 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut143 #-}
happyIn144 :: (Token) -> (HappyAbsSyn )
happyIn144 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn144 #-}
happyOut144 :: (HappyAbsSyn ) -> (Token)
happyOut144 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut144 #-}
happyIn145 :: (Token) -> (HappyAbsSyn )
happyIn145 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn145 #-}
happyOut145 :: (HappyAbsSyn ) -> (Token)
happyOut145 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut145 #-}
happyIn146 :: (Token) -> (HappyAbsSyn )
happyIn146 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn146 #-}
happyOut146 :: (HappyAbsSyn ) -> (Token)
happyOut146 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut146 #-}
happyIn147 :: (Token) -> (HappyAbsSyn )
happyIn147 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn147 #-}
happyOut147 :: (HappyAbsSyn ) -> (Token)
happyOut147 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut147 #-}
happyIn148 :: ([String]) -> (HappyAbsSyn )
happyIn148 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn148 #-}
happyOut148 :: (HappyAbsSyn ) -> ([String])
happyOut148 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut148 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x38\x00\x00\x00\xe8\x02\x38\x00\x00\x00\x00\x00\x00\x00\x1b\x03\x1b\x03\xe7\x02\xe7\x02\x00\x00\xe7\x02\x00\x00\x33\x00\xe7\x02\x33\x00\x00\x00\x15\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe4\x02\xe4\x02\xe4\x02\xe4\x02\x00\x00\x12\x03\x00\x00\x0e\x01\xe1\x02\x00\x00\x00\x00\x00\x00\x00\x00\x0e\x01\x0b\x03\x00\x00\x00\x00\x0b\x03\x45\x04\xed\x03\x0b\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x90\x01\x00\x00\x00\x00\x00\x00\x0e\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd3\x00\x00\x00\xd1\x00\x00\x00\x0d\x03\x00\x00\x00\x00\x00\x00\xc8\x00\x00\x00\x0d\x03\xb6\x00\x00\x00\x0d\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xda\x02\x00\x00\xed\x03\x00\x00\x00\x00\xed\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd3\x02\xd3\x02\xd3\x02\xd3\x02\xd3\x02\xd3\x02\xd3\x02\xd3\x02\xd3\x02\x01\x03\x00\x00\xef\x02\x00\x00\x00\x00\x63\x03\xcc\x03\x00\x00\xf3\x02\xfd\x02\x00\x00\x63\x03\xca\x02\xfb\x02\x01\x06\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xfb\x02\xcb\x02\xcc\x03\xcc\x03\xcc\x03\xcc\x03\x00\x00\xcc\x03\x00\x00\x00\x00\xc7\x02\xc7\x02\xcc\x02\xb5\x02\xed\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xed\x03\xed\x03\xb5\x02\xb5\x02\xb5\x02\xb5\x02\xb5\x02\xb5\x02\xb5\x02\xdc\x02\xd6\x02\xa9\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc5\x02\xb3\x02\x00\x00\x00\x00\xd5\x02\xc4\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc4\x02\xc3\x02\xc3\x02\xc3\x02\x00\x00\x00\x00\xba\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb7\x02\xb7\x02\xb7\x02\xb7\x02\xb7\x02\x8a\x02\x8a\x02\x8a\x02\x8a\x02\x8a\x02\xb0\x02\x00\x00\xa1\x02\x00\x00\x00\x00\x00\x00\x7e\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb2\x00\x0e\x01\x29\x00\x8b\x02\xb2\x00\x00\x00\xa8\x02\x00\x00\x00\x00\x00\x00\xcc\x03\x7c\x02\x9f\x02\x73\x02\x00\x00\xed\x03\x00\x00\xed\x03\x00\x00\x00\x00\x92\x02\x91\x02\x00\x00\xed\x03\x6f\x02\x00\x00\x00\x00\x00\x00\xb3\x04\xa0\x02\x00\x00\xa0\x02\x00\x00\xa0\x02\x00\x00\x00\x00\x6e\x02\x6e\x02\x96\x02\x00\x00\x96\x02\x00\x00\x00\x00\x9e\x02\x9e\x02\x00\x00\x00\x00\x9e\x02\x9e\x02\x33\x00\x99\x02\x98\x02\x8e\x02\x8c\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8f\x02\x00\x00\x8f\x02\x8f\x02\x8f\x02\x8f\x02\x8f\x02\x5b\x02\x5b\x02\x5b\x02\x5b\x02\x5b\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb2\x00\x6d\x02\x86\x02\x0e\x01\xb2\x00\x62\x04\xcc\x07\x00\x00\xb2\x00\x83\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x84\x02\x81\x02\x00\x00\x00\x00\x81\x02\x7b\x02\x00\x00\x00\x00\x72\x02\x68\x02\x00\x00\x59\x03\x00\x00\x68\x02\x68\x02\x68\x02\x66\x02\x66\x02\x00\x00\x33\x00\x66\x02\x66\x02\x00\x00\x00\x00\x63\x02\x61\x02\x00\x00\x00\x00\xcc\x03\x45\x04\xed\x03\x60\x02\x00\x00\x62\x04\x00\x00\x62\x04\x62\x04\x51\x02\xb2\x00\x4f\x02\x4b\x02\x39\x02\x48\x02\x00\x00\x00\x00\x48\x02\x00\x00\x48\x02\x48\x02\x48\x02\x33\x00\x48\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x46\x02\xb2\x00\x40\x02\x00\x00\x00\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x3f\x00\x00\x00\x00\x00\x32\x00\x00\x00\x00\x00\x00\x00\xe0\x01\xdf\x01\xad\x01\xa6\x01\x00\x00\xa5\x01\x00\x00\x66\x05\xa4\x01\xfd\x04\x00\x00\xc9\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa3\x01\xa2\x01\xa1\x01\xa0\x01\x00\x00\xc8\x01\x00\x00\x49\x00\x96\x01\x00\x00\x00\x00\x00\x00\x00\x00\x36\x00\xc6\x01\x00\x00\x00\x00\xc2\x01\x09\x05\xf4\x00\x0a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x00\x00\x00\x00\x00\x00\xc1\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\xbc\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xbb\x01\x00\x00\x00\x00\xba\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x77\x00\x00\x00\x00\x00\x27\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8a\x01\x85\x01\x84\x01\x83\x01\x82\x01\x81\x01\x80\x01\x6f\x01\x64\x01\x06\x00\x00\x00\xf3\xff\x00\x00\x00\x00\x79\x05\x51\x06\x00\x00\x19\x00\x91\x01\x00\x00\xe7\x05\x62\x01\x8f\x01\xc9\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8d\x01\x5c\x01\x32\x07\xd1\x06\xc1\x06\xb2\x07\x00\x00\xa3\x07\x00\x00\x00\x00\x4f\x01\x4b\x01\x2d\x00\x45\x01\xb2\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3d\x03\xc8\x02\x44\x01\x3e\x01\x3d\x01\x3c\x01\x3b\x01\x38\x01\x30\x01\x5d\x01\x5b\x01\x2c\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x23\x00\x00\x00\x00\x00\x5a\x01\x58\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x54\x01\x59\x01\x56\x01\x28\x01\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x55\x01\x51\x01\x50\x01\x4e\x01\x47\x01\x17\x01\xef\x00\xee\x00\xed\x00\xec\x00\x14\x01\x00\x00\xf1\xff\x00\x00\x00\x00\x00\x00\xda\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x2c\x03\xfe\x02\x03\x00\x54\x00\x29\x01\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x60\x06\x09\x00\xff\x00\xd6\x00\x00\x00\x53\x02\x00\x00\xde\x01\x00\x00\x00\x00\x0d\x00\x22\x00\x00\x00\x69\x01\xc9\x00\x00\x00\x00\x00\x00\x00\xf0\x07\xfa\x00\x00\x00\xed\xff\x00\x00\xf7\xff\x00\x00\x00\x00\xc6\x00\xbb\x00\xe9\xff\x00\x00\xca\xff\x00\x00\x00\x00\xf6\x00\xf5\x00\x00\x00\x00\x00\xf1\x00\xea\x00\xf9\x04\xcb\xff\xe9\x00\xe5\x00\xde\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe7\x00\x00\x00\xe6\x00\xe3\x00\xe0\x00\xdb\x00\xd0\x00\xaa\x00\xa3\x00\xa2\x00\xa0\x00\x9b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x88\x02\x08\x00\xa7\x00\x66\x00\x13\x02\x41\x02\x13\x08\x00\x00\x9e\x01\xc5\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa6\x00\xc4\x00\x00\x00\x00\x00\xb0\x00\x9e\x00\x00\x00\x00\x00\xa5\x00\xa4\x00\x00\x00\xe2\x00\x00\x00\xa1\x00\x9f\x00\x0b\x00\x87\x00\x86\x00\x00\x00\x62\x05\x85\x00\x7b\x00\x00\x00\x00\x00\x72\x00\x05\x00\x00\x00\x00\x00\x42\x07\x98\x04\xfa\xff\x55\x00\x00\x00\xcc\x01\x00\x00\xb6\x02\x57\x01\x78\x00\x72\x03\xff\xff\xf4\xff\xd3\xff\x53\x00\x00\x00\x00\x00\x4b\x00\x00\x00\x2e\x00\x0e\x00\xe8\xff\x88\x04\xd5\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x6a\x00\xb4\x00\xb1\xff\x00\x00\x00\x00\x00\x00\x00\x00"#

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\xfe\xff\x00\x00\x00\x00\xfe\xff\xfc\xff\xfb\xff\xfa\xff\x00\x00\x00\x00\x25\xff\x25\xff\x3c\xff\x25\xff\x3d\xff\x00\x00\x25\xff\x00\x00\xfd\xff\x00\x00\x65\xff\x63\xff\x57\xff\x56\xff\x55\xff\x62\xff\x58\xff\x64\xff\x25\xff\x25\xff\x25\xff\x25\xff\x54\xff\x00\x00\x24\xff\x00\x00\x25\xff\x33\xff\x35\xff\x3a\xff\x3b\xff\x00\x00\x00\x00\xf5\xff\x50\xff\x00\x00\x00\x00\x00\x00\xf6\xff\xf4\xff\xf2\xff\xf1\xff\xef\xff\xee\xff\xf3\xff\xe7\xff\xe6\xff\xdf\xff\x00\x00\xe5\xff\xcd\xff\xcc\xff\xc9\xff\xc8\xff\xcb\xff\x00\x00\xc1\xff\xca\xff\xbc\xff\xba\xff\xbe\xff\xb8\xff\xb7\xff\xc7\xff\xb3\xff\xb1\xff\xc2\xff\xaf\xff\xad\xff\xc0\xff\xb9\xff\xb0\xff\xac\xff\xb6\xff\x5f\xff\x5e\xff\x00\x00\xd5\xff\xd4\xff\x00\x00\xb5\xff\x61\xff\x60\xff\xab\xff\x5c\xff\x5b\xff\x5d\xff\x25\xff\x25\xff\x25\xff\x25\xff\x25\xff\x25\xff\x25\xff\x25\xff\x25\xff\xf6\xff\xdd\xff\xdb\xff\xd7\xff\xd9\xff\x00\x00\x00\x00\xd8\xff\x00\x00\x00\x00\xdc\xff\x00\x00\x25\xff\x00\x00\x00\x00\x32\xff\x34\xff\x36\xff\x37\xff\x38\xff\x39\xff\x3e\xff\x41\xff\x42\xff\xe0\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc5\xff\x00\x00\xc4\xff\xc3\xff\x25\xff\x25\xff\x00\x00\x25\xff\x00\x00\xd3\xff\xd2\xff\xd0\xff\xcf\xff\xce\xff\xd1\xff\x00\x00\x00\x00\x25\xff\x25\xff\x25\xff\x25\xff\x25\xff\x25\xff\x25\xff\x00\x00\x00\x00\x25\xff\x40\xff\x45\xff\x46\xff\x47\xff\x48\xff\x49\xff\x4a\xff\xec\xff\xe9\xff\xf0\xff\x52\xff\x00\x00\xe2\xff\x43\xff\x44\xff\xd6\xff\xbf\xff\xb4\xff\xbd\xff\xc6\xff\xaa\xff\x00\x00\x00\x00\x00\x00\x5a\xff\xe4\xff\x8d\xff\xa7\xff\xa3\xff\xa6\xff\xa5\xff\x99\xff\x98\xff\x97\xff\xa4\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x25\xff\x25\xff\x25\xff\x25\xff\x25\xff\x00\x00\x3f\xff\xdb\xff\xde\xff\xda\xff\xf8\xff\x25\xff\x2b\xff\x2f\xff\x30\xff\x2e\xff\x31\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf7\xff\x00\x00\xae\xff\xb2\xff\xbb\xff\x00\x00\x00\x00\x00\x00\x25\xff\xea\xff\x00\x00\xed\xff\x00\x00\x53\xff\xf9\xff\xec\xff\xe9\xff\x51\xff\x00\x00\x25\xff\xe1\xff\xa9\xff\x8e\xff\x00\x00\x00\x00\xa1\xff\x94\xff\x59\xff\x8d\xff\x91\xff\x92\xff\x25\xff\x25\xff\x8d\xff\x9a\xff\x8d\xff\x8f\xff\x4f\xff\x00\x00\x00\x00\x2c\xff\x2d\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8a\xff\x86\xff\x88\xff\x84\xff\x83\xff\x87\xff\x80\xff\x7c\xff\x7f\xff\x7e\xff\x00\x00\x8c\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x25\xff\x25\xff\x25\xff\x25\xff\x25\xff\x4b\xff\xe3\xff\xe8\xff\xeb\xff\x26\xff\x27\xff\x28\xff\x29\xff\x2a\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8b\xff\x00\x00\x00\x00\x95\xff\x96\xff\x93\xff\x9b\xff\x90\xff\x00\x00\x00\x00\x89\xff\x6f\xff\x67\xff\x75\xff\x71\xff\x73\xff\x00\x00\x72\xff\x6e\xff\x00\x00\x6d\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7b\xff\x00\x00\x00\x00\x00\x00\x82\xff\x78\xff\x00\x00\x77\xff\x7d\xff\x81\xff\x00\x00\x00\x00\x00\x00\x00\x00\x69\xff\x00\x00\x85\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0\xff\x9c\xff\x00\x00\x66\xff\x74\xff\x00\x00\x68\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x79\xff\x76\xff\x6a\xff\x6b\xff\x6c\xff\x70\xff\x7a\xff\x9e\xff\x00\x00\x00\x00\x00\x00\xa2\xff\x9f\xff\x9d\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x15\x00\x0d\x00\x15\x00\x0f\x00\x10\x00\x05\x00\x12\x00\x3a\x00\x44\x00\x05\x00\x45\x00\x17\x00\x18\x00\x62\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x0c\x00\x11\x00\x0c\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x3f\x00\x44\x00\x63\x00\x65\x00\x0e\x00\x0e\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x62\x00\x1f\x00\x20\x00\x31\x00\x44\x00\x06\x00\x6a\x00\x11\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x41\x00\x44\x00\x3e\x00\x45\x00\x1f\x00\x20\x00\x62\x00\x18\x00\x19\x00\x1a\x00\x65\x00\x06\x00\x18\x00\x19\x00\x65\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\x65\x00\x60\x00\x61\x00\x65\x00\x2a\x00\x31\x00\x1f\x00\x20\x00\x21\x00\x2f\x00\x64\x00\x31\x00\x63\x00\x65\x00\x76\x00\x19\x00\x76\x00\x65\x00\x65\x00\x61\x00\x73\x00\x74\x00\x65\x00\x62\x00\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x76\x00\x0d\x00\x76\x00\x0f\x00\x10\x00\x7f\x00\x12\x00\x71\x00\x88\x00\x89\x00\x85\x00\x17\x00\x18\x00\x62\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x60\x00\x75\x00\x75\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x60\x00\x78\x00\x79\x00\x7f\x00\x62\x00\x78\x00\x79\x00\x7a\x00\x71\x00\x72\x00\x5f\x00\x4e\x00\x62\x00\x80\x00\x78\x00\x79\x00\x64\x00\x6b\x00\x6c\x00\x6d\x00\x6e\x00\x6f\x00\x70\x00\x56\x00\x78\x00\x79\x00\x7a\x00\x75\x00\x76\x00\x60\x00\x11\x00\x12\x00\x80\x00\x18\x00\x19\x00\x1a\x00\x63\x00\x56\x00\x7b\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\x64\x00\x60\x00\x61\x00\x11\x00\x12\x00\x63\x00\x2a\x00\x62\x00\x78\x00\x79\x00\x7a\x00\x2f\x00\x11\x00\x12\x00\x11\x00\x12\x00\x80\x00\x62\x00\x62\x00\x62\x00\x73\x00\x74\x00\x38\x00\x39\x00\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x61\x00\x0d\x00\x61\x00\x0f\x00\x10\x00\x61\x00\x12\x00\x62\x00\x6a\x00\x63\x00\x63\x00\x17\x00\x18\x00\x59\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x31\x00\x60\x00\x65\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x18\x00\x19\x00\x1a\x00\x65\x00\x65\x00\x90\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x90\x00\x61\x00\x90\x00\x90\x00\x80\x00\x53\x00\x54\x00\x55\x00\x56\x00\x57\x00\x90\x00\x59\x00\x61\x00\x2f\x00\x5c\x00\x5d\x00\x5e\x00\x61\x00\x60\x00\x65\x00\x61\x00\x63\x00\x64\x00\x61\x00\x61\x00\x64\x00\x61\x00\x90\x00\x62\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\x62\x00\x60\x00\x61\x00\x90\x00\x62\x00\x62\x00\x90\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x65\x00\x37\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x90\x00\x73\x00\x74\x00\x6a\x00\x90\x00\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x0f\x00\x10\x00\x66\x00\x12\x00\x90\x00\x90\x00\x90\x00\x90\x00\x17\x00\x18\x00\x59\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x31\x00\x60\x00\x62\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x15\x00\x16\x00\x90\x00\x61\x00\x80\x00\x53\x00\x54\x00\x55\x00\x56\x00\x57\x00\x61\x00\x59\x00\x61\x00\x61\x00\x5c\x00\x5d\x00\x5e\x00\x61\x00\x60\x00\x62\x00\x65\x00\x63\x00\x62\x00\x90\x00\x65\x00\x64\x00\x62\x00\x90\x00\x66\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\x90\x00\x60\x00\x61\x00\x90\x00\x90\x00\x90\x00\x90\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x90\x00\x90\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x90\x00\x73\x00\x74\x00\x82\x00\x90\x00\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x0f\x00\x10\x00\x62\x00\x12\x00\x62\x00\x90\x00\x62\x00\x90\x00\x17\x00\x18\x00\x59\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x31\x00\x60\x00\x90\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x90\x00\x90\x00\x90\x00\x90\x00\x90\x00\x90\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x90\x00\x61\x00\x61\x00\x61\x00\x80\x00\x53\x00\x54\x00\x55\x00\x56\x00\x57\x00\x63\x00\x59\x00\x90\x00\x65\x00\x5c\x00\x5d\x00\x5e\x00\x65\x00\x60\x00\x65\x00\x65\x00\x63\x00\x90\x00\x90\x00\x90\x00\x90\x00\x90\x00\x90\x00\x90\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\x90\x00\x60\x00\x61\x00\x61\x00\x61\x00\x02\x00\x0a\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x03\x00\x02\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x05\x00\x73\x00\x74\x00\x04\x00\x03\x00\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x0f\x00\x10\x00\x04\x00\x12\x00\x05\x00\x04\x00\x02\x00\x01\x00\x17\x00\x18\x00\x59\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x31\x00\x60\x00\x02\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x0a\x00\x05\x00\x03\x00\x05\x00\x03\x00\x1d\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x34\x00\x01\x00\x05\x00\x04\x00\x80\x00\x53\x00\x54\x00\x55\x00\x56\x00\x57\x00\x01\x00\x59\x00\x05\x00\x03\x00\x5c\x00\x5d\x00\x5e\x00\x02\x00\x60\x00\x34\x00\x34\x00\x63\x00\x05\x00\x15\x00\x34\x00\x16\x00\x0a\x00\x2e\x00\x03\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\x34\x00\x60\x00\x61\x00\x2a\x00\x06\x00\x16\x00\x01\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x34\x00\x05\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x02\x00\x73\x00\x74\x00\x15\x00\x05\x00\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x0f\x00\x10\x00\x04\x00\x12\x00\x16\x00\x06\x00\x34\x00\x02\x00\x17\x00\x18\x00\x59\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x31\x00\x60\x00\x34\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x2e\x00\x34\x00\x31\x00\x02\x00\x34\x00\x02\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x11\x00\x16\x00\x05\x00\x34\x00\x80\x00\x53\x00\x54\x00\x55\x00\x56\x00\x33\x00\x01\x00\x59\x00\x05\x00\x03\x00\x5c\x00\x5d\x00\x5e\x00\x34\x00\x60\x00\x05\x00\x34\x00\x63\x00\x05\x00\x34\x00\x01\x00\x35\x00\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\x61\x00\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\xff\xff\xff\xff\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x3c\x00\x73\x00\x74\x00\xff\xff\xff\xff\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x0f\x00\x10\x00\xff\xff\x12\x00\xff\xff\xff\xff\xff\xff\xff\xff\x17\x00\x18\x00\xff\xff\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x03\x00\x04\x00\x60\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x43\x00\xff\xff\x18\x00\x19\x00\x1a\x00\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\xff\xff\x17\x00\x18\x00\x19\x00\x1a\x00\x80\x00\xff\xff\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x59\x00\xff\xff\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x60\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\x61\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\xff\xff\xff\xff\x38\x00\x39\x00\x80\x00\xff\xff\xff\xff\xff\xff\x73\x00\x74\x00\xff\xff\xff\xff\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x0f\x00\x10\x00\xff\xff\x12\x00\xff\xff\xff\xff\xff\xff\xff\xff\x17\x00\x18\x00\x59\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\xff\xff\x60\x00\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x18\x00\x19\x00\x1a\x00\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x01\x00\xff\xff\xff\xff\xff\xff\x80\x00\xff\xff\xff\xff\xff\xff\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\xff\xff\x13\x00\x14\x00\xff\xff\xff\xff\x17\x00\x18\x00\x19\x00\x1a\x00\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\x61\x00\xff\xff\xff\xff\xff\xff\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x73\x00\x74\x00\xff\xff\xff\xff\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x0f\x00\x10\x00\xff\xff\x12\x00\xff\xff\xff\xff\xff\xff\xff\xff\x17\x00\x18\x00\xff\xff\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x01\x00\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\xff\xff\xff\xff\xff\xff\x17\x00\x18\x00\x19\x00\x1a\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x03\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\xff\xff\xff\xff\x18\x00\x19\x00\x1a\x00\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\x61\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\xff\xff\xff\xff\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x73\x00\x74\x00\xff\xff\xff\xff\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x13\x00\x14\x00\xff\xff\x16\x00\x17\x00\xff\xff\xff\xff\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x04\x00\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\xff\xff\x18\x00\x19\x00\x1a\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x52\x00\xff\xff\xff\xff\x2a\x00\xff\xff\xff\xff\x58\x00\x59\x00\x2f\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\x61\x00\xff\xff\xff\xff\xff\xff\x34\x00\x35\x00\x36\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x3b\x00\xff\xff\x3d\x00\x3e\x00\x80\x00\x40\x00\x82\x00\x42\x00\xff\xff\xff\xff\xff\xff\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x13\x00\x14\x00\xff\xff\x16\x00\x17\x00\x58\x00\x59\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\xff\xff\x60\x00\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\xff\xff\xff\xff\xff\xff\xff\xff\x80\x00\xff\xff\x82\x00\xff\xff\x84\x00\x85\x00\x86\x00\x87\x00\x58\x00\x59\x00\x8a\x00\xff\xff\x58\x00\x59\x00\xff\xff\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\x61\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x80\x00\xff\xff\x82\x00\xff\xff\x80\x00\xff\xff\x82\x00\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x14\x00\xff\xff\x16\x00\x17\x00\xff\xff\xff\xff\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x52\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x58\x00\x59\x00\xff\xff\xff\xff\x58\x00\x59\x00\xff\xff\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x80\x00\xff\xff\x82\x00\xff\xff\x80\x00\xff\xff\x82\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x16\x00\x17\x00\xff\xff\xff\xff\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\xff\xff\xff\xff\x21\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2a\x00\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\xff\xff\x31\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x77\x00\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x18\x00\x19\x00\x1a\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\xff\xff\xff\xff\xff\xff\x2a\x00\xff\xff\xff\xff\xff\xff\xff\xff\x2f\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x5a\x00\x5b\x00\x5c\x00\x5d\x00\x5e\x00\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x37\x00\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x80\x00\x81\x00\x82\x00\x83\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\xff\xff\x4f\x00\x50\x00\x51\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x59\x00\x37\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\x64\x00\xff\xff\xff\xff\xff\xff\xff\xff\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\xff\xff\x4f\x00\x50\x00\x51\x00\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\x59\x00\xff\xff\xff\xff\xff\xff\x80\x00\xff\xff\xff\xff\x60\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x8b\x00\x8c\x00\x8d\x00\x8e\x00\x8f\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x78\x00\x79\x00\x7a\x00\x7b\x00\xff\xff\xff\xff\xff\xff\xff\xff\x80\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x8b\x00\x8c\x00\x8d\x00\x8e\x00\x8f\x00\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x6e\x01\x30\x00\x31\x00\x32\x00\x33\x00\xd4\x00\x34\x00\x73\x00\x35\x00\x36\x00\x76\x00\x37\x00\x7a\x01\x07\x01\xa0\x00\x39\x01\x38\x00\x39\x00\x7e\x01\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x2a\x01\xf5\x00\xec\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x0c\x01\x08\x01\xf8\x00\xe2\x00\x29\x01\xea\x00\x11\x00\x03\x00\x04\x00\x05\x00\x06\x00\x73\x01\x87\x00\x88\x00\xaf\x00\x0b\x01\x29\x00\x7b\x01\xae\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06\x00\xfd\x00\xe1\x00\x53\x01\xf7\x00\x01\x01\x02\x01\x75\x01\x0a\x00\x0b\x00\x1c\x00\xe2\x00\x2c\x00\x0a\x00\x0b\x00\x0d\x01\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x7c\x01\x14\x00\x55\x00\xe2\x00\x1d\x00\xaf\x00\x87\x00\x88\x00\x89\x00\x1e\x00\x7d\x01\x1f\x00\xf8\x00\xe2\x00\x74\x00\x90\x00\x74\x00\x71\x01\x77\x00\x5b\x01\x56\x00\x57\x00\x77\x00\x76\x01\x58\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x82\x00\x30\x00\x31\x00\x32\x00\x33\x00\xed\x00\x34\x00\xed\x00\x35\x00\x36\x00\x5c\x00\x37\x00\x8a\x00\xfe\x00\xff\x00\xc7\x00\x38\x00\x39\x00\x77\x01\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x2a\x00\xeb\x00\xeb\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x2a\x00\x07\x00\x08\x00\x5c\x00\x78\x01\x15\x00\x16\x00\x17\x00\x8a\x00\x8b\x00\xfb\x00\x50\x01\x79\x01\x19\x00\x07\x00\x08\x00\x6d\x01\x91\x00\x92\x00\x93\x00\x94\x00\x95\x00\x96\x00\x80\x01\x15\x00\x16\x00\x17\x00\x97\x00\x98\x00\x51\x01\xbd\xff\xbd\xff\x19\x00\x0a\x00\x0b\x00\x1c\x00\x4a\x01\x69\x01\xfc\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x72\x01\x14\x00\x55\x00\xb4\xff\xb4\xff\x4a\x01\x1d\x00\x55\x01\x15\x00\x16\x00\x17\x00\x1e\x00\xbf\xff\xbf\xff\x8d\x00\x8e\x00\x19\x00\x56\x01\x59\x01\x5a\x01\x56\x00\x57\x00\x7f\x01\x67\x01\x58\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x33\x00\x5c\x01\x34\x00\x5d\x01\x35\x00\x36\x00\x60\x01\x37\x00\x61\x01\x62\x01\x65\x01\x52\x01\x38\x00\x39\x00\x68\x01\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x42\x01\x14\x00\x63\x01\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x0a\x00\x0b\x00\x1c\x00\x64\x01\x3f\x01\x2b\x01\x15\x00\x16\x00\x17\x00\x18\x00\x2c\x01\x30\x01\x2d\x01\x2e\x01\x19\x00\x43\x01\x44\x01\x45\x01\x46\x01\x5e\x01\x2f\x01\x48\x01\x31\x01\x1e\x00\x49\x01\x53\x00\x54\x00\x32\x01\x14\x00\x36\x01\x33\x01\x4a\x01\x5f\x01\x34\x01\x35\x01\x37\x01\x38\x01\x09\x01\x3b\x01\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x3c\x01\x14\x00\x55\x00\x0a\x01\x3d\x01\x3e\x01\x27\x01\x15\x00\x16\x00\x17\x00\x18\x00\x4b\x01\x0e\x01\xf9\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xf2\x00\x56\x00\x57\x00\xf3\x00\x06\x01\x58\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x28\x01\x36\x00\xd5\x00\x37\x00\xd7\x00\xd8\x00\xd9\x00\xda\x00\x38\x00\x39\x00\xfa\x00\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x42\x01\x14\x00\xe3\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x9a\x00\x9b\x00\x9c\x00\x9d\x00\x9e\x00\x9f\x00\x15\x00\x16\x00\x17\x00\x18\x00\xa0\x00\x76\x00\xdb\x00\xdc\x00\x19\x00\x43\x01\x44\x01\x45\x01\x46\x01\x6a\x01\xdd\x00\x48\x01\xde\x00\xdf\x00\x49\x01\x53\x00\x54\x00\xe0\x00\x14\x00\xe4\x00\xe6\x00\x4a\x01\xe5\x00\xee\x00\xe7\x00\xe8\x00\xa1\x00\xa3\x00\xef\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\xa4\x00\x14\x00\x55\x00\xa5\x00\xa6\x00\xa7\x00\xa8\x00\x15\x00\x16\x00\x17\x00\x18\x00\x4b\x01\xa9\x00\xad\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xb0\x00\x56\x00\x57\x00\xbb\x00\xb1\x00\x58\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xf0\x00\x36\x00\xbc\x00\x37\x00\xd0\x00\xd1\x00\xd3\x00\x78\x00\x38\x00\x39\x00\x40\x01\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x42\x01\x14\x00\x79\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x7a\x00\x7b\x00\x7c\x00\x7d\x00\x7e\x00\x7f\x00\x15\x00\x16\x00\x17\x00\x18\x00\x80\x00\x84\x00\x85\x00\x86\x00\x19\x00\x43\x01\x44\x01\x45\x01\x46\x01\x6c\x01\x8e\x00\x48\x01\x2b\x00\x2d\x00\x49\x01\x53\x00\x54\x00\x2e\x00\x14\x00\x22\x00\x28\x00\x4a\x01\x24\x00\x25\x00\x26\x00\x27\x00\x1f\x00\x21\x00\x0b\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x0d\x00\x14\x00\x55\x00\x0e\x00\x10\x00\xa3\x00\xf5\x00\x15\x00\x16\x00\x17\x00\x18\x00\x4b\x01\x90\x00\xa3\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x24\x00\x56\x00\x57\x00\xea\x00\x90\x00\x58\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xf1\x00\x36\x00\xea\x00\x37\x00\x24\x00\xea\x00\xa3\x00\x10\x00\x38\x00\x39\x00\x4f\x01\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x42\x01\x14\x00\xa3\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\xf5\x00\x24\x00\x90\x00\x24\x00\x90\x00\xce\x00\x15\x00\x16\x00\x17\x00\x18\x00\x0d\x00\x10\x00\x24\x00\xea\x00\x19\x00\x43\x01\x44\x01\x45\x01\x46\x01\x47\x01\x10\x00\x48\x01\x24\x00\x90\x00\x49\x01\x53\x00\x54\x00\xa3\x00\x14\x00\x0d\x00\x0d\x00\x4a\x01\x24\x00\xa0\x00\x0d\x00\x76\x00\xf5\x00\x67\x00\x90\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x0d\x00\x14\x00\x55\x00\x1d\x00\xd7\x00\x76\x00\x10\x00\x15\x00\x16\x00\x17\x00\x18\x00\x4b\x01\x0d\x00\x24\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xa3\x00\x56\x00\x57\x00\xa0\x00\x24\x00\x58\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xaa\x00\x36\x00\xea\x00\x37\x00\x76\x00\xd7\x00\x0d\x00\xa3\x00\x38\x00\x39\x00\x54\x01\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x42\x01\x14\x00\x0d\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x67\x00\x0d\x00\x1f\x00\xa3\x00\x0d\x00\xa3\x00\x15\x00\x16\x00\x17\x00\x18\x00\x8d\x00\x76\x00\x24\x00\x0d\x00\x19\x00\x6b\x01\x44\x01\x45\x01\x46\x01\x84\x00\x10\x00\x48\x01\x24\x00\x90\x00\x49\x01\x53\x00\x54\x00\x0d\x00\x14\x00\x24\x00\x0d\x00\x4a\x01\x24\x00\x0d\x00\x10\x00\xff\xff\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x55\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x4b\x01\x00\x00\x00\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x02\x01\x56\x00\x57\x00\x00\x00\x00\x00\x58\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xab\x00\x36\x00\x00\x00\x37\x00\x00\x00\x00\x00\x00\x00\x00\x00\x38\x00\x39\x00\x00\x00\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x90\x00\xea\x00\x03\x01\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x04\x01\x00\x00\x0a\x00\x0b\x00\x1c\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x00\x00\x63\x00\x0a\x00\x0b\x00\x1c\x00\x19\x00\x00\x00\x4d\x01\x4e\x01\x4f\x01\x1d\x00\x64\x00\x05\x01\x00\x00\x67\x00\x1e\x00\x68\x00\x1f\x00\x69\x00\x14\x00\x1d\x00\x64\x00\x65\x00\x66\x00\x67\x00\x1e\x00\x68\x00\x1f\x00\x69\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x55\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x66\x01\x67\x01\x19\x00\x00\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x00\x00\x58\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xac\x00\x36\x00\x00\x00\x37\x00\x00\x00\x00\x00\x00\x00\x00\x00\x38\x00\x39\x00\x68\x01\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x00\x00\x14\x00\x00\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x0a\x00\x0b\x00\x1c\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x10\x00\x00\x00\x00\x00\x00\x00\x19\x00\x00\x00\x00\x00\x00\x00\x1d\x00\x64\x00\x65\x00\x66\x00\x67\x00\x1e\x00\x68\x00\x1f\x00\x69\x00\x00\x00\x61\x00\x62\x00\x00\x00\x00\x00\x63\x00\x0a\x00\x0b\x00\x1c\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x55\x00\x00\x00\x00\x00\x00\x00\x1d\x00\x64\x00\x65\x00\x66\x00\x67\x00\x1e\x00\x68\x00\x1f\x00\x69\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x00\x00\x58\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x81\x00\x36\x00\x00\x00\x37\x00\x00\x00\x00\x00\x00\x00\x00\x00\x38\x00\x39\x00\x00\x00\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x10\x00\x00\x00\x00\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x00\x00\x00\x00\x00\x00\x63\x00\x0a\x00\x0b\x00\x1c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x90\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1d\x00\x64\x00\x65\x00\x66\x00\x67\x00\x1e\x00\x68\x00\x1f\x00\x69\x00\x00\x00\x00\x00\x0a\x00\x0b\x00\x1c\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x55\x00\x4d\x01\x4e\x01\x4f\x01\x1d\x00\x64\x00\x00\x00\x00\x00\x67\x00\x1e\x00\x68\x00\x1f\x00\x69\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x56\x00\x57\x00\x00\x00\x00\x00\x58\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x6f\x01\x6a\x00\x00\x00\x6b\x00\x6c\x00\x00\x00\x00\x00\x6d\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\xea\x00\x00\x00\x00\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x00\x00\x0a\x00\x0b\x00\x1c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x23\x01\x24\x01\x25\x01\x26\x01\x27\x01\x74\x01\x00\x00\x00\x00\x1d\x00\x00\x00\x00\x00\x58\x01\x13\x00\x1e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x6e\x00\x00\x00\x00\x00\x00\x00\xbd\x00\xbe\x00\xbf\x00\x15\x00\x16\x00\x17\x00\x18\x00\xc0\x00\x00\x00\xc1\x00\xc2\x00\x19\x00\xc3\x00\x1a\x00\xc4\x00\x00\x00\x00\x00\x00\x00\x6f\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x69\x00\x6a\x00\x00\x00\x6b\x00\x6c\x00\xc5\x00\x13\x00\x6d\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x00\x00\x14\x00\x00\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x19\x00\x00\x00\x1a\x00\x00\x00\xc6\x00\xc7\x00\xc8\x00\xc9\x00\x3a\x01\x13\x00\xca\x00\x00\x00\x12\x00\x13\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x6e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x00\x00\x1a\x00\x00\x00\x19\x00\x00\x00\x1a\x00\x6f\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x72\x00\x00\x00\x6b\x00\x6c\x00\x00\x00\x00\x00\x6d\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x00\x00\x00\x00\x00\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x57\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x58\x01\x13\x00\x00\x00\x00\x00\x20\x00\x13\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x15\x00\x16\x00\x17\x00\x18\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x00\x00\x1a\x00\x00\x00\x19\x00\x00\x00\x1a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x6f\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xd2\x00\x6c\x00\x00\x00\x00\x00\x6d\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x00\x00\x00\x00\x00\x00\x3f\x00\x40\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\x0a\x00\x0b\x00\x1c\x00\xcc\x00\xcd\x00\xce\x00\xcf\x00\x00\x00\x00\x00\xd0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1d\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1e\x00\x00\x00\x1f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x6f\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x70\x00\x3b\x00\x3c\x00\x3d\x00\x3e\x00\x00\x00\x00\x00\x00\x00\x3f\x00\x71\x00\x41\x00\x42\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\x48\x00\x49\x00\x4a\x00\x4b\x00\x4c\x00\x4d\x00\x4e\x00\xb7\x00\x41\x00\xb3\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\xb4\x00\x49\x00\x4a\x00\xb5\x00\x4c\x00\x4d\x00\x4e\x00\xf6\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xb7\x00\x41\x00\xb3\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\xb4\x00\x49\x00\x4a\x00\xb5\x00\x4c\x00\x4d\x00\x4e\x00\xb8\x00\xb7\x00\x41\x00\xb3\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\xb4\x00\x49\x00\x4a\x00\xb5\x00\x4c\x00\x4d\x00\x4e\x00\xb9\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xb7\x00\x41\x00\xb3\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\xb4\x00\x49\x00\x4a\x00\xb5\x00\x4c\x00\x4d\x00\x4e\x00\xba\x00\x70\x01\x41\x00\xb3\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\xb4\x00\x49\x00\x4a\x00\xb5\x00\x4c\x00\x4d\x00\x4e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\xb2\x00\x41\x00\xb3\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\xb4\x00\x49\x00\x4a\x00\xb5\x00\x4c\x00\x4d\x00\x4e\x00\xb6\x00\x41\x00\xb3\x00\x43\x00\x44\x00\x45\x00\x46\x00\x47\x00\xb4\x00\x49\x00\x4a\x00\xb5\x00\x4c\x00\x4d\x00\x4e\x00\x0a\x00\x0b\x00\x1c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x23\x01\x24\x01\x25\x01\x26\x01\x27\x01\x00\x00\x00\x00\x00\x00\x1d\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1e\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4f\x00\x50\x00\x51\x00\x52\x00\x53\x00\x54\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x0f\x01\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x59\x00\x5a\x00\x5b\x00\x5c\x00\x19\x00\x5d\x00\x5e\x00\x5f\x00\x10\x01\x11\x01\x12\x01\x13\x01\x14\x01\x15\x01\x16\x01\x17\x01\x00\x00\x18\x01\x19\x01\x1a\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1b\x01\x0f\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x1c\x01\x00\x00\x00\x00\x00\x00\x00\x00\x41\x01\x11\x01\x12\x01\x13\x01\x14\x01\x15\x01\x16\x01\x17\x01\x00\x00\x18\x01\x19\x01\x1a\x01\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x1b\x01\x00\x00\x00\x00\x00\x00\x19\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1d\x01\x1e\x01\x1f\x01\x20\x01\x21\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x19\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1d\x01\x1e\x01\x1f\x01\x20\x01\x21\x01\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (1, 219) [
	(1 , happyReduce_1),
	(2 , happyReduce_2),
	(3 , happyReduce_3),
	(4 , happyReduce_4),
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65),
	(66 , happyReduce_66),
	(67 , happyReduce_67),
	(68 , happyReduce_68),
	(69 , happyReduce_69),
	(70 , happyReduce_70),
	(71 , happyReduce_71),
	(72 , happyReduce_72),
	(73 , happyReduce_73),
	(74 , happyReduce_74),
	(75 , happyReduce_75),
	(76 , happyReduce_76),
	(77 , happyReduce_77),
	(78 , happyReduce_78),
	(79 , happyReduce_79),
	(80 , happyReduce_80),
	(81 , happyReduce_81),
	(82 , happyReduce_82),
	(83 , happyReduce_83),
	(84 , happyReduce_84),
	(85 , happyReduce_85),
	(86 , happyReduce_86),
	(87 , happyReduce_87),
	(88 , happyReduce_88),
	(89 , happyReduce_89),
	(90 , happyReduce_90),
	(91 , happyReduce_91),
	(92 , happyReduce_92),
	(93 , happyReduce_93),
	(94 , happyReduce_94),
	(95 , happyReduce_95),
	(96 , happyReduce_96),
	(97 , happyReduce_97),
	(98 , happyReduce_98),
	(99 , happyReduce_99),
	(100 , happyReduce_100),
	(101 , happyReduce_101),
	(102 , happyReduce_102),
	(103 , happyReduce_103),
	(104 , happyReduce_104),
	(105 , happyReduce_105),
	(106 , happyReduce_106),
	(107 , happyReduce_107),
	(108 , happyReduce_108),
	(109 , happyReduce_109),
	(110 , happyReduce_110),
	(111 , happyReduce_111),
	(112 , happyReduce_112),
	(113 , happyReduce_113),
	(114 , happyReduce_114),
	(115 , happyReduce_115),
	(116 , happyReduce_116),
	(117 , happyReduce_117),
	(118 , happyReduce_118),
	(119 , happyReduce_119),
	(120 , happyReduce_120),
	(121 , happyReduce_121),
	(122 , happyReduce_122),
	(123 , happyReduce_123),
	(124 , happyReduce_124),
	(125 , happyReduce_125),
	(126 , happyReduce_126),
	(127 , happyReduce_127),
	(128 , happyReduce_128),
	(129 , happyReduce_129),
	(130 , happyReduce_130),
	(131 , happyReduce_131),
	(132 , happyReduce_132),
	(133 , happyReduce_133),
	(134 , happyReduce_134),
	(135 , happyReduce_135),
	(136 , happyReduce_136),
	(137 , happyReduce_137),
	(138 , happyReduce_138),
	(139 , happyReduce_139),
	(140 , happyReduce_140),
	(141 , happyReduce_141),
	(142 , happyReduce_142),
	(143 , happyReduce_143),
	(144 , happyReduce_144),
	(145 , happyReduce_145),
	(146 , happyReduce_146),
	(147 , happyReduce_147),
	(148 , happyReduce_148),
	(149 , happyReduce_149),
	(150 , happyReduce_150),
	(151 , happyReduce_151),
	(152 , happyReduce_152),
	(153 , happyReduce_153),
	(154 , happyReduce_154),
	(155 , happyReduce_155),
	(156 , happyReduce_156),
	(157 , happyReduce_157),
	(158 , happyReduce_158),
	(159 , happyReduce_159),
	(160 , happyReduce_160),
	(161 , happyReduce_161),
	(162 , happyReduce_162),
	(163 , happyReduce_163),
	(164 , happyReduce_164),
	(165 , happyReduce_165),
	(166 , happyReduce_166),
	(167 , happyReduce_167),
	(168 , happyReduce_168),
	(169 , happyReduce_169),
	(170 , happyReduce_170),
	(171 , happyReduce_171),
	(172 , happyReduce_172),
	(173 , happyReduce_173),
	(174 , happyReduce_174),
	(175 , happyReduce_175),
	(176 , happyReduce_176),
	(177 , happyReduce_177),
	(178 , happyReduce_178),
	(179 , happyReduce_179),
	(180 , happyReduce_180),
	(181 , happyReduce_181),
	(182 , happyReduce_182),
	(183 , happyReduce_183),
	(184 , happyReduce_184),
	(185 , happyReduce_185),
	(186 , happyReduce_186),
	(187 , happyReduce_187),
	(188 , happyReduce_188),
	(189 , happyReduce_189),
	(190 , happyReduce_190),
	(191 , happyReduce_191),
	(192 , happyReduce_192),
	(193 , happyReduce_193),
	(194 , happyReduce_194),
	(195 , happyReduce_195),
	(196 , happyReduce_196),
	(197 , happyReduce_197),
	(198 , happyReduce_198),
	(199 , happyReduce_199),
	(200 , happyReduce_200),
	(201 , happyReduce_201),
	(202 , happyReduce_202),
	(203 , happyReduce_203),
	(204 , happyReduce_204),
	(205 , happyReduce_205),
	(206 , happyReduce_206),
	(207 , happyReduce_207),
	(208 , happyReduce_208),
	(209 , happyReduce_209),
	(210 , happyReduce_210),
	(211 , happyReduce_211),
	(212 , happyReduce_212),
	(213 , happyReduce_213),
	(214 , happyReduce_214),
	(215 , happyReduce_215),
	(216 , happyReduce_216),
	(217 , happyReduce_217),
	(218 , happyReduce_218),
	(219 , happyReduce_219)
	]

happy_n_terms = 54 :: Int
happy_n_nonterms = 145 :: Int

happyReduce_1 = happySpecReduce_0  0# happyReduction_1
happyReduction_1  =  happyIn4
		 ([]
	)

happyReduce_2 = happySpecReduce_2  0# happyReduction_2
happyReduction_2 happy_x_2
	happy_x_1
	 =  case happyOut5 happy_x_1 of { happy_var_1 -> 
	case happyOut4 happy_x_2 of { happy_var_2 -> 
	happyIn4
		 (happy_var_1 : happy_var_2
	)}}

happyReduce_3 = happySpecReduce_1  1# happyReduction_3
happyReduction_3 happy_x_1
	 =  case happyOut6 happy_x_1 of { happy_var_1 -> 
	happyIn5
		 (happy_var_1
	)}

happyReduce_4 = happySpecReduce_1  2# happyReduction_4
happyReduction_4 happy_x_1
	 =  case happyOut7 happy_x_1 of { happy_var_1 -> 
	happyIn6
		 (happy_var_1
	)}

happyReduce_5 = happySpecReduce_1  2# happyReduction_5
happyReduction_5 happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	happyIn6
		 (happy_var_1
	)}

happyReduce_6 = happyReduce 10# 3# happyReduction_6
happyReduction_6 (happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut92 happy_x_3 of { happy_var_3 -> 
	case happyOut10 happy_x_5 of { happy_var_5 -> 
	case happyOut11 happy_x_7 of { happy_var_7 -> 
	case happyOut9 happy_x_8 of { happy_var_8 -> 
	happyIn7
		 (F  (readWord happy_var_3)         happy_var_5                happy_var_7           happy_var_8
	) `HappyStk` happyRest}}}}

happyReduce_7 = happyReduce 10# 4# happyReduction_7
happyReduction_7 (happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut92 happy_x_3 of { happy_var_3 -> 
	case happyOut10 happy_x_5 of { happy_var_5 -> 
	case happyOut23 happy_x_7 of { happy_var_7 -> 
	case happyOut9 happy_x_8 of { happy_var_8 -> 
	happyIn8
		 (F   (readWord happy_var_3)     happy_var_5  (univquant_free_vars happy_var_7) happy_var_8
	) `HappyStk` happyRest}}}}

happyReduce_8 = happySpecReduce_3  5# happyReduction_8
happyReduction_8 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut56 happy_x_2 of { happy_var_2 -> 
	happyIn9
		 (happy_var_2
	)}

happyReduce_9 = happySpecReduce_0  5# happyReduction_9
happyReduction_9  =  happyIn9
		 (NoSource
	)

happyReduce_10 = happySpecReduce_1  6# happyReduction_10
happyReduction_10 happy_x_1
	 =  case happyOut100 happy_x_1 of { happy_var_1 -> 
	happyIn10
		 (readRole happy_var_1
	)}

happyReduce_11 = happySpecReduce_1  7# happyReduction_11
happyReduction_11 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn11
		 (happy_var_1
	)}

happyReduce_12 = happySpecReduce_1  7# happyReduction_12
happyReduction_12 happy_x_1
	 =  case happyOut19 happy_x_1 of { happy_var_1 -> 
	happyIn11
		 (happy_var_1
	)}

happyReduce_13 = happySpecReduce_1  8# happyReduction_13
happyReduction_13 happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	happyIn12
		 (happy_var_1
	)}

happyReduce_14 = happySpecReduce_1  8# happyReduction_14
happyReduction_14 happy_x_1
	 =  case happyOut14 happy_x_1 of { happy_var_1 -> 
	happyIn12
		 (happy_var_1
	)}

happyReduce_15 = happySpecReduce_3  9# happyReduction_15
happyReduction_15 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_2 of { happy_var_2 -> 
	case happyOut19 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (BinOp happy_var_1 happy_var_2 happy_var_3
	)}}}

happyReduce_16 = happySpecReduce_1  10# happyReduction_16
happyReduction_16 happy_x_1
	 =  case happyOut15 happy_x_1 of { happy_var_1 -> 
	happyIn14
		 (happy_var_1
	)}

happyReduce_17 = happySpecReduce_1  10# happyReduction_17
happyReduction_17 happy_x_1
	 =  case happyOut17 happy_x_1 of { happy_var_1 -> 
	happyIn14
		 (happy_var_1
	)}

happyReduce_18 = happyReduce 4# 11# happyReduction_18
happyReduction_18 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut19 happy_x_3 of { happy_var_3 -> 
	case happyOut16 happy_x_4 of { happy_var_4 -> 
	happyIn15
		 (L.foldl (binOp (:|:)) (BinOp happy_var_1 (:|:) happy_var_3) happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_19 = happySpecReduce_0  12# happyReduction_19
happyReduction_19  =  happyIn16
		 ([]
	)

happyReduce_20 = happySpecReduce_3  12# happyReduction_20
happyReduction_20 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut19 happy_x_2 of { happy_var_2 -> 
	case happyOut16 happy_x_3 of { happy_var_3 -> 
	happyIn16
		 (happy_var_2 : happy_var_3
	)}}

happyReduce_21 = happyReduce 4# 13# happyReduction_21
happyReduction_21 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut19 happy_x_3 of { happy_var_3 -> 
	case happyOut18 happy_x_4 of { happy_var_4 -> 
	happyIn17
		 (L.foldl (binOp (:&:)) (BinOp happy_var_1 (:&:) happy_var_3) happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_22 = happySpecReduce_0  14# happyReduction_22
happyReduction_22  =  happyIn18
		 ([]
	)

happyReduce_23 = happySpecReduce_3  14# happyReduction_23
happyReduction_23 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut19 happy_x_2 of { happy_var_2 -> 
	case happyOut18 happy_x_3 of { happy_var_3 -> 
	happyIn18
		 (happy_var_2 : happy_var_3
	)}}

happyReduce_24 = happySpecReduce_1  15# happyReduction_24
happyReduction_24 happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	happyIn19
		 (happy_var_1
	)}

happyReduce_25 = happySpecReduce_1  15# happyReduction_25
happyReduction_25 happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	happyIn19
		 (happy_var_1
	)}

happyReduce_26 = happySpecReduce_1  15# happyReduction_26
happyReduction_26 happy_x_1
	 =  case happyOut30 happy_x_1 of { happy_var_1 -> 
	happyIn19
		 (happy_var_1
	)}

happyReduce_27 = happySpecReduce_3  15# happyReduction_27
happyReduction_27 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_2 of { happy_var_2 -> 
	happyIn19
		 (happy_var_2
	)}

happyReduce_28 = happyReduce 6# 16# happyReduction_28
happyReduction_28 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut21 happy_x_3 of { happy_var_3 -> 
	case happyOut19 happy_x_6 of { happy_var_6 -> 
	happyIn20
		 (Quant happy_var_1 happy_var_3 happy_var_6
	) `HappyStk` happyRest}}}

happyReduce_29 = happySpecReduce_1  17# happyReduction_29
happyReduction_29 happy_x_1
	 =  case happyOut53 happy_x_1 of { happy_var_1 -> 
	happyIn21
		 ([happy_var_1]
	)}

happyReduce_30 = happySpecReduce_3  17# happyReduction_30
happyReduction_30 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut53 happy_x_1 of { happy_var_1 -> 
	case happyOut21 happy_x_3 of { happy_var_3 -> 
	happyIn21
		 (happy_var_1 : happy_var_3
	)}}

happyReduce_31 = happySpecReduce_2  18# happyReduction_31
happyReduction_31 happy_x_2
	happy_x_1
	 =  case happyOut19 happy_x_2 of { happy_var_2 -> 
	happyIn22
		 ((:~:) happy_var_2
	)}

happyReduce_32 = happySpecReduce_1  18# happyReduction_32
happyReduction_32 happy_x_1
	 =  case happyOut27 happy_x_1 of { happy_var_1 -> 
	happyIn22
		 (happy_var_1
	)}

happyReduce_33 = happySpecReduce_3  19# happyReduction_33
happyReduction_33 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut24 happy_x_2 of { happy_var_2 -> 
	happyIn23
		 (happy_var_2
	)}

happyReduce_34 = happySpecReduce_1  19# happyReduction_34
happyReduction_34 happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	happyIn23
		 (happy_var_1
	)}

happyReduce_35 = happySpecReduce_2  20# happyReduction_35
happyReduction_35 happy_x_2
	happy_x_1
	 =  case happyOut26 happy_x_1 of { happy_var_1 -> 
	case happyOut25 happy_x_2 of { happy_var_2 -> 
	happyIn24
		 (L.foldl (binOp (:|:)) happy_var_1 happy_var_2
	)}}

happyReduce_36 = happySpecReduce_0  21# happyReduction_36
happyReduction_36  =  happyIn25
		 ([]
	)

happyReduce_37 = happySpecReduce_3  21# happyReduction_37
happyReduction_37 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut26 happy_x_2 of { happy_var_2 -> 
	case happyOut25 happy_x_3 of { happy_var_3 -> 
	happyIn25
		 (happy_var_2 : happy_var_3
	)}}

happyReduce_38 = happySpecReduce_1  22# happyReduction_38
happyReduction_38 happy_x_1
	 =  case happyOut30 happy_x_1 of { happy_var_1 -> 
	happyIn26
		 (happy_var_1
	)}

happyReduce_39 = happySpecReduce_2  22# happyReduction_39
happyReduction_39 happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_2 of { happy_var_2 -> 
	happyIn26
		 ((:~:) happy_var_2
	)}

happyReduce_40 = happySpecReduce_1  22# happyReduction_40
happyReduction_40 happy_x_1
	 =  case happyOut27 happy_x_1 of { happy_var_1 -> 
	happyIn26
		 (happy_var_1
	)}

happyReduce_41 = happySpecReduce_3  23# happyReduction_41
happyReduction_41 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	case happyOut37 happy_x_2 of { happy_var_2 -> 
	case happyOut39 happy_x_3 of { happy_var_3 -> 
	happyIn27
		 (InfixPred happy_var_1 happy_var_2 happy_var_3
	)}}}

happyReduce_42 = happySpecReduce_1  24# happyReduction_42
happyReduction_42 happy_x_1
	 =  happyIn28
		 (All
	)

happyReduce_43 = happySpecReduce_1  24# happyReduction_43
happyReduction_43 happy_x_1
	 =  happyIn28
		 (Exists
	)

happyReduce_44 = happySpecReduce_1  25# happyReduction_44
happyReduction_44 happy_x_1
	 =  happyIn29
		 ((:<=>:)
	)

happyReduce_45 = happySpecReduce_1  25# happyReduction_45
happyReduction_45 happy_x_1
	 =  happyIn29
		 ((:=>:)
	)

happyReduce_46 = happySpecReduce_1  25# happyReduction_46
happyReduction_46 happy_x_1
	 =  happyIn29
		 ((:<=:)
	)

happyReduce_47 = happySpecReduce_1  25# happyReduction_47
happyReduction_47 happy_x_1
	 =  happyIn29
		 ((:<~>:)
	)

happyReduce_48 = happySpecReduce_1  25# happyReduction_48
happyReduction_48 happy_x_1
	 =  happyIn29
		 ((:~|:)
	)

happyReduce_49 = happySpecReduce_1  25# happyReduction_49
happyReduction_49 happy_x_1
	 =  happyIn29
		 ((:~&:)
	)

happyReduce_50 = happySpecReduce_1  26# happyReduction_50
happyReduction_50 happy_x_1
	 =  case happyOut31 happy_x_1 of { happy_var_1 -> 
	happyIn30
		 (happy_var_1
	)}

happyReduce_51 = happySpecReduce_1  26# happyReduction_51
happyReduction_51 happy_x_1
	 =  case happyOut32 happy_x_1 of { happy_var_1 -> 
	happyIn30
		 (happy_var_1
	)}

happyReduce_52 = happySpecReduce_1  26# happyReduction_52
happyReduction_52 happy_x_1
	 =  case happyOut38 happy_x_1 of { happy_var_1 -> 
	happyIn30
		 (happy_var_1
	)}

happyReduce_53 = happySpecReduce_1  27# happyReduction_53
happyReduction_53 happy_x_1
	 =  case happyOut41 happy_x_1 of { happy_var_1 -> 
	happyIn31
		 (fApp2pApp happy_var_1
	)}

happyReduce_54 = happySpecReduce_1  28# happyReduction_54
happyReduction_54 happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 (happy_var_1
	)}

happyReduce_55 = happySpecReduce_1  28# happyReduction_55
happyReduction_55 happy_x_1
	 =  case happyOut34 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 (happy_var_1
	)}

happyReduce_56 = happySpecReduce_1  29# happyReduction_56
happyReduction_56 happy_x_1
	 =  case happyOut47 happy_x_1 of { happy_var_1 -> 
	happyIn33
		 (fApp2pApp happy_var_1
	)}

happyReduce_57 = happySpecReduce_3  30# happyReduction_57
happyReduction_57 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	case happyOut35 happy_x_2 of { happy_var_2 -> 
	case happyOut39 happy_x_3 of { happy_var_3 -> 
	happyIn34
		 (InfixPred happy_var_1 happy_var_2 happy_var_3
	)}}}

happyReduce_58 = happySpecReduce_1  31# happyReduction_58
happyReduction_58 happy_x_1
	 =  case happyOut36 happy_x_1 of { happy_var_1 -> 
	happyIn35
		 (happy_var_1
	)}

happyReduce_59 = happySpecReduce_1  32# happyReduction_59
happyReduction_59 happy_x_1
	 =  happyIn36
		 ((:=:)
	)

happyReduce_60 = happySpecReduce_1  33# happyReduction_60
happyReduction_60 happy_x_1
	 =  happyIn37
		 ((:!=:)
	)

happyReduce_61 = happySpecReduce_1  34# happyReduction_61
happyReduction_61 happy_x_1
	 =  case happyOut50 happy_x_1 of { happy_var_1 -> 
	happyIn38
		 (fApp2pApp happy_var_1
	)}

happyReduce_62 = happySpecReduce_1  35# happyReduction_62
happyReduction_62 happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (happy_var_1
	)}

happyReduce_63 = happySpecReduce_1  35# happyReduction_63
happyReduction_63 happy_x_1
	 =  case happyOut53 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (Var happy_var_1
	)}

happyReduce_64 = happySpecReduce_1  36# happyReduction_64
happyReduction_64 happy_x_1
	 =  case happyOut41 happy_x_1 of { happy_var_1 -> 
	happyIn40
		 (happy_var_1
	)}

happyReduce_65 = happySpecReduce_1  36# happyReduction_65
happyReduction_65 happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	happyIn40
		 (happy_var_1
	)}

happyReduce_66 = happySpecReduce_1  36# happyReduction_66
happyReduction_66 happy_x_1
	 =  case happyOut50 happy_x_1 of { happy_var_1 -> 
	happyIn40
		 (happy_var_1
	)}

happyReduce_67 = happySpecReduce_1  37# happyReduction_67
happyReduction_67 happy_x_1
	 =  case happyOut42 happy_x_1 of { happy_var_1 -> 
	happyIn41
		 (FunApp happy_var_1 []
	)}

happyReduce_68 = happyReduce 4# 37# happyReduction_68
happyReduction_68 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut43 happy_x_1 of { happy_var_1 -> 
	case happyOut54 happy_x_3 of { happy_var_3 -> 
	happyIn41
		 (FunApp happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_69 = happySpecReduce_1  38# happyReduction_69
happyReduction_69 happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	happyIn42
		 (happy_var_1
	)}

happyReduce_70 = happySpecReduce_1  39# happyReduction_70
happyReduction_70 happy_x_1
	 =  case happyOut93 happy_x_1 of { happy_var_1 -> 
	happyIn43
		 (happy_var_1
	)}

happyReduce_71 = happySpecReduce_1  40# happyReduction_71
happyReduction_71 happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	happyIn44
		 (happy_var_1
	)}

happyReduce_72 = happySpecReduce_1  40# happyReduction_72
happyReduction_72 happy_x_1
	 =  case happyOut46 happy_x_1 of { happy_var_1 -> 
	happyIn44
		 (happy_var_1
	)}

happyReduce_73 = happySpecReduce_1  41# happyReduction_73
happyReduction_73 happy_x_1
	 =  case happyOut96 happy_x_1 of { happy_var_1 -> 
	happyIn45
		 (NumberLitTerm happy_var_1
	)}

happyReduce_74 = happySpecReduce_1  41# happyReduction_74
happyReduction_74 happy_x_1
	 =  case happyOut128 happy_x_1 of { happy_var_1 -> 
	happyIn45
		 (DistinctObjectTerm (stripQuotes '"' happy_var_1)
	)}

happyReduce_75 = happySpecReduce_1  42# happyReduction_75
happyReduction_75 happy_x_1
	 =  case happyOut47 happy_x_1 of { happy_var_1 -> 
	happyIn46
		 (happy_var_1
	)}

happyReduce_76 = happySpecReduce_1  43# happyReduction_76
happyReduction_76 happy_x_1
	 =  case happyOut48 happy_x_1 of { happy_var_1 -> 
	happyIn47
		 (FunApp (AtomicWord happy_var_1) []
	)}

happyReduce_77 = happyReduce 4# 43# happyReduction_77
happyReduction_77 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut49 happy_x_1 of { happy_var_1 -> 
	case happyOut54 happy_x_3 of { happy_var_3 -> 
	happyIn47
		 (FunApp (AtomicWord happy_var_1) happy_var_3
	) `HappyStk` happyRest}}

happyReduce_78 = happySpecReduce_1  44# happyReduction_78
happyReduction_78 happy_x_1
	 =  case happyOut49 happy_x_1 of { happy_var_1 -> 
	happyIn48
		 (happy_var_1
	)}

happyReduce_79 = happySpecReduce_1  45# happyReduction_79
happyReduction_79 happy_x_1
	 =  case happyOut94 happy_x_1 of { happy_var_1 -> 
	happyIn49
		 (happy_var_1
	)}

happyReduce_80 = happySpecReduce_1  46# happyReduction_80
happyReduction_80 happy_x_1
	 =  case happyOut51 happy_x_1 of { happy_var_1 -> 
	happyIn50
		 (FunApp (AtomicWord happy_var_1) []
	)}

happyReduce_81 = happyReduce 4# 46# happyReduction_81
happyReduction_81 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut52 happy_x_1 of { happy_var_1 -> 
	case happyOut54 happy_x_3 of { happy_var_3 -> 
	happyIn50
		 (FunApp (AtomicWord happy_var_1) happy_var_3
	) `HappyStk` happyRest}}

happyReduce_82 = happySpecReduce_1  47# happyReduction_82
happyReduction_82 happy_x_1
	 =  case happyOut52 happy_x_1 of { happy_var_1 -> 
	happyIn51
		 (happy_var_1
	)}

happyReduce_83 = happySpecReduce_1  48# happyReduction_83
happyReduction_83 happy_x_1
	 =  case happyOut95 happy_x_1 of { happy_var_1 -> 
	happyIn52
		 (happy_var_1
	)}

happyReduce_84 = happySpecReduce_1  49# happyReduction_84
happyReduction_84 happy_x_1
	 =  case happyOut131 happy_x_1 of { happy_var_1 -> 
	happyIn53
		 (V happy_var_1
	)}

happyReduce_85 = happySpecReduce_1  50# happyReduction_85
happyReduction_85 happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	happyIn54
		 ([happy_var_1]
	)}

happyReduce_86 = happySpecReduce_3  50# happyReduction_86
happyReduction_86 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	case happyOut54 happy_x_3 of { happy_var_3 -> 
	happyIn54
		 (happy_var_1 : happy_var_3
	)}}

happyReduce_87 = happySpecReduce_1  51# happyReduction_87
happyReduction_87 happy_x_1
	 =  case happyOut87 happy_x_1 of { happy_var_1 -> 
	happyIn55
		 (happy_var_1
	)}

happyReduce_88 = happySpecReduce_1  52# happyReduction_88
happyReduction_88 happy_x_1
	 =  case happyOut57 happy_x_1 of { happy_var_1 -> 
	happyIn56
		 (happy_var_1
	)}

happyReduce_89 = happySpecReduce_1  52# happyReduction_89
happyReduction_89 happy_x_1
	 =  case happyOut63 happy_x_1 of { happy_var_1 -> 
	happyIn56
		 (happy_var_1
	)}

happyReduce_90 = happySpecReduce_1  52# happyReduction_90
happyReduction_90 happy_x_1
	 =  case happyOut65 happy_x_1 of { happy_var_1 -> 
	happyIn56
		 (happy_var_1
	)}

happyReduce_91 = happySpecReduce_1  53# happyReduction_91
happyReduction_91 happy_x_1
	 =  case happyOut92 happy_x_1 of { happy_var_1 -> 
	happyIn57
		 (Name (readWord happy_var_1)
	)}

happyReduce_92 = happySpecReduce_1  53# happyReduction_92
happyReduction_92 happy_x_1
	 =  case happyOut58 happy_x_1 of { happy_var_1 -> 
	happyIn57
		 (happy_var_1
	)}

happyReduce_93 = happyReduce 10# 54# happyReduction_93
happyReduction_93 (happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut59 happy_x_3 of { happy_var_3 -> 
	case happyOut73 happy_x_5 of { happy_var_5 -> 
	case happyOut60 happy_x_8 of { happy_var_8 -> 
	happyIn58
		 (Inference happy_var_3 happy_var_5 happy_var_8
	) `HappyStk` happyRest}}}

happyReduce_94 = happySpecReduce_1  55# happyReduction_94
happyReduction_94 happy_x_1
	 =  case happyOut93 happy_x_1 of { happy_var_1 -> 
	happyIn59
		 (readRule $ readWord happy_var_1
	)}

happyReduce_95 = happySpecReduce_1  56# happyReduction_95
happyReduction_95 happy_x_1
	 =  case happyOut61 happy_x_1 of { happy_var_1 -> 
	happyIn60
		 ([happy_var_1]
	)}

happyReduce_96 = happySpecReduce_3  56# happyReduction_96
happyReduction_96 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut61 happy_x_1 of { happy_var_1 -> 
	case happyOut60 happy_x_3 of { happy_var_3 -> 
	happyIn60
		 (happy_var_1 : happy_var_3
	)}}

happyReduce_97 = happySpecReduce_2  57# happyReduction_97
happyReduction_97 happy_x_2
	happy_x_1
	 =  case happyOut93 happy_x_1 of { happy_var_1 -> 
	case happyOut62 happy_x_2 of { happy_var_2 -> 
	happyIn61
		 (Parent (readWord happy_var_1) happy_var_2
	)}}

happyReduce_98 = happySpecReduce_2  58# happyReduction_98
happyReduction_98 happy_x_2
	happy_x_1
	 =  case happyOut90 happy_x_2 of { happy_var_2 -> 
	happyIn62
		 (happy_var_2
	)}

happyReduce_99 = happySpecReduce_0  58# happyReduction_99
happyReduction_99  =  happyIn62
		 ([]
	)

happyReduce_100 = happyReduce 5# 59# happyReduction_100
happyReduction_100 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut64 happy_x_3 of { happy_var_3 -> 
	case happyOut72 happy_x_4 of { happy_var_4 -> 
	happyIn63
		 (Introduced happy_var_3 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_101 = happySpecReduce_1  60# happyReduction_101
happyReduction_101 happy_x_1
	 =  case happyOut100 happy_x_1 of { happy_var_1 -> 
	happyIn64
		 (readType happy_var_1
	)}

happyReduce_102 = happySpecReduce_1  61# happyReduction_102
happyReduction_102 happy_x_1
	 =  case happyOut66 happy_x_1 of { happy_var_1 -> 
	happyIn65
		 (happy_var_1
	)}

happyReduce_103 = happySpecReduce_1  61# happyReduction_103
happyReduction_103 happy_x_1
	 =  case happyOut68 happy_x_1 of { happy_var_1 -> 
	happyIn65
		 (happy_var_1
	)}

happyReduce_104 = happySpecReduce_1  61# happyReduction_104
happyReduction_104 happy_x_1
	 =  case happyOut70 happy_x_1 of { happy_var_1 -> 
	happyIn65
		 (happy_var_1
	)}

happyReduce_105 = happyReduce 5# 62# happyReduction_105
happyReduction_105 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut99 happy_x_3 of { happy_var_3 -> 
	case happyOut67 happy_x_4 of { happy_var_4 -> 
	happyIn66
		 (File    happy_var_3        happy_var_4
	) `HappyStk` happyRest}}

happyReduce_106 = happySpecReduce_2  63# happyReduction_106
happyReduction_106 happy_x_2
	happy_x_1
	 =  case happyOut92 happy_x_2 of { happy_var_2 -> 
	happyIn67
		 (Just (readWord happy_var_2)
	)}

happyReduce_107 = happySpecReduce_0  63# happyReduction_107
happyReduction_107  =  happyIn67
		 (Nothing
	)

happyReduce_108 = happyReduce 5# 64# happyReduction_108
happyReduction_108 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut69 happy_x_3 of { happy_var_3 -> 
	case happyOut72 happy_x_4 of { happy_var_4 -> 
	happyIn68
		 (Theory    happy_var_3          happy_var_4
	) `HappyStk` happyRest}}

happyReduce_109 = happySpecReduce_1  65# happyReduction_109
happyReduction_109 happy_x_1
	 =  happyIn69
		 (Equality
	)

happyReduce_110 = happySpecReduce_1  65# happyReduction_110
happyReduction_110 happy_x_1
	 =  happyIn69
		 (AC
	)

happyReduce_111 = happyReduce 5# 66# happyReduction_111
happyReduction_111 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut71 happy_x_3 of { happy_var_3 -> 
	case happyOut72 happy_x_4 of { happy_var_4 -> 
	happyIn70
		 (Creator happy_var_3 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_112 = happySpecReduce_1  67# happyReduction_112
happyReduction_112 happy_x_1
	 =  case happyOut93 happy_x_1 of { happy_var_1 -> 
	happyIn71
		 (readWord happy_var_1
	)}

happyReduce_113 = happySpecReduce_2  68# happyReduction_113
happyReduction_113 happy_x_2
	happy_x_1
	 =  case happyOut73 happy_x_2 of { happy_var_2 -> 
	happyIn72
		 (happy_var_2
	)}

happyReduce_114 = happySpecReduce_0  68# happyReduction_114
happyReduction_114  =  happyIn72
		 ([]
	)

happyReduce_115 = happySpecReduce_2  69# happyReduction_115
happyReduction_115 happy_x_2
	happy_x_1
	 =  happyIn73
		 ([]
	)

happyReduce_116 = happySpecReduce_3  69# happyReduction_116
happyReduction_116 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut74 happy_x_2 of { happy_var_2 -> 
	happyIn73
		 (happy_var_2
	)}

happyReduce_117 = happySpecReduce_1  70# happyReduction_117
happyReduction_117 happy_x_1
	 =  case happyOut75 happy_x_1 of { happy_var_1 -> 
	happyIn74
		 ([happy_var_1]
	)}

happyReduce_118 = happySpecReduce_3  70# happyReduction_118
happyReduction_118 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut75 happy_x_1 of { happy_var_1 -> 
	case happyOut74 happy_x_3 of { happy_var_3 -> 
	happyIn74
		 (happy_var_1 : happy_var_3
	)}}

happyReduce_119 = happySpecReduce_1  71# happyReduction_119
happyReduction_119 happy_x_1
	 =  case happyOut77 happy_x_1 of { happy_var_1 -> 
	happyIn75
		 (happy_var_1
	)}

happyReduce_120 = happySpecReduce_1  71# happyReduction_120
happyReduction_120 happy_x_1
	 =  case happyOut80 happy_x_1 of { happy_var_1 -> 
	happyIn75
		 (happy_var_1
	)}

happyReduce_121 = happySpecReduce_1  71# happyReduction_121
happyReduction_121 happy_x_1
	 =  case happyOut76 happy_x_1 of { happy_var_1 -> 
	happyIn75
		 (happy_var_1
	)}

happyReduce_122 = happyReduce 4# 72# happyReduction_122
happyReduction_122 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut93 happy_x_1 of { happy_var_1 -> 
	case happyOut91 happy_x_3 of { happy_var_3 -> 
	happyIn76
		 (Function (readWord happy_var_1) happy_var_3
	) `HappyStk` happyRest}}

happyReduce_123 = happySpecReduce_1  73# happyReduction_123
happyReduction_123 happy_x_1
	 =  case happyOut78 happy_x_1 of { happy_var_1 -> 
	happyIn77
		 (happy_var_1
	)}

happyReduce_124 = happySpecReduce_1  73# happyReduction_124
happyReduction_124 happy_x_1
	 =  case happyOut79 happy_x_1 of { happy_var_1 -> 
	happyIn77
		 (happy_var_1
	)}

happyReduce_125 = happyReduce 4# 74# happyReduction_125
happyReduction_125 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut93 happy_x_3 of { happy_var_3 -> 
	happyIn78
		 (Description $ readWord happy_var_3
	) `HappyStk` happyRest}

happyReduce_126 = happyReduce 4# 75# happyReduction_126
happyReduction_126 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut93 happy_x_3 of { happy_var_3 -> 
	happyIn79
		 (IQuote $ readWord happy_var_3
	) `HappyStk` happyRest}

happyReduce_127 = happySpecReduce_1  76# happyReduction_127
happyReduction_127 happy_x_1
	 =  case happyOut81 happy_x_1 of { happy_var_1 -> 
	happyIn80
		 (happy_var_1
	)}

happyReduce_128 = happySpecReduce_1  76# happyReduction_128
happyReduction_128 happy_x_1
	 =  case happyOut84 happy_x_1 of { happy_var_1 -> 
	happyIn80
		 (happy_var_1
	)}

happyReduce_129 = happySpecReduce_1  76# happyReduction_129
happyReduction_129 happy_x_1
	 =  case happyOut85 happy_x_1 of { happy_var_1 -> 
	happyIn80
		 (happy_var_1
	)}

happyReduce_130 = happyReduce 4# 77# happyReduction_130
happyReduction_130 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut82 happy_x_3 of { happy_var_3 -> 
	happyIn81
		 (Status happy_var_3
	) `HappyStk` happyRest}

happyReduce_131 = happySpecReduce_1  77# happyReduction_131
happyReduction_131 happy_x_1
	 =  case happyOut83 happy_x_1 of { happy_var_1 -> 
	happyIn81
		 (happy_var_1
	)}

happyReduce_132 = happySpecReduce_1  78# happyReduction_132
happyReduction_132 happy_x_1
	 =  case happyOut100 happy_x_1 of { happy_var_1 -> 
	happyIn82
		 (readStatus happy_var_1
	)}

happyReduce_133 = happyReduce 6# 79# happyReduction_133
happyReduction_133 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut59 happy_x_1 of { happy_var_1 -> 
	case happyOut93 happy_x_3 of { happy_var_3 -> 
	case happyOut90 happy_x_5 of { happy_var_5 -> 
	happyIn83
		 (InferenceInfo happy_var_1 ( readWord happy_var_3) happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_134 = happyReduce 6# 80# happyReduction_134
happyReduction_134 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut86 happy_x_4 of { happy_var_4 -> 
	happyIn84
		 (AssumptionR (L.map readWord happy_var_4)
	) `HappyStk` happyRest}

happyReduce_135 = happyReduce 4# 81# happyReduction_135
happyReduction_135 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut66 happy_x_3 of { happy_var_3 -> 
	happyIn85
		 (Refutation happy_var_3
	) `HappyStk` happyRest}

happyReduce_136 = happySpecReduce_1  82# happyReduction_136
happyReduction_136 happy_x_1
	 =  case happyOut92 happy_x_1 of { happy_var_1 -> 
	happyIn86
		 ([happy_var_1]
	)}

happyReduce_137 = happySpecReduce_3  82# happyReduction_137
happyReduction_137 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut92 happy_x_1 of { happy_var_1 -> 
	case happyOut86 happy_x_3 of { happy_var_3 -> 
	happyIn86
		 (happy_var_1 : happy_var_3
	)}}

happyReduce_138 = happySpecReduce_1  83# happyReduction_138
happyReduction_138 happy_x_1
	 =  case happyOut88 happy_x_1 of { happy_var_1 -> 
	happyIn87
		 (GTerm happy_var_1
	)}

happyReduce_139 = happySpecReduce_3  83# happyReduction_139
happyReduction_139 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut88 happy_x_1 of { happy_var_1 -> 
	case happyOut87 happy_x_3 of { happy_var_3 -> 
	happyIn87
		 (ColonSep happy_var_1 happy_var_3
	)}}

happyReduce_140 = happySpecReduce_1  83# happyReduction_140
happyReduction_140 happy_x_1
	 =  case happyOut90 happy_x_1 of { happy_var_1 -> 
	happyIn87
		 (GList happy_var_1
	)}

happyReduce_141 = happySpecReduce_1  84# happyReduction_141
happyReduction_141 happy_x_1
	 =  case happyOut93 happy_x_1 of { happy_var_1 -> 
	happyIn88
		 (GWord happy_var_1
	)}

happyReduce_142 = happySpecReduce_1  84# happyReduction_142
happyReduction_142 happy_x_1
	 =  case happyOut89 happy_x_1 of { happy_var_1 -> 
	happyIn88
		 (happy_var_1
	)}

happyReduce_143 = happyReduce 4# 84# happyReduction_143
happyReduction_143 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut93 happy_x_1 of { happy_var_1 -> 
	case happyOut91 happy_x_3 of { happy_var_3 -> 
	happyIn88
		 (GApp happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_144 = happySpecReduce_1  84# happyReduction_144
happyReduction_144 happy_x_1
	 =  case happyOut53 happy_x_1 of { happy_var_1 -> 
	happyIn88
		 (GVar happy_var_1
	)}

happyReduce_145 = happySpecReduce_1  84# happyReduction_145
happyReduction_145 happy_x_1
	 =  case happyOut96 happy_x_1 of { happy_var_1 -> 
	happyIn88
		 (GNumber happy_var_1
	)}

happyReduce_146 = happySpecReduce_1  84# happyReduction_146
happyReduction_146 happy_x_1
	 =  case happyOut128 happy_x_1 of { happy_var_1 -> 
	happyIn88
		 (GDistinctObject (stripQuotes '"' happy_var_1)
	)}

happyReduce_147 = happyReduce 4# 85# happyReduction_147
happyReduction_147 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut11 happy_x_3 of { happy_var_3 -> 
	happyIn89
		 (GFormulaData "$fof" happy_var_3
	) `HappyStk` happyRest}

happyReduce_148 = happyReduce 4# 85# happyReduction_148
happyReduction_148 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut23 happy_x_3 of { happy_var_3 -> 
	happyIn89
		 (GFormulaData "$cnf" happy_var_3
	) `HappyStk` happyRest}

happyReduce_149 = happyReduce 4# 85# happyReduction_149
happyReduction_149 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut39 happy_x_3 of { happy_var_3 -> 
	happyIn89
		 (GFormulaTerm "$fot" happy_var_3
	) `HappyStk` happyRest}

happyReduce_150 = happySpecReduce_2  86# happyReduction_150
happyReduction_150 happy_x_2
	happy_x_1
	 =  happyIn90
		 ([]
	)

happyReduce_151 = happySpecReduce_3  86# happyReduction_151
happyReduction_151 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut91 happy_x_2 of { happy_var_2 -> 
	happyIn90
		 (happy_var_2
	)}

happyReduce_152 = happySpecReduce_1  87# happyReduction_152
happyReduction_152 happy_x_1
	 =  case happyOut87 happy_x_1 of { happy_var_1 -> 
	happyIn91
		 ([happy_var_1]
	)}

happyReduce_153 = happySpecReduce_3  87# happyReduction_153
happyReduction_153 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut87 happy_x_1 of { happy_var_1 -> 
	case happyOut91 happy_x_3 of { happy_var_3 -> 
	happyIn91
		 (happy_var_1 : happy_var_3
	)}}

happyReduce_154 = happySpecReduce_1  88# happyReduction_154
happyReduction_154 happy_x_1
	 =  case happyOut93 happy_x_1 of { happy_var_1 -> 
	happyIn92
		 (happy_var_1
	)}

happyReduce_155 = happySpecReduce_1  88# happyReduction_155
happyReduction_155 happy_x_1
	 =  case happyOut134 happy_x_1 of { happy_var_1 -> 
	happyIn92
		 (AtomicWord(show happy_var_1)
	)}

happyReduce_156 = happySpecReduce_1  89# happyReduction_156
happyReduction_156 happy_x_1
	 =  case happyOut100 happy_x_1 of { happy_var_1 -> 
	happyIn93
		 (AtomicWord happy_var_1
	)}

happyReduce_157 = happySpecReduce_1  89# happyReduction_157
happyReduction_157 happy_x_1
	 =  case happyOut127 happy_x_1 of { happy_var_1 -> 
	happyIn93
		 (AtomicWord (stripQuotes '\'' happy_var_1)
	)}

happyReduce_158 = happySpecReduce_1  90# happyReduction_158
happyReduction_158 happy_x_1
	 =  case happyOut129 happy_x_1 of { happy_var_1 -> 
	happyIn94
		 (happy_var_1
	)}

happyReduce_159 = happySpecReduce_1  91# happyReduction_159
happyReduction_159 happy_x_1
	 =  case happyOut130 happy_x_1 of { happy_var_1 -> 
	happyIn95
		 (happy_var_1
	)}

happyReduce_160 = happySpecReduce_1  92# happyReduction_160
happyReduction_160 happy_x_1
	 =  case happyOut97 happy_x_1 of { happy_var_1 -> 
	happyIn96
		 (fromIntegral happy_var_1
	)}

happyReduce_161 = happySpecReduce_1  92# happyReduction_161
happyReduction_161 happy_x_1
	 =  case happyOut98 happy_x_1 of { happy_var_1 -> 
	happyIn96
		 (happy_var_1
	)}

happyReduce_162 = happySpecReduce_1  92# happyReduction_162
happyReduction_162 happy_x_1
	 =  case happyOut135 happy_x_1 of { happy_var_1 -> 
	happyIn96
		 (happy_var_1
	)}

happyReduce_163 = happySpecReduce_1  93# happyReduction_163
happyReduction_163 happy_x_1
	 =  case happyOut133 happy_x_1 of { happy_var_1 -> 
	happyIn97
		 (happy_var_1
	)}

happyReduce_164 = happySpecReduce_1  93# happyReduction_164
happyReduction_164 happy_x_1
	 =  case happyOut134 happy_x_1 of { happy_var_1 -> 
	happyIn97
		 (happy_var_1
	)}

happyReduce_165 = happySpecReduce_3  94# happyReduction_165
happyReduction_165 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut97 happy_x_1 of { happy_var_1 -> 
	case happyOut134 happy_x_3 of { happy_var_3 -> 
	happyIn98
		 (happy_var_1 % happy_var_3
	)}}

happyReduce_166 = happySpecReduce_1  95# happyReduction_166
happyReduction_166 happy_x_1
	 =  case happyOut127 happy_x_1 of { happy_var_1 -> 
	happyIn99
		 (stripQuotes '\'' happy_var_1
	)}

happyReduce_167 = happySpecReduce_1  96# happyReduction_167
happyReduction_167 happy_x_1
	 =  case happyOut132 happy_x_1 of { happy_var_1 -> 
	happyIn100
		 (happy_var_1
	)}

happyReduce_168 = happySpecReduce_1  96# happyReduction_168
happyReduction_168 happy_x_1
	 =  happyIn100
		 ("fof"
	)

happyReduce_169 = happySpecReduce_1  96# happyReduction_169
happyReduction_169 happy_x_1
	 =  happyIn100
		 ("cnf"
	)

happyReduce_170 = happySpecReduce_1  96# happyReduction_170
happyReduction_170 happy_x_1
	 =  happyIn100
		 ("include"
	)

happyReduce_171 = happySpecReduce_2  97# happyReduction_171
happyReduction_171 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn101
		 (happy_var_1
	)}

happyReduce_172 = happySpecReduce_2  98# happyReduction_172
happyReduction_172 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn102
		 (happy_var_1
	)}

happyReduce_173 = happySpecReduce_2  99# happyReduction_173
happyReduction_173 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn103
		 (happy_var_1
	)}

happyReduce_174 = happySpecReduce_2  100# happyReduction_174
happyReduction_174 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn104
		 (happy_var_1
	)}

happyReduce_175 = happySpecReduce_2  101# happyReduction_175
happyReduction_175 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn105
		 (happy_var_1
	)}

happyReduce_176 = happySpecReduce_2  102# happyReduction_176
happyReduction_176 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn106
		 (happy_var_1
	)}

happyReduce_177 = happySpecReduce_2  103# happyReduction_177
happyReduction_177 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn107
		 (happy_var_1
	)}

happyReduce_178 = happySpecReduce_2  104# happyReduction_178
happyReduction_178 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn108
		 (happy_var_1
	)}

happyReduce_179 = happySpecReduce_2  105# happyReduction_179
happyReduction_179 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn109
		 (happy_var_1
	)}

happyReduce_180 = happySpecReduce_2  106# happyReduction_180
happyReduction_180 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn110
		 (happy_var_1
	)}

happyReduce_181 = happySpecReduce_2  107# happyReduction_181
happyReduction_181 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn111
		 (happy_var_1
	)}

happyReduce_182 = happySpecReduce_2  108# happyReduction_182
happyReduction_182 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn112
		 (happy_var_1
	)}

happyReduce_183 = happySpecReduce_2  109# happyReduction_183
happyReduction_183 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn113
		 (happy_var_1
	)}

happyReduce_184 = happySpecReduce_2  110# happyReduction_184
happyReduction_184 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn114
		 (happy_var_1
	)}

happyReduce_185 = happySpecReduce_2  111# happyReduction_185
happyReduction_185 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn115
		 (happy_var_1
	)}

happyReduce_186 = happySpecReduce_2  112# happyReduction_186
happyReduction_186 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn116
		 (happy_var_1
	)}

happyReduce_187 = happySpecReduce_2  113# happyReduction_187
happyReduction_187 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn117
		 (happy_var_1
	)}

happyReduce_188 = happySpecReduce_2  114# happyReduction_188
happyReduction_188 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn118
		 (happy_var_1
	)}

happyReduce_189 = happySpecReduce_2  115# happyReduction_189
happyReduction_189 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn119
		 (happy_var_1
	)}

happyReduce_190 = happySpecReduce_2  116# happyReduction_190
happyReduction_190 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn120
		 (happy_var_1
	)}

happyReduce_191 = happySpecReduce_2  117# happyReduction_191
happyReduction_191 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn121
		 (happy_var_1
	)}

happyReduce_192 = happySpecReduce_2  118# happyReduction_192
happyReduction_192 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn122
		 (happy_var_1
	)}

happyReduce_193 = happySpecReduce_2  119# happyReduction_193
happyReduction_193 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn123
		 (happy_var_1
	)}

happyReduce_194 = happySpecReduce_2  120# happyReduction_194
happyReduction_194 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn124
		 (happy_var_1
	)}

happyReduce_195 = happySpecReduce_2  121# happyReduction_195
happyReduction_195 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn125
		 (happy_var_1
	)}

happyReduce_196 = happySpecReduce_2  122# happyReduction_196
happyReduction_196 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn126
		 (happy_var_1
	)}

happyReduce_197 = happySpecReduce_2  123# happyReduction_197
happyReduction_197 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (SingleQuoted happy_var_1) -> 
	happyIn127
		 (happy_var_1
	)}

happyReduce_198 = happySpecReduce_2  124# happyReduction_198
happyReduction_198 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (DoubleQuoted happy_var_1) -> 
	happyIn128
		 (happy_var_1
	)}

happyReduce_199 = happySpecReduce_2  125# happyReduction_199
happyReduction_199 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (DollarWord happy_var_1) -> 
	happyIn129
		 (happy_var_1
	)}

happyReduce_200 = happySpecReduce_2  126# happyReduction_200
happyReduction_200 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (DollarDollarWord happy_var_1) -> 
	happyIn130
		 (happy_var_1
	)}

happyReduce_201 = happySpecReduce_2  127# happyReduction_201
happyReduction_201 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (UpperWord happy_var_1) -> 
	happyIn131
		 (happy_var_1
	)}

happyReduce_202 = happySpecReduce_2  128# happyReduction_202
happyReduction_202 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (LowerWord happy_var_1) -> 
	happyIn132
		 (happy_var_1
	)}

happyReduce_203 = happySpecReduce_2  129# happyReduction_203
happyReduction_203 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (SignedInt happy_var_1) -> 
	happyIn133
		 (happy_var_1
	)}

happyReduce_204 = happySpecReduce_2  130# happyReduction_204
happyReduction_204 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (UnsignedInt happy_var_1) -> 
	happyIn134
		 (happy_var_1
	)}

happyReduce_205 = happySpecReduce_2  131# happyReduction_205
happyReduction_205 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (Real happy_var_1) -> 
	happyIn135
		 (happy_var_1
	)}

happyReduce_206 = happySpecReduce_2  132# happyReduction_206
happyReduction_206 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn136
		 (happy_var_1
	)}

happyReduce_207 = happySpecReduce_2  133# happyReduction_207
happyReduction_207 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn137
		 (happy_var_1
	)}

happyReduce_208 = happySpecReduce_2  134# happyReduction_208
happyReduction_208 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn138
		 (happy_var_1
	)}

happyReduce_209 = happySpecReduce_2  135# happyReduction_209
happyReduction_209 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn139
		 (happy_var_1
	)}

happyReduce_210 = happySpecReduce_2  136# happyReduction_210
happyReduction_210 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn140
		 (happy_var_1
	)}

happyReduce_211 = happySpecReduce_2  137# happyReduction_211
happyReduction_211 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn141
		 (happy_var_1
	)}

happyReduce_212 = happySpecReduce_2  138# happyReduction_212
happyReduction_212 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn142
		 (happy_var_1
	)}

happyReduce_213 = happySpecReduce_2  139# happyReduction_213
happyReduction_213 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn143
		 (happy_var_1
	)}

happyReduce_214 = happySpecReduce_2  140# happyReduction_214
happyReduction_214 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn144
		 (happy_var_1
	)}

happyReduce_215 = happySpecReduce_2  141# happyReduction_215
happyReduction_215 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn145
		 (happy_var_1
	)}

happyReduce_216 = happySpecReduce_2  142# happyReduction_216
happyReduction_216 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn146
		 (happy_var_1
	)}

happyReduce_217 = happySpecReduce_2  143# happyReduction_217
happyReduction_217 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn147
		 (happy_var_1
	)}

happyReduce_218 = happySpecReduce_0  144# happyReduction_218
happyReduction_218  =  happyIn148
		 ([]
	)

happyReduce_219 = happySpecReduce_2  144# happyReduction_219
happyReduction_219 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (CommentToken happy_var_1) -> 
	case happyOut148 happy_x_2 of { happy_var_2 -> 
	happyIn148
		 (happy_var_1 : happy_var_2
	)}}

happyNewToken action sts stk [] =
	happyDoAction 53# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	LP -> cont 1#;
	RP -> cont 2#;
	Lbrack -> cont 3#;
	Rbrack -> cont 4#;
	Comma -> cont 5#;
	Dot -> cont 6#;
	Star -> cont 7#;
	Plus -> cont 8#;
	Rangle -> cont 9#;
	Oper ":" -> cont 10#;
	Oper "<=>" -> cont 11#;
	Oper "=>" -> cont 12#;
	Oper "<~>" -> cont 13#;
	Oper "~|" -> cont 14#;
	Oper "~&" -> cont 15#;
	Oper "<=" -> cont 16#;
	Oper "=" -> cont 17#;
	Oper "!=" -> cont 18#;
	Oper "!" -> cont 19#;
	Oper "?" -> cont 20#;
	Oper "&" -> cont 21#;
	Oper "|" -> cont 22#;
	Oper "~" -> cont 23#;
	LowerWord "fof" -> cont 24#;
	LowerWord "cnf" -> cont 25#;
	LowerWord "include" -> cont 26#;
	LowerWord "inference" -> cont 27#;
	LowerWord "introduced" -> cont 28#;
	LowerWord "file" -> cont 29#;
	LowerWord "theory" -> cont 30#;
	LowerWord "ac" -> cont 31#;
	LowerWord "equality" -> cont 32#;
	LowerWord "creator" -> cont 33#;
	LowerWord "iquote" -> cont 34#;
	LowerWord "status" -> cont 35#;
	LowerWord "assumptions" -> cont 36#;
	LowerWord "refutation" -> cont 37#;
	LowerWord "description" -> cont 38#;
	DollarWord "$fof" -> cont 39#;
	DollarWord "$cnf" -> cont 40#;
	DollarWord "$fot" -> cont 41#;
	SingleQuoted happy_dollar_dollar -> cont 42#;
	DoubleQuoted happy_dollar_dollar -> cont 43#;
	DollarWord happy_dollar_dollar -> cont 44#;
	DollarDollarWord happy_dollar_dollar -> cont 45#;
	UpperWord happy_dollar_dollar -> cont 46#;
	LowerWord happy_dollar_dollar -> cont 47#;
	SignedInt happy_dollar_dollar -> cont 48#;
	UnsignedInt happy_dollar_dollar -> cont 49#;
	Real happy_dollar_dollar -> cont 50#;
	Slash -> cont 51#;
	CommentToken happy_dollar_dollar -> cont 52#;
	_ -> happyError' (tk:tks)
	}

happyError_ 53# tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Functor HappyIdentity where
    fmap f (HappyIdentity a) = HappyIdentity (f a)

instance Applicative HappyIdentity where
    pure  = return
    (<*>) = ap
instance Monad HappyIdentity where
    return = HappyIdentity
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (return) a
happyError' :: () => [(Token)] -> HappyIdentity a
happyError' = HappyIdentity . ((\xs -> case xs of
                    xs -> error ("Parse error, pos: "++show (take 25 xs))))

parseTSTP tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (happyOut4 x))

happySeq = happyDontSeq


stripQuotes which (x:xs) = go xs
                      where
                        go [x] = []
                        go ('\\':'\\':xs) = '\\':go xs
                        go ('\\':which:xs) = which:go xs
                        go (x:xs) = x:go xs

fApp2pApp (FunApp x args) = PredApp x args
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 19 "<built-in>" #-}
{-# LINE 1 "/usr/local/lib/ghc-8.0.1/include/ghcversion.h" #-}


















{-# LINE 20 "<built-in>" #-}
{-# LINE 1 "/var/folders/3t/cxqg6zhd2ys_qwb8ny5zy7280000gn/T/ghc20538_0/ghc_2.h" #-}



























































































































































































































































































{-# LINE 21 "<built-in>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 


{-# LINE 13 "templates/GenericTemplate.hs" #-}





-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif

{-# LINE 46 "templates/GenericTemplate.hs" #-}


data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList






{-# LINE 67 "templates/GenericTemplate.hs" #-}


{-# LINE 77 "templates/GenericTemplate.hs" #-}










infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is 0#, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}
          

          case action of
                0#           -> {- nothing -}
                                     happyFail i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}
                                                   
                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}
                                     

                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = indexShortOffAddr happyActOffsets st
         off_i  = (off Happy_GHC_Exts.+# i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else False
         action
          | check     = indexShortOffAddr happyTable off_i
          | otherwise = indexShortOffAddr happyDefActions st


indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#





data HappyAddr = HappyA# Happy_GHC_Exts.Addr#




-----------------------------------------------------------------------------
-- HappyState data type (not arrays)


{-# LINE 170 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = indexShortOffAddr happyGotoOffsets st1
             off_i = (off Happy_GHC_Exts.+# nt)
             new_state = indexShortOffAddr happyTable off_i



          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = indexShortOffAddr happyGotoOffsets st
         off_i = (off Happy_GHC_Exts.+# nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (0# is the error token)

-- parse error if we are in recovery and we fail again
happyFail 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  0# tk old_st (HappyCons ((action)) (sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        happyDoAction 0# tk action sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ( (Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.

