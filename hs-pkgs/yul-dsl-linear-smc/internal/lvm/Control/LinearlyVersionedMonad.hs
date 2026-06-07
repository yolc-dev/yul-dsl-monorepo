{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

Linearly versioned monad (LVM) provides a form of "linear safety" in handling effectful data operations.

A short description of such form of "linear safety" can be found in the documentation of 'LVM'.

This module is designed to work with the QualifiedDo syntax, where when import qualified as "LVM", an expression of
@LVM.do@ can start a do-notation syntax block where statements are de-sugared into'(LVM.>>=)' and '(LVM.>>)'.

There may be something to be said about the difference between parameterized and graded monad. In author's limited
understanding of this subject, it seems more appropriate to call 'LVM' parameterized only. For more study about this
matter, please refer to [Orchard, Dominic, Philip Wadler, and Harley Eades III. "Unifying graded and parameterised
monads." arXiv preprint arXiv:2001.10274 (2020).]

-}
module Control.LinearlyVersionedMonad
  ( -- $linear_safety
  ) where
