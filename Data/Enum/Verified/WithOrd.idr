||| VerifiedEnum, with more laws for types also having an Ord implementation
module Data.Enum.Verified.WithOrd

import Data.Fin
import Syntax.PreorderReasoning

import Data.Enum.Verified
import Data.Enum.Verified.Lemmas
import Data.Enum.Verified.Types

%access public export
%default total

------------------------------------------------------------------------------
-- VerifiedOrdEnum
------------------------------------------------------------------------------
      
interface (VerifiedEnum ty, Ord ty) => VerifiedOrdEnum ty where
    ||| An element is `GT` its `pred` everywhere except the minimum
    gt_pred : (x : ty) -> Either (IsMin VerifiedEnum.enumPoints x)
                                 (compare x (pred x) = GT)
    
    ||| An element is `LT` its `succ` everywhere except the maximum
    lt_succ : (x : ty) -> Either (IsMax VerifiedEnum.enumPoints x)
                                 (compare x (succ x) = LT)

implementation VerifiedOrdEnum () where
    gt_pred () = Left Refl
    lt_succ () = Left Refl
                                             
implementation VerifiedOrdEnum Bool where        
    gt_pred False = Left Refl
    gt_pred True  = Right Refl
    
    lt_succ False = Right Refl
    lt_succ True  = Left Refl
      
implementation VerifiedOrdEnum Nat where
    gt_pred Z         = Left Refl
    gt_pred (S Z)     = Right Refl
    gt_pred (S (S n)) with (gt_pred (S n))
        | Left refl    = absurd refl
        | Right normal = Right normal
    
    lt_succ Z         = Right Refl
    lt_succ (S Z)     = Right Refl
    lt_succ (S (S n)) with (lt_succ (S n))
        | Left is_min  = absurd is_min
        | Right normal = Right normal

implementation VerifiedOrdEnum Int where
    -- can't use pattern matching here
    -- see https://github.com/idris-lang/Idris-dev/issues/4265        
    gt_pred n with (decEq n (-9223372036854775808))
        | Yes eq = Left eq
        | No neq = Right $ believe_me $ Refl {x=n}

    lt_succ 9223372036854775807 = Left Refl
    lt_succ n                   = Right $ believe_me $ Refl {x=n}

implementation VerifiedOrdEnum (Fin (S n)) where
    
    gt_pred FZ      = Left Refl
    gt_pred (FS FZ) = Right Refl
    gt_pred (FS (FS x)) with (gt_pred $ FS x)
        | Left fsx_zero       = absurd $ fz_not_fs $ sym fsx_zero
        | Right inductive_prf = Right $
            (compare (FS $ FS x) (pred $ FS $ FS x))
                ={ cong {f=compare (FS $ FS x)} $ sym $
                   pred_FS_commute _ (FS x) (fz_not_fs . sym) }=
            (compare (FS $ FS x) (FS $ pred $ FS x))
                ={ sym $ fs_preserves_compare _ _             }=
            (compare (FS x) (pred $ FS x))
                ={ inductive_prf                              }=
            GT QED
    
    lt_succ x with (succ_either_last_or_fs _ x)
        | Left x_is_last = Left x_is_last
        | Right x_n_last = Right $ lt_succ_except_last _ _ x_n_last
    
                    
