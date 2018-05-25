module Data.Enum.Verified

import Data.Fin
import Syntax.PreorderReasoning

import Data.Equality.Conversion
import Data.Equality.If
import Data.Enum.Verified.Lemmas
import Data.Enum.Verified.Types

%access public export
%default total
          
implementation Enum () where
    pred    () = ()
    succ    () = ()
    toNat   () = Z
    fromNat _  = ()

implementation Enum Bool where
    pred  False   = False
    pred  True    = False
    succ  False   = True
    succ  True    = True
    toNat False   = Z     
    toNat True    = S Z
    fromNat Z     = False
    fromNat (S _) = True

implementation HasDefaultImpl Ord Bool where DefaultImpl = %implementation
implementation HasDefaultImpl Enum Bool where DefaultImpl = %implementation

------------------------------------------------------------------------------
-- VerifiedEnum
------------------------------------------------------------------------------

namespace VerifiedEnum

    ||| Proof of correctness of an `Enum` implementation, with a definition of
    ||| 'correctness' retrofitted to the actual behaviour of existing `Enum`
    ||| implementations.
    ||| 
    ||| In Haskell, neither <https://hackage.haskell.org/package/base-4.10.1.0/docs/Prelude.html#t:Enum the API documentation>
    ||| nor the <https://www.haskell.org/onlinereport/haskell2010/haskellch11.html#x18-18400011.2 Haskell 2010 Report>
    ||| specify many laws for `Enum`, and almost all of those are restricted to
    ||| types which have implementations of both `Enum` and `Bounded` (see
    ||| `VerifiedBoundedEnum` for our implementation of those laws). Some
    ||| specific contrast & comparison with Haskell:
    |||
    ||| 1. 'The calls `succ maxBound` and `pred minBound` should result in a
    |||    runtime error'. However, in Idris they simply result in the same
    |||    value (except in 'grandfathered' cases like `Int` where they result
    |||    in wraparound). The existence of such fixed points or wrap-around
    |||    points is permitted if they are defined and proven in `enumPoints`;
    |||    their uniqueness is verified by `unique_min` and `unique_max`; that
    |||    those points are equal to `minBound` and `maxBound` is verified in
    |||    `VerifiedBoundedEnum`.
    ||| 2. '`fromEnum` and `toEnum` should give a runtime error if the result
    |||    value is not representable in the result type.' Instead, the result
    |||    is clipped to the allowable range. This behaviour is verified by
    |||    `toNat_left_inverse_fromNat`.
    ||| 3. 'The nullary constructors are assumed to be numbered left-to-right
    |||    with the indices 0 through n − 1.' Verified here by
    |||    `toNat_preserves_pred`.
    interface (Enum ty) => VerifiedEnum ty where
        ||| Defines the so-called 'special points' of the enumeration, or
        ||| proves that it has none
        enumPoints :  EnumPoints ty Prelude.pred Prelude.succ Prelude.toNat

        ||| If the enumeration has a minimum point, that point is unique. If
        ||| the enumeration lacks a minimum point, `IsMin` will be `Void` and
        ||| the result type will be `Just x = Nothing`, so implementors could
        ||| only discharge the proof obligation with `absurd`.
        unique_min :  (x : ty)
                   -> IsMin enumPoints x
                   -> Just x = MinPoint enumPoints

        ||| If the enumeration has a maximum point, that point is unique. If
        ||| the enumeration lacks a maximum point, `IsMax` will be `Void` and
        ||| the result type will be `Just _ = Nothing`, so implementors could
        ||| only discharge the proof obligation with `absurd`.
        unique_max :  (x : ty)
                   -> IsMax enumPoints x
                   -> Just x = MaxPoint enumPoints

        ||| `pred` is a left inverse of `succ` everywhere except the maximum
        ||| fixed-point.
        pred_left_inverse_succ :  (a : ty)
                               -> Not (IsFixedMax enumPoints a)
                               -> (a = Prelude.pred (succ a))

        ||| `succ` is a left inverse of `pred` everywhere except the minimum
        ||| fixed-point.
        succ_left_inverse_pred :  (a : ty)
                               -> Not (IsFixedMin enumPoints a)
                               -> (a = succ (Prelude.pred a))

        ||| `fromNat` is a left inverse of `toNat`, except at points where
        ||| `toNat` misbehaves
        fromNat_left_inverse_toNat
            :  (a : ty)
            -> Either (BelowToNatMin enumPoints a)
                      (Prelude.fromNat (Prelude.toNat a) = a)
                                             
        ||| `toNat` is a left inverse of `fromNat`, except when `fromNat`
        ||| results in one of the special points.
        toNat_left_inverse_fromNat
            :  (n : Nat)
            -> Either (IsSpecialPoint enumPoints (Prelude.fromNat n))
                      (Prelude.toNat (Prelude.fromNat {a=ty} n) = n)
        
        {-
        ||| `toNat` produces consecutive values in the order of enumeration.
        toNat_preserves_pred :  (a : ty)
                             -> a = pred b
                             -> toNat a = pred (toNat b)
        -}

||| `Dec`ides whether the given value `a` is a minimum fixed point of the
||| enumeration
decIsFixedMin :  (DecEq ty, VerifiedEnum ty)
              => (a : ty) -> Dec (IsFixedMin (enumPoints {ty}) a)
decIsFixedMin {ty} a with (enumPoints {ty})
    | FixedBothPoints    pts _ = decEq a (fst $ predFixedPoint pts)
    | WrapBothPoints     _   _ = No id -- Dec Void is always No, of course
    | WrapBothPointsNeg  _   _ = No id
    | InfinitePredPoints _   _ = No id
    | InfiniteSuccPoints pts _ = decEq a (fst $ predFixedPoint pts)
    | InfiniteBothPoints _   _ = No id

||| `Dec`ides whether the given value `a` is a maximum fixed point of the
||| enumeration
decIsFixedMax :  (DecEq ty, VerifiedEnum ty)
              => (a : ty) -> Dec (IsFixedMax (enumPoints {ty}) a)
decIsFixedMax {ty} a with (enumPoints {ty})
    | FixedBothPoints    pts _ = decEq a (fst $ succFixedPoint pts)
    | WrapBothPoints     _   _ = No id
    | WrapBothPointsNeg  _   _ = No id
    | InfinitePredPoints pts _ = decEq a (fst $ succFixedPoint pts)
    | InfiniteSuccPoints _   _ = No id
    | InfiniteBothPoints _   _ = No id
    
||| `Dec`ides whether the given value `a` is a minimum point of the enumeration
decIsMin :  (DecEq ty, VerifiedEnum ty)
         => (a : ty) -> Dec (IsMin (enumPoints {ty}) a)
decIsMin {ty} a with (enumPoints {ty})
    | FixedBothPoints    pts _ = decEq a (fst $ predFixedPoint pts)
    | WrapBothPoints     pts _ = decEq a (fst $ predWrapPoint pts)
    | WrapBothPointsNeg  pts _ = decEq a (fst $ predWrapPoint pts)
    | InfinitePredPoints _   _ = No id
    | InfiniteSuccPoints pts _ = decEq a (fst $ predFixedPoint pts)
    | InfiniteBothPoints _   _ = No id

||| `Dec`ides whether the given value `a` is a maximum point of the enumeration
decIsMax :  (DecEq ty, VerifiedEnum ty)
         => (a : ty) -> Dec (IsMax (enumPoints {ty}) a)
decIsMax {ty} a with (enumPoints {ty})
    | FixedBothPoints    pts _ = decEq a (fst $ succFixedPoint pts)
    | WrapBothPoints     pts _ = decEq a (fst $ succWrapPoint pts)
    | WrapBothPointsNeg  pts _ = decEq a (fst $ succWrapPoint pts)
    | InfinitePredPoints pts _ = decEq a (fst $ succFixedPoint pts)
    | InfiniteSuccPoints pts _ = No id
    | InfiniteBothPoints _   _ = No id

||| `Dec`ides whether the given value `a` is a special point of the enumeration
||| Tests for the minimum point first, so if the same point is both minimum and
||| maximum this will return `Yes` `SpecialMin`.
decIsSpecialPoint :  (DecEq ty, VerifiedEnum ty)
                  => (a : ty) -> Dec (IsSpecialPoint (enumPoints {ty}) a)
decIsSpecialPoint a with (decIsMin a)
    | Yes isMin = Yes $ SpecialMin isMin
    | No notMin with (decIsMax a)
        | Yes isMax = Yes $ SpecialMax isMax
        | No notMax = No $ \x => case x of
            SpecialMin isMin => notMin isMin
            SpecialMax isMax => notMax isMax

||| Given a `Dec`ision procedure for `a`, if `Not a` implies `b`, then `Either`
||| `a` or `b` must be true.
decEither : Dec a -> (Not a -> b) -> Either a b
decEither (Yes a) _ = Left a
decEither (No na) f = Right $ f na

------------------------------------------------------------------------------
-- VerifiedEnum implementations
------------------------------------------------------------------------------

implementation VerifiedEnum () where
    enumPoints = FixedBothPoints enumPoints toNatPoints where
        enumPoints = MkPoints (() ** Refl) (() ** Refl)
            (\(() ** refl) => uninhabited $ sym refl)
            (\(() ** refl) => uninhabited refl)
        toNatPoints (() ** (val_neq, _)) = val_neq Refl

    unique_min () Refl = Refl
    unique_max () Refl = Refl
                    
    pred_left_inverse_succ () not_unit = absurd $ not_unit Refl
    succ_left_inverse_pred () not_unit = absurd $ not_unit Refl
    
    fromNat_left_inverse_toNat ()    = Right Refl
    toNat_left_inverse_fromNat Z     = Right Refl
    toNat_left_inverse_fromNat (S _) = Left $ SpecialMin Refl
    
implementation VerifiedEnum Bool where
    enumPoints = FixedBothPoints (MkPoints (False ** Refl) (True ** Refl)
        noPredWrap noSuccWrap) toNatPoints where
        noPredWrap (False ** refl) = uninhabited $ sym refl
        noPredWrap (True  ** refl) = uninhabited $ sym refl
        noSuccWrap (False ** refl) = uninhabited refl
        noSuccWrap (True  ** refl) = uninhabited refl
        toNatPoints (False ** (val_neq, toNat_eq)) = val_neq Refl
        toNatPoints (True  ** (val_neq, toNat_eq)) = absurd toNat_eq
        
    unique_min False Refl = Refl
    unique_min True  Refl impossible
    
    unique_max False Refl impossible
    unique_max True  Refl = Refl
    
    pred_left_inverse_succ False not_true = Refl
    pred_left_inverse_succ True  not_true = absurd $ not_true Refl

    succ_left_inverse_pred False not_false = absurd $ not_false Refl
    succ_left_inverse_pred True  not_false = Refl

    fromNat_left_inverse_toNat False = Right Refl
    fromNat_left_inverse_toNat True  = Right Refl
    
    toNat_left_inverse_fromNat Z         = Right Refl
    toNat_left_inverse_fromNat (S Z)     = Right Refl
    toNat_left_inverse_fromNat (S (S _)) = Left $ SpecialMax Refl
    
implementation VerifiedEnum Nat where
    enumPoints = InfiniteSuccPoints (MkPoints (Z ** Refl) noSuccFixed
        noPredWrap noSuccWrap) toNatPoints where
        
        noSuccFixed (n ** refl) = n_not_s_n n refl
        noPredWrap  (Z ** refl) = uninhabited $ sym refl
        noPredWrap  (n ** refl) = go n refl where
            go Z         refl   = uninhabited $ sym refl
            go (S Z)     refl   = uninhabited $ sym refl
            go (S (S n)) refl   = go (S n) $ predPreservesCompare refl
        noSuccWrap  (n ** refl) = go n refl where
            go Z         refl   = uninhabited refl
            go (S Z)     refl   = uninhabited refl
            go (S (S n)) refl   = go (S n) $ predPreservesCompare refl

        toNatPoints (val ** (val_neq, toNat_eq)) = val_neq toNat_eq
        
    unique_min Z     Refl = Refl
    unique_min (S n) Refl impossible
    
    unique_max n void = absurd void
    
    pred_left_inverse_succ n not_max = Refl
    
    succ_left_inverse_pred Z     not_min = absurd $ not_min Refl
    succ_left_inverse_pred (S n) not_min = Refl
    
    fromNat_left_inverse_toNat n = Right Refl
    toNat_left_inverse_fromNat n = Right Refl

||| Implementation consists mostly of cheating and ad-hoc postulates    
implementation VerifiedEnum Int where
    enumPoints = WrapBothPointsNeg (MkPoints noPredFixed noSuccFixed
        ((-9223372036854775808) ** Refl) (9223372036854775807 ** Refl))
        toNatPoints where
        noPredFixed (n ** refl) = zero_not_one $ cong {f=negate} $ 
            0                   ={ sym a_minus_a_is_zero                   }=
            (n - n)             ={ cong {f=\a=>a-n} refl                   }=
            ((n - 1) - n)       ={ cong {f=\a=>a-n} sub_is_add_negative    }=
            ((n + (-1)) - n)    ={ cong {f=\a=>a-n} add_commutative        }=
            (((-1) + n) - n)    ={ add_sub_associative                     }=
            ((-1) + (n - n))    ={ cong a_minus_a_is_zero                  }=
            ((-1) + 0)          ={ Refl                                    }=
            (-1)                QED
        noSuccFixed (n ** refl) = zero_not_one $
            0                   ={ sym a_minus_a_is_zero                   }=
            (n - n)             ={ cong {f=\a=>a-n} refl                   }=
            ((n + 1) - n)       ={ cong {f=\a=>a-n} add_commutative        }=
            ((1 + n) - n)       ={ add_sub_associative                     }=
            (1 + (n - n))       ={ cong {f=\a=>1+a} a_minus_a_is_zero      }=
            1                   QED
        toNatPoints = (0 ** (zero_not_one . cong {f=negate}, Refl))
        
    unique_min n refl = believe_me $ Refl {x=n}
    unique_max n refl = believe_me $ Refl {x=n}
    
    pred_left_inverse_succ n not_max =
        n                ={ sym zero_is_add_identity                     }=
        (n + 0)          ={ cong $ sym a_minus_a_is_zero                 }=
        (n + (1 - 1))    ={ sym $ add_sub_associative                    }=
        ((n + 1) - 1)    QED

    succ_left_inverse_pred n not_min =
        n                ={ sym zero_is_add_identity                     }=
        (n + 0)          ={ cong $ sym a_minus_a_is_zero                 }=
        (n + (1 - 1))    ={ cong $ sub_is_add_negative                   }=
        (n + (1 + (-1))) ={ sym add_associative                          }=
        ((n + (-1)) + 1) ={ cong {f=\a=>a+1} $ sym $ sub_is_add_negative }=
        ((n - 1) + 1)    QED

    fromNat_left_inverse_toNat n with (decEq n 0)
        | Yes zero = Right $ believe_me $ Refl {x=n}
        | No nzero = if n > 0 
                     then Right $ believe_me $ Refl {x=n}
                     else Left (nzero, believe_me $ Refl {x=0})
    toNat_left_inverse_fromNat n = Right $ believe_me $ Refl {x=n}

implementation VerifiedEnum (Fin (S n)) where
    enumPoints {n} = FixedBothPoints (MkPoints (FZ ** Refl) (maxFin ** maxPrf)
        noPredWrap noSuccWrap) toNatPoints where

        fprd : Fin (S q) -> Fin (S q)
        fprd = pred
        fsuc : Fin (S q) -> Fin (S q)
        fsuc = succ
        fnat : Fin (S q) -> Nat
        fnat = toNat
        
        maxFin : Fin (S n)
        maxFin = last {n}
        
        maxPrf with (strengthen maxFin) proof strengthen_maxFin_prf
            | Left no = Refl
            | Right y =  (\Refl impossible) $
                trans strengthen_maxFin_prf $ cannot_strengthen_last _
        
        noPredWrap (x ** refl) = go n x refl where
            go :  (m : Nat) -> (x : Fin (S m))
               -> IsWrapPoint fnat Prelude.Interfaces.LT fprd x
               -> Void
            go m         FZ          refl = uninhabited $ sym refl
            go (S m)     (FS FZ)     refl = uninhabited $ sym refl
            go (S (S m)) (FS (FS x)) refl =
                go (S m) (FS x) (predPreservesCompare refl)

        noSuccWrap (x ** compare_x_succ_x_gt)
            with (compare_succ_either_eq_or_lt _ x)
            | Left compare_x_succ_x_eq  = absurd $
                 EQ                    ={ sym compare_x_succ_x_eq        }=
                 (compare x (succ x))  ={ finToNat_preserves_compare _ _ }=
                 (compare (toNat x)
                     (toNat $ succ x)) ={ compare_x_succ_x_gt            }=
                 GT                    QED
            | Right compare_x_succ_x_lt = absurd $
                 LT                    ={ sym compare_x_succ_x_lt        }=
                 (compare x (succ x))  ={ finToNat_preserves_compare _ _ }=
                 (compare (toNat x)
                     (toNat $ succ x)) ={ compare_x_succ_x_gt            }=
                 GT                    QED
        
        toNatPoints (x ** (pred_neq, toNat_eq)) =
            pred_neq $ finToNatInjective _ _ toNat_eq

    unique_min x isMin = cong isMin
    unique_max x isMax = cong isMax

    pred_left_inverse_succ x not_max with (strengthen x) proof str_x_prf
        | Left s_no = absurd $ not_max $ strengthen_left_is_last _ x $
            sym str_x_prf
        | Right s_x with (weaken s_x) proof ws_x_prf
            | ws_x with (weaken_usually_left_inverse_strengthen _ x $
                not_max . strengthen_left_is_last _ _)
                | wlis_y = 
                    x            ={ sym $ rightInjective $ 
                                    trans (cong str_x_prf) wlis_y       }=
                    (weaken s_x) ={ sym ws_x_prf                        }=
                    ws_x         QED
        
    succ_left_inverse_pred FZ     not_min = absurd $ not_min Refl
    succ_left_inverse_pred (FS x) not_min
        with (strengthen (weaken (FS x))) proof sw_fsx
        | Left no = (\Refl impossible) $ -- strengthen never fails after weaken
            trans sw_fsx $ strengthen_left_inverse_weaken _ $ FS x
        | Right y = sym $ rightInjective $
            trans sw_fsx $ strengthen_left_inverse_weaken _ $ FS x
    
    fromNat_left_inverse_toNat FZ      = Right Refl
    fromNat_left_inverse_toNat (FS FZ) = Right Refl
    fromNat_left_inverse_toNat (FS (FS a))
        with (fromNat_left_inverse_toNat (FS a))
        | Left no = absurd no
        | Right y = Right $ sym $
            (FS $ FS a)                   ={ cong {f=FS} $ sym y         }=
            (FS $ fromNat $ toNat $ FS a) ={ fromNat_FS _ (toNat $ FS a) }=
            (fromNat $ S $ toNat $ FS a)  ={ Refl                        }=
            (fromNat $ toNat $ FS $ FS a) QED
                     
    toNat_left_inverse_fromNat {n} val
        with (finToNat_left_inverse_natToFin n val)
        | Left is_nothing  = Left $ SpecialMax $ natToFin_last n val is_nothing
        | Right is_inverse with (natToFin val (S n)) proof natToFin_prf
            | Nothing = (\Refl impossible) is_inverse
            | Just _  = Right $ justInjective is_inverse
