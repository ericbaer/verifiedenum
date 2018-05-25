||| Random out-of-place proofs
module Data.Enum.Verified.Lemmas

import Data.Bifunctor
import Data.Fin
import Syntax.PreorderReasoning

import Data.Equality.If -- for the DecEq implementation on Ordering

%access public export
%default total

%hide Prelude.Nat.LT
%hide Prelude.Nat.GT
    
||| Proof that `bimap`ping injective functions on `Either` is injective
||| @f_inj proof that `f` is injective
||| @g_inj proof that `g` is injective
bimap_Either_injective :  (c, d : Either l r)
                       -> {f : l -> l'}
                       -> (f_inj : (a, b : l) -> f a = f b -> a = b)
                       -> {g : r -> r'}
                       -> (g_inj : (a, b : r) -> g a = g b -> a = b)
                       -> bimap f g c = bimap f g d
                       -> c = d
bimap_Either_injective (Left _)   (Right _)      _         _     Refl impossible
bimap_Either_injective (Right _)  (Left _)       _         _     Refl impossible 
bimap_Either_injective (Left c')  (Left d')  {f} f_inj {g} g_inj refl =
    cong $ f_inj c' d' $ leftInjective $
    (Left $ f c')          ={ Refl   }=
    (bimap f g (Left c'))  ={ refl   }=
    (bimap f g (Left d'))  ={ Refl   }=
    (Left $ f d')          QED
bimap_Either_injective (Right c') (Right d') {f} f_inj {g} g_inj refl =
    cong $ g_inj c' d' $ rightInjective $
    (Right $ g c')         ={ Refl   }=
    (bimap f g (Right c')) ={ refl   }=
    (bimap f g (Right d')) ={ Refl   }=
    (Right $ g d')         QED

||| Proof that `map`ping an injective function on `Either` is injective
||| @f_inj proof that `f` is injective
map_Either_injective :  (c, d : Either l ty)
                     -> {f : ty -> ty'}
                     -> (f_inj : (a, b : ty) -> f a = f b -> a = b)
                     -> map f c = map f d
                     -> c = d
map_Either_injective (Left _)   (Left _)       f_inj Refl = Refl
map_Either_injective (Left _)   (Right _)      f_inj Refl impossible
map_Either_injective (Right _)  (Left _)       f_inj Refl impossible 
map_Either_injective (Right c') (Right d') {f} f_inj refl =
    cong $ f_inj c' d' $ rightInjective $
    (Right $ f c')     ={ Refl   }=
    (map f (Right c')) ={ refl   }=
    (map f (Right d')) ={ Refl   }=
    (Right $ f d')     QED

------------------------------------------------------------------------------
-- Proofs about Fin in general
------------------------------------------------------------------------------

fz_not_fs : Not (FZ = FS x)
fz_not_fs Refl impossible

last_pred : (n : Nat) -> FS o = (last {n=S n}) -> o = (last {n})
last_pred n Refl = Refl

last_fs : (n : Nat) -> o = (last {n}) -> FS o = (last {n=S n})
last_fs n Refl = Refl

||| In `Fin 2` and bigger, `last` is never zero
last_not_fz :  (m : Nat)
            -> Not (last {n=(S m)} = FZ)
last_not_fz m Refl impossible

------------------------------------------------------------------------------
-- Proofs about strengthen
------------------------------------------------------------------------------
            
||| The result of `strengthen` is `Left` if and only if the result of its
||| recursive call is also `Left`.
strengthen_step_left :  (n : Nat)
                     -> (o : Fin (S n))
                     -> strengthen o = Left p
                     -> strengthen (FS o) = Left (FS p)
strengthen_step_left n o refl with (strengthen o)
    | Left no = cong {f=bimap FS FS} refl
    | Right y = (\Refl impossible) refl

||| The result of `strengthen` is `Right` if and only if the result of its
||| recursive call is also `Right`.
strengthen_step_right :  (n : Nat)
                      -> (o : Fin (S n))
                      -> strengthen o = Right p
                      -> strengthen (FS o) = Right (FS p)
strengthen_step_right n o refl with (strengthen o)
    | Left no = (\Refl impossible) refl 
    | Right y = cong {f=bimap FS FS} refl

||| The result of `strengthen` is `Left` if and only if the result of its
||| recursive call is also `Left`.
strengthen_stepDown_left :  (n : Nat)
                         -> (o : Fin (S n))
                         -> strengthen (FS o) = Left (FS p)
                         -> strengthen o = Left p
strengthen_stepDown_left n o refl with (strengthen o)
    | Left no = cong {f=Left} $ FSInjective _ _ $ leftInjective refl
    | Right y = (\Refl impossible) refl

||| The result of `strengthen` is `Right` if and only if the result of its
||| recursive call is also `Right`
strengthen_stepDown_right :  (n : Nat)
                          -> (o : Fin (S n))
                          -> strengthen (FS o) = Right (FS p)
                          -> strengthen o = Right p
strengthen_stepDown_right n o refl with (strengthen o)
    | Left no = (\Refl impossible) refl
    | Right y = cong {f=Right} $ FSInjective _ _ $ rightInjective refl

||| The result of `strengthen` is always `FS` the result of its recursive call
strengthen_stepDown :  (n : Nat)
                    -> (o : Fin (S n))
                    -> strengthen (FS o) = bimap FS FS (strengthen o)
strengthen_stepDown n o with (strengthen o) proof strengthen_o_prf
    | Left no_o = Refl
    | Right y_o = Refl

||| `strengthen` will always return `Left` when given `last` as an argument
cannot_strengthen_last :  (n : Nat) -> strengthen (last {n}) = Left (last {n})
cannot_strengthen_last Z      = Refl
cannot_strengthen_last (S n') =
    strengthen_step_left _ _ $ cannot_strengthen_last n'

||| `strengthen`ing a non-`FZ` value never yields `FZ`
strengthen_fs_not_left_fz :  (n : Nat)
                     -> (o : Fin (S n))
                     -> Not (strengthen (FS o) = Left FZ)
strengthen_fs_not_left_fz Z      FZ      Refl  impossible
strengthen_fs_not_left_fz (S _)  FZ      Refl  impossible
strengthen_fs_not_left_fz (S n') (FS o') str_o with (strengthen o') proof str_o'
    | Left o_no = fz_not_fs $ leftInjective $ sym str_o
    | Right o_y with (strengthen (FS o')) proof str_fso'
        | Left fso_no = (\Refl impossible) str_o
        | Right fso_y = (\Refl impossible) str_o

||| `strengthen`ing a non-`FZ` value never yields `FZ`
-- FIXME: changing this to `Not` breaks compare_fs_is_lt
strengthen_fs_not_right_fz :  (n : Nat)
                     -> (o : Fin (S n))
                     -> strengthen (FS o) = Right FZ
                     -> Void
strengthen_fs_not_right_fz Z      FZ      Refl  impossible
strengthen_fs_not_right_fz (S _)  FZ      Refl  impossible
strengthen_fs_not_right_fz (S n') (FS o') str_o
    with (strengthen o') proof str_o'
    | Left ono with (strengthen (FS o')) proof str_fso'
        | Left fsono = (\Refl impossible) str_o
        | Right fsoy = (\Refl impossible) str_o
    | Right oy = fz_not_fs $ rightInjective $ sym str_o

||| If `strengthen` fails on a `Fin 2` or higher, then that `Fin` is not `FZ`
strengthen_not_fz :  (n : Nat)
                  -> (o : Fin (S (S n)))
                  -> strengthen o = Left p
                  -> Not (p = FZ)
strengthen_not_fz Z      FZ      Refl impossible
strengthen_not_fz Z      (FS FZ) Refl = \Refl impossible
strengthen_not_fz (S _)  FZ      Refl impossible
strengthen_not_fz (S n') (FS o') refl =
    \p_fz => strengthen_fs_not_left_fz _ _ (trans refl $ cong {f=Left} p_fz)

||| If `strengthen` fails, that means its argument is equal to `last`
strengthen_left_is_last :  (n : Nat)
                        -> (o : Fin (S n))
                        -> strengthen o = Left p
                        -> o = (last {n})
strengthen_left_is_last Z          FZ           {p=FZ}   Refl = Refl
strengthen_left_is_last Z          FZ           {p=FS _} Refl impossible
strengthen_left_is_last Z          (FS _)                Refl impossible
strengthen_left_is_last Z          (FS _)                Refl impossible
strengthen_left_is_last (S _)      FZ                    Refl impossible
strengthen_left_is_last (S Z)      (FS FZ)               Refl = Refl
strengthen_left_is_last (S (S n')) (FS FZ)      {p=FZ}   Refl impossible
-- FIXME can this be improved? this seems absurdly baroque for disposing of
-- such a simple impossible case
strengthen_left_is_last (S (S n')) (FS (FS o')) {p=FZ}   refl 
    with (strengthen (FS (FS o'))) proof strengthen_fsfso
    | Left no = absurd $ strengthen_not_fz _ (FS (FS o'))
        (sym strengthen_fsfso) (leftInjective refl)
    | Right y = (\Refl impossible) refl
strengthen_left_is_last (S n')     (FS o')      {p=FS _} refl = cong {f=FS} $
    strengthen_left_is_last n' o' $ strengthen_stepDown_left n' o' refl

strengthen_fs_commute :  (n : Nat)
                      -> (o : Fin (S n))
                      -> strengthen (FS o) = bimap FS FS (strengthen o)
strengthen_fs_commute Z      FZ      = Refl
strengthen_fs_commute Z      (FS _)  impossible
strengthen_fs_commute (S _)  FZ      = Refl
strengthen_fs_commute (S n') (FS o') with (strengthen_fs_commute n' o')
   | ind with (strengthen (FS o')) proof str_fsfso
       | Left no = Refl
       | Right y = Refl

weaken_fs_commute_bimap :  (x : Either (Fin (S a)) (Fin a))
                        -> map Data.Fin.weaken (bimap FS FS x) =
                           bimap FS FS (map Data.Fin.weaken x)
weaken_fs_commute_bimap (Left l)  = Refl
weaken_fs_commute_bimap (Right r) = Refl

||| `strengthen`ing then `weaken`ing returns `Right` of the original value,
||| if `strengthen` succeeded in the first place.
weaken_usually_left_inverse_strengthen
    :  (n : Nat)
    -> (o : Fin (S n))
    -> Not (strengthen o = Left o)
    -> map Data.Fin.weaken (strengthen o) = Right o
weaken_usually_left_inverse_strengthen Z      FZ      not_left =
    absurd $ not_left Refl
weaken_usually_left_inverse_strengthen Z      (FS _)  not_left impossible
weaken_usually_left_inverse_strengthen (S _)  FZ      not_left = Refl
weaken_usually_left_inverse_strengthen (S n') (FS o') not_left
    with (weaken_usually_left_inverse_strengthen n' o'
          (not_left . strengthen_step_left n' o'))
    | ind =
        (map weaken (strengthen (FS o'))) ={ cong $ strengthen_fs_commute _ _ }=
        (map weaken (bimap FS FS
         (strengthen o')))                ={ weaken_fs_commute_bimap _        }=
        (bimap FS FS
         (map weaken (strengthen o')))    ={ cong ind                         }=
        (Right (FS o'))                   QED        

||| `weaken`ing then `strengthen`ing always succeeds, and returns `Right` of
||| the original value.
strengthen_left_inverse_weaken :  (n : Nat)
                               -> (o : Fin (S n))
                               -> strengthen (weaken o) = Right o
strengthen_left_inverse_weaken Z      FZ      = Refl
strengthen_left_inverse_weaken Z      (FS _)  impossible                               
strengthen_left_inverse_weaken (S _)  FZ      = Refl
strengthen_left_inverse_weaken (S n') (FS o') = strengthen_step_right _ _ $
    strengthen_left_inverse_weaken n' o'
                               
------------------------------------------------------------------------------
-- Proofs about succ
------------------------------------------------------------------------------

||| `last` is a fixed point of `succ`
succ_last_is_last : (n : Nat) -> succ (last {n}) = (last {n})
succ_last_is_last n with (strengthen $ last {n}) proof strengthen_last_n_prf
    | Left no = Refl
    | Right y = (\Refl impossible) $ trans strengthen_last_n_prf $
        cannot_strengthen_last n

||| The result of `succ` is `Either` the `last` value in the `Fin` type, or
||| the result of `strengthen`ing `FS`
succ_either_last_or_fs :  (n : Nat)
                       -> (o : Fin (S n))
                       -> Either (o = last {n})
                                 (Right (succ o) = strengthen (FS o))
succ_either_last_or_fs Z      FZ      = Left Refl
succ_either_last_or_fs Z      (FS _)  impossible
succ_either_last_or_fs (S n') FZ      = Right Refl
succ_either_last_or_fs (S n') (FS o') with (decEq (FS o') (last {n=S n'}))
    | Yes is_last = Left is_last
    | No not_last with (strengthen (FS o')) proof strengthen_fso_prf
        | Left no = absurd $ not_last $ strengthen_left_is_last _ (FS o') $
            sym strengthen_fso_prf
        | Right y = Right Refl

||| `pred` and `FS` commute on all arguments besides `FZ`
pred_FS_commute :  (n : Nat)
                -> (o : Fin (S n))
                -> Not (o = FZ)
                -> FS (pred o) = pred (FS o)
pred_FS_commute _ FZ      o'_not_fz = absurd $ o'_not_fz Refl
pred_FS_commute _ (FS o') o'_not_fz = Refl
    
||| `succ` and `FS` commute on all arguments
succ_FS_commute :  (n : Nat)
        -> (o : Fin (S n))
        -> FS (succ o) = succ (FS o)
succ_FS_commute n o with (strengthen o)
    | Left no = Refl
    | Right y = Refl

succ_stepDown :  (n : Nat)
              -> (o : Fin (S n))
              -> Right (succ (FS o)) = strengthen (FS (FS o))
              -> Right (succ o) = strengthen (FS o)
succ_stepDown Z      FZ      Refl impossible
succ_stepDown Z      (FS _)  Refl impossible
succ_stepDown (S _)  FZ      Refl = Refl
succ_stepDown (S n') (FS o') refl =
    bimap_Either_injective _ _ FSInjective FSInjective $
    (bimap FS FS $ Right $ succ $ FS o')    ={ Refl                        }=
    (Right $ FS $ succ $ FS o')             ={ cong $ succ_FS_commute _ _  }=
    (Right $ succ $ FS $ FS o')             ={ refl                        }=
    (strengthen $ FS $ FS $ FS o')          ={ strengthen_stepDown _
                                               (FS $ FS o')                }=
    (bimap FS FS $ strengthen $ FS $ FS o') QED

||| In `Fin 2` and bigger, `succ` is always `FS` of something
succ_is_FS :  (n : Nat)
           -> (o : Fin (S (S n)))
           -> (o' ** (succ o = FS o'))
succ_is_FS n o with (succ o) proof succ_o
    | FZ with (strengthen o) proof str_o
        | Left no with (o) 
            | FZ     = (\Refl impossible) succ_o
            | (FS x) = (\Refl impossible) succ_o
        | Right y with (o)
            | FZ     = (\Refl impossible) succ_o
            | (FS x) = (\Refl impossible) succ_o
    | (FS o') = (o' ** Refl)

||| In `Fin 2` and bigger, `succ` is never zero
succ_not_FZ :  (n : Nat)
            -> (o : Fin (S (S n)))
            -> Not (succ o = FZ)
succ_not_FZ n o succ_fz with (succ_is_FS n o)
    | (o' ** succ_fs) = (\Refl impossible) $ trans (sym succ_fz) succ_fs

------------------------------------------------------------------------------
-- Proofs about natToFin
------------------------------------------------------------------------------

||| A number is never equal to its successor
n_not_s_n : (n : Nat) -> n = S n -> Void
n_not_s_n   Z     Refl impossible
n_not_s_n   (S _) Refl impossible

||| `FS` can be 'moved inside' of `fromNat`
fromNat_FS :  (max, val : Nat)
           -> FS (fromNat {a=Fin (S max)} val) =
              fromNat {a=Fin (S (S max))} (S val)
fromNat_FS max val with (natToFin val (S max))
    | Nothing = Refl
    | Just _  = Refl

||| Applying `pred` to a `Fin` and to both the value and ceiling arguments of
||| `natToFin` preserves their relationship.
||| @max the maximum value of the `Fin`
||| @val a natural number
||| @o the `Fin` equivalent of `val`
||| @prf proof of relationship between `val` and `o`
natToFin_preserves_pred :  (max : Nat)
                        -> (val : Nat)
                        -> (o : Fin (S max))
                        -> (prf : Just (FS o) = natToFin (S val) (S (S max)))
                        -> (Just o = natToFin val (S max))
natToFin_preserves_pred max val o refl with (natToFin val (S max))
    | Nothing = absurd refl
    | Just o' with (decEq o o')
        | Yes eq = cong {f=Just} eq
        | No neq = absurd $ neq $ FSInjective _ _ $ justInjective refl

||| Applying `succ` to a `Fin` and to both the value and ceiling arguments of
||| `natToFin` preserves their relationship
||| @max the maximum value of the `Fin`
||| @val a natural number
||| @o the `Fin` equivalent of `val`
||| @prf proof of relationship between `val` and `o`
natToFin_preserves_succ :  (max, val : Nat)
                        -> (o : Fin (S max))
                        -> (prf : Just o = natToFin val (S max))
                        -> (Just (FS o) = natToFin (S val) (S (S max)))
natToFin_preserves_succ max val o refl
    with (natToFin (S val) (S (S max))) proof sval_prf
    | Nothing with (natToFin val (S max)) proof val_prf
        | Nothing = absurd refl
        | Just yo = absurd $ trans (cong {f=map FS} refl) $ sym sval_prf
    | Just so with (decEq (FS o) so)
        | Yes eq = cong {f=Just} eq
        | No neq with (natToFin val (S max)) proof val_prf
            | Nothing = absurd refl
            | Just yo = absurd $ neq $ justInjective $
                trans (cong {f=map FS} refl) $ sym sval_prf

natToFin_preserves_succ_nothing :  (max, val : Nat)
                                -> (prf : Nothing = natToFin val (S max))
                                -> (Nothing = natToFin (S val) (S (S max)))
natToFin_preserves_succ_nothing max val refl with (natToFin val (S max))
    | Just _  = absurd refl
    | Nothing = Refl

||| Proof of how `fromNat` relates with `natToFin`
toNat_natToFin :  (max, val : Nat)
               -> (o : Fin (S max))
               -> o = fromNat val
               -> Either (o = last {n=max}) (Just o = natToFin val (S max))
toNat_natToFin max val o refl with (natToFin val (S max)) proof natToFin_prf
    | Just o' = Right $ cong {f=Just} refl
    | Nothing with (decEq o (last {n=max}))
        | Yes eq = Left eq
        | No neq = absurd $ neq refl

finToNat_left_inverse_natToFin
    :  (max, val : Nat)
    -> Either (natToFin val (S max) = Nothing)
              (map Data.Fin.finToNat (natToFin val (S max)) = Just val)
finToNat_left_inverse_natToFin Z        Z            = Right Refl
finToNat_left_inverse_natToFin (S _)    Z            = Right Refl
finToNat_left_inverse_natToFin Z        (S Z)        = Left Refl
finToNat_left_inverse_natToFin Z        (S (S val')) = Left Refl
finToNat_left_inverse_natToFin (S max') (S val')
    with (finToNat_left_inverse_natToFin max' val')
    | Left ind  = Left $ sym $ natToFin_preserves_succ_nothing _ _ $ sym ind
    | Right ind = Right $ sym $
        (Just (S val'))
            ={ Refl                                              }=
        (map S (Just val'))
            ={ sym $ cong {f=map S} ind                          }=
        (map S (map finToNat (natToFin val' (S max')))) 
            ={ sym $ finToNat_step max' (natToFin val' (S max')) }=
        (map finToNat (map FS (natToFin val' (S max')))) 
            ={ cong {f=map finToNat} $ natToFin_step max' val'   }=
        (map finToNat (natToFin (S val') (S (S max'))))
            QED where
            
        natToFin_step :  (max : Nat)
                      -> (val : Nat)
                      -> map FS (natToFin val (S max)) =
                         natToFin (S val) (S (S max))
        natToFin_step max val with (natToFin val (S max))
            | Nothing = Refl
            | Just _  = Refl


        finToNat_step :  (max : Nat)
                      -> (x : Maybe (Fin (S max)))
                      -> map Data.Fin.finToNat (map FS x) =
                         map S (map Data.Fin.finToNat x)
        finToNat_step max Nothing  = Refl
        finToNat_step max (Just x) = Refl
            

natToFin_last :  (max, val : Nat)
              -> natToFin val (S max) = Nothing
              -> fromNat val = last {n=max}
natToFin_last max val refl with (natToFin val (S max)) proof natToFin_prf
    | Nothing = Refl
    | Just _  = (\Refl impossible) refl


------------------------------------------------------------------------------
-- Proofs about compare
------------------------------------------------------------------------------

fs_preserves_compare :  (a, b : Fin n)
                     -> compare a b = compare (FS a) (FS b)
fs_preserves_compare FZ      FZ      = Refl
fs_preserves_compare FZ      (FS _)  = Refl
fs_preserves_compare (FS _)  FZ      = Refl
fs_preserves_compare (FS a') (FS b') = Refl

||| Ad-hoc, in the absence of a `VerifiedOrd`: reflexivity of `compare`
fin_eq_compare : (a, b : Fin n) -> a = b -> compare a b = EQ
fin_eq_compare FZ     FZ     Refl = Refl
fin_eq_compare FZ     (FS b) Refl impossible
fin_eq_compare (FS a) FZ     Refl impossible
fin_eq_compare (FS a) (FS b) refl = fin_eq_compare a b $ FSInjective a b refl

compare_fs_is_lt :  (n : Nat)
                 -> (o : Fin (S n))
                 -> (p : Fin (S n))
                 -> (Right p = strengthen (FS o))
                 -> compare o p = LT
compare_fs_is_lt Z      FZ      FZ      Refl impossible
compare_fs_is_lt (S _)  FZ      FZ      Refl impossible
compare_fs_is_lt (S _)  FZ      (FS _)  Refl = Refl
compare_fs_is_lt (S _)  (FS _)  FZ      refl =
    absurd $ strengthen_fs_not_right_fz _ _ $ sym refl
compare_fs_is_lt (S n') (FS o') (FS p')  refl
    with (sym $ strengthen_stepDown_right (S n') (FS o') $ sym refl)
    | refl' = compare_fs_is_lt n' o' p' refl'

compare_succ_either_eq_or_lt :  (n : Nat)
                             -> (o : Fin (S n))
                             -> Either (compare o (succ o) = EQ)
                                       (compare o (succ o) = LT)
compare_succ_either_eq_or_lt n o with (succ_either_last_or_fs n o)
    | Left x_is_last with (((cong x_is_last) `trans` (succ_last_is_last n))
        `trans` (sym x_is_last))
        | succ_x_is_x = Left $ fin_eq_compare _ _ $ sym succ_x_is_x
    | Right succ_fsx = Right $ compare_fs_is_lt _ _ _ succ_fsx

finToNat_preserves_compare :  (a, b : Fin n)
                           -> compare a b = compare (finToNat a) (finToNat b)
finToNat_preserves_compare FZ      FZ      = Refl
finToNat_preserves_compare FZ      (FS _)  = Refl
finToNat_preserves_compare (FS _)  FZ      = Refl
finToNat_preserves_compare (FS a') (FS b') =
    trans (sym $ fs_preserves_compare a' b') (finToNat_preserves_compare a' b')

||| If `strengthen` succeeds on `o` (i.e. if `o` is not `last`), then `o` is
||| `LT` its `succ`essor.
lt_succ_except_last :  (n : Nat)
                    -> (o : Fin (S n)) 
                    -> (not_last : Right (succ o) = strengthen (FS o))
                    -> compare o (succ o) = LT
lt_succ_except_last Z      FZ      Refl impossible
lt_succ_except_last Z      (FS _)  Refl impossible
lt_succ_except_last (S _)  FZ      refl = Refl
lt_succ_except_last (S n') (FS o') refl =
    (compare (FS o') (succ $ FS o')) ={ cong {f=compare (FS o')} $
                                        sym $ succ_FS_commute _ o'     }=
    (compare (FS o') (FS $ succ o')) ={ sym $ fs_preserves_compare _ _ }=
    (compare o' (succ o'))           ={ lt_succ_except_last n' o' $
                                        succ_stepDown _ _ refl         }=
    LT                               QED
       
------------------------------------------------------------------------------
-- Postulates about integer addition
------------------------------------------------------------------------------

postulate zero_is_add_identity : {a : Int} -> a + 0 = a
postulate add_associative : {a, b, c : Int} ->  (a + b) + c = a + (b + c)
postulate add_commutative : {a, b : Int} -> a + b = b + a
postulate sub_is_add_negative : {a, b : Int} -> a - b = a + (-b)
postulate a_minus_a_is_zero : {a : Int} -> a - a = 0
postulate zero_not_one : (=) {A=Int} {B=Int} 0 1 -> Void

add_sub_associative : {a, b, c : Int} -> (a + b) - c = a + (b - c)
add_sub_associative {a} {b} {c} =
      ((a + b) - c)    ={ sub_is_add_negative            }=
      ((a + b) + (-c)) ={ add_associative                }=
      (a + (b + (-c))) ={ cong $ sym sub_is_add_negative }=
      (a + (b - c))    QED
