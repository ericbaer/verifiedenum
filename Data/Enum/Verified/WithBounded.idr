||| VerifiedEnum, with more laws for types which also having a MinBound and/or
||| MaxBound implementation
module Data.Enum.Verified.WithBounded

import Data.Fin
import Data.RelVect
import Data.Vect
import Syntax.PreorderReasoning

import Data.Equality.Conversion
import Data.Enum.Verified
import Data.Enum.Verified.Types
import Data.Enum.Verified.Lemmas
-- import Data.Bounded.Verified.Types

%access public export
%default total

%access public export
%default total

------------------------------------------------------------------------------
-- Some preliminaries
------------------------------------------------------------------------------

implementation MinBound ()   where minBound = ()
implementation MaxBound ()   where maxBound = ()
implementation MinBound Bool where minBound = False
implementation MaxBound Bool where maxBound = True

||| Proof that for a given `n`, there exists `m` such that `S m = n`.
NonZero : (n : Nat) -> Type
NonZero n = DPair Nat ((=) n . S)

------------------------------------------------------------------------------
-- VerifiedMin/MaxBoundEnum
------------------------------------------------------------------------------

interface (VerifiedEnum ty, MinBound ty) => VerifiedMinBoundEnum ty where
    ||| `minBound` must be either a fixed point or a wrap point of `pred`
    minBound_valid : IsMin (VerifiedEnum.enumPoints)
                           (Prelude.Interfaces.minBound {b=ty})

interface (VerifiedEnum ty, MaxBound ty) => VerifiedMaxBoundEnum ty where
    ||| `maxBound` must be either a fixed point or a wrap point of `succ`
    maxBound_valid : IsMax (VerifiedEnum.enumPoints)
                           (Prelude.Interfaces.maxBound {b=ty})

||| `Nat` only has a `MinBound`, not a `MaxBound`
implementation VerifiedMinBoundEnum Nat where
    minBound_valid = Refl
            
implementation VerifiedMinBoundEnum () where
    minBound_valid = Refl
        
implementation VerifiedMaxBoundEnum () where
    maxBound_valid = Refl
    
implementation VerifiedMinBoundEnum Bool where
    minBound_valid = Refl

implementation VerifiedMaxBoundEnum Bool where
    maxBound_valid = Refl
    
implementation VerifiedMinBoundEnum (Fin (S n)) where
    minBound_valid = Refl
    
implementation VerifiedMaxBoundEnum (Fin (S n)) where
    maxBound_valid = Refl

------------------------------------------------------------------------------
-- AscendingVect
------------------------------------------------------------------------------

||| Proof type for a `RelVect` that each element is the `succ'` of the element
||| preceeding it.
AscentProof : (succ' : ty -> ty) -> (x : ty) -> (y : ty) -> Type
AscentProof succ' = \x, y => succ' x = y

namespace AscendingVect
    ||| A datatype consisting of:
    ||| 1. A `RelVect` where each element is the `succ` of previous element
    ||| 2. Proof that the first element in that `RelVect` is `minBound'`
    |||
    ||| @n         the number of elements in the vector
    ||| @ty        a type
    ||| @minBound' the first value in the `RelVect`, e.g. `MinBound`
    ||| @succ'     a successor function, as from `Enum`
    data AscendingVect :  (n : Nat)
                       -> (ty : Type)
                       -> (minBound' : ty)
                       -> (succ' : ty -> ty)
                       -> Type where
        MkVect :  (vec : RelVect {a=ty} (S n) (AscentProof succ'))
               -> (prf : head vec = minBound')
               -> AscendingVect (S n) ty minBound' succ'

    ||| Gets the underlying `RelVect` out of an `AscendingVect`
    relVect :  AscendingVect n ty minBound' succ'
            -> RelVect {a=ty} n (\x, y => succ' x = y)
    relVect (MkVect vec _) = vec
    
    ||| Gets the proof that the head of the `RelVect` is `minBound`' out of
    ||| an `AscendingVect`
    headProof :  (x : AscendingVect (S n) ty minBound' succ')
              -> head (relVect x) = minBound'
    headProof (MkVect x prf) = prf

    tail :   AscendingVect (S (S n)) ty a succ'
         ->  AscendingVect (S n) ty (succ' a) succ'
    tail {succ'} (MkVect ((::) b bs {x=succ_b_is_head_bs}) b_is_a) =
        MkVect bs $ (head bs) ={ sym succ_b_is_head_bs }=
                    (succ' b) ={ cong b_is_a           }=
                    (succ' a) QED

------------------------------------------------------------------------------
-- VerifiedCardinality
------------------------------------------------------------------------------

||| Types for which we can prove that `succ` starting from `minBound` reaches
||| every element of that type including `maxBound`
interface (VerifiedMinBoundEnum ty, VerifiedMaxBoundEnum ty) =>
    VerifiedCardinality (n : Nat) ty | ty where
    
    ||| Proof that this type has non-zero cardinality
    CardinalityNonZero : NonZero n

    ||| Every element in `ty`, starting from `minBound`
    All : AscendingVect n ty (minBound {b=ty}) (succ {a=ty})
    
    ||| Proof that `All` actually contains every element of `ty`
    all_valid : (x : ty) -> Elem x (relVect All)

implementation VerifiedCardinality 1 () where
    CardinalityNonZero = (0 ** Refl)
    All                = MkVect [()] Refl
    all_valid ()       = Here
    
implementation VerifiedCardinality 2 Bool where
    CardinalityNonZero = (1 ** Refl)
    All                = MkVect [False, True] Refl
    all_valid False    = Here
    all_valid True     = There Here

------------------------------------------------------------------------------
-- The instance on Fin, which still needs some fixing
------------------------------------------------------------------------------

implementation VerifiedCardinality (S n) (Fin (S n)) where
    CardinalityNonZero {n} = (n ** Refl)

    All                {n} = makeAll n where
            
        makeAll :  (m : Nat)
                -> AscendingVect (S m) (Fin (S m))
                                 (minBound {b=Fin (S m)}) (succ {a=Fin (S m)})
        makeAll Z          = MkVect [FZ] Refl
        makeAll (S Z)      = MkVect [FZ, FS FZ] Refl

       -- For the inductive step, we create the vect of `Fin m` s, then
        -- `rmap FS` onto them to make them all into `Fin (S m)`s
        makeAll (S (S m')) = MkVect ((::) FZ (fst rest) {x=xyPrf}) Refl where
            
            succ_sssm' : Fin (S (S (S m'))) -> Fin (S (S (S m')))
            succ_sssm' = succ
            
            succ_ssm' : Fin (S (S m')) -> Fin (S (S m'))
            succ_ssm' = succ
            
            -- Given proof that (o : Fin (S m')) could be cons'ed onto os,
            -- prove that (r : Fin (S (S m')) could be cons'ed onto rs,
            -- given the definition r = FS o
            prover : RmapProver (AscentProof succ_ssm')
                                (AscentProof succ_sssm') FS
            -- rs is empty, no proof needed
            prover o_prf r [] r_is_FS_o r'_is_FS_o' = ()
            -- The first element in rs is FZ. Impossible, because rs was
            -- generated by applying FS to another vector of elements.
            prover o_prf r ((::) FZ rs' {x}) r_is_FS_o r'_is_FS_o' =
                (\Refl impossible) r'_is_FS_o'
            -- The first element in rs is FS FZ. Impossible, that would
            -- imply that r is FZ, but r is FS _ by definition.
            prover o_prf r ((::) (FS FZ) rs' {x}) r_is_FS_o r'_is_FS_o'
                with (sym $ FSInjective _ _ r'_is_FS_o')
                | o'_is_fz with (trans o_prf o'_is_fz)
                    | succ_o_is_fz = absurd $ succ_not_FZ _ _ succ_o_is_fz
            -- The first element in rs is at least 2
            prover o_prf r ((::) (FS (FS r''')) rs' {x}) r_is_FS_o r'_is_FS_o' =
                sym $
                (FS $ FS r''')      ={ r'_is_FS_o'              }=
                (FS _)              ={ cong $ sym o_prf         }= -- hole is o'
                (FS (succ_ssm' _))  ={ succ_FS_commute (S m') _ }= -- hole is o
                (succ_sssm' (FS _)) QED

            -- The inductive result
            ind : AscendingVect (S (S m')) (Fin (S (S m')))
                                (minBound {b=Fin (S (S m'))}) succ_ssm'
            ind = assert_total $ makeAll (S m')
            
            -- The tail of the result we will return
            rest : DPair (RelVect (S (S m')) (AscentProof succ_sssm'))
                         (RmapProof (AscentProof succ_sssm') FS (relVect ind))
            rest = rmap_ FS prover $ relVect ind
            
            -- The proof that FZ can be cons'ed onto rest.
            -- Not sure why this needs assert_total
            xyPrf : (succ_sssm' FZ = (head $ fst rest))
            xyPrf = assert_total $ sym $
                 (head $ fst rest)         ={ snd rest                    }=
                 (FS $ head $ relVect ind) ={ cong {f=FS} $ headProof ind }=
                 (FS FZ)                   ={ Refl                        }=
                 (succ_sssm' FZ)           QED

     all_valid {n} o = ?all_valid_prf_goes_here
