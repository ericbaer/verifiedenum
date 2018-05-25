module Data.Enum.Verified.Types

%access public export
%default total

------------------------------------------------------------------------------
-- Special points of pred and succ
------------------------------------------------------------------------------

||| Proof that `x` is a fixed point of `f`
IsFixedPoint : (f : ty -> ty) -> ty -> Type
IsFixedPoint f x = x = f x

||| Proof that `f` has a fixed point
HasFixedPoint : (f : ty -> ty) -> Type
HasFixedPoint {ty} f = DPair ty (IsFixedPoint f)

||| Proof that `x` is a wrap point of `f`, under the given `compare` function
||| We define a 'wrap point' as a value for which the `toNat` of the `pred`
||| (`succ`) is strictly `GT` (`LT`) the `toNat` of the value itself. This
||| means that a `VerifiedEnum` on a unit type must be defined as having a
||| fixed point rather than a wrap point.
IsWrapPoint :  (toNat : ty -> Nat)
            -> (unexpected : Ordering)
            -> (f : ty -> ty)
            -> ty
            -> Type
IsWrapPoint toNat unexpected f x = compare (toNat x) (toNat $ f x) = unexpected

||| Proof that `f` has a wrap point under the given `compare` function.
HasWrapPoint :  (toNat : ty -> Nat)
             -> (unexpected : Ordering)
             -> (f : ty -> ty)
             -> Type
HasWrapPoint {ty} compare unexpected f =
    DPair ty (IsWrapPoint compare unexpected f)

data EnumDirection = Pred | Succ
data EnumCaseTag   = FixedBoth | WrapBoth | InfinitePred | InfiniteSucc
                   | InfiniteBoth
data EnumRecordTag = FixedProof EnumDirection | WrapProof EnumDirection

||| Proof that either `pred` or `succ` (depending on the `EnumDirection`) has a
||| wrap point under the given `compare` function.
WrapPoint :  (d : EnumDirection)
          -> (pred : ty -> ty)
          -> (succ : ty -> ty)
          -> (toNat : ty -> Nat)
          -> Type
WrapPoint Pred pred succ toNat = HasWrapPoint toNat LT pred
WrapPoint Succ pred succ toNat = HasWrapPoint toNat GT succ

||| Type of parameter to `TaggedEnumPoints`
EnumPoint :  EnumRecordTag -> EnumCaseTag -> Type -> Type
EnumPoint (FixedProof Pred) FixedBoth    x = x
EnumPoint (FixedProof Succ) FixedBoth    x = x
EnumPoint (WrapProof  Pred) FixedBoth    x = Not x
EnumPoint (WrapProof  Succ) FixedBoth    x = Not x
EnumPoint (FixedProof Pred) WrapBoth     x = Not x
EnumPoint (FixedProof Succ) WrapBoth     x = Not x
EnumPoint (WrapProof  Pred) WrapBoth     x = x
EnumPoint (WrapProof  Succ) WrapBoth     x = x
EnumPoint (FixedProof Pred) InfinitePred x = Not x
EnumPoint (FixedProof Succ) InfinitePred x = x
EnumPoint (WrapProof  Pred) InfinitePred x = Not x
EnumPoint (WrapProof  Succ) InfinitePred x = Not x
EnumPoint (FixedProof Pred) InfiniteSucc x = x
EnumPoint (FixedProof Succ) InfiniteSucc x = Not x
EnumPoint (WrapProof  Pred) InfiniteSucc x = Not x
EnumPoint (WrapProof  Succ) InfiniteSucc x = Not x
EnumPoint (FixedProof Pred) InfiniteBoth x = Not x
EnumPoint (FixedProof Succ) InfiniteBoth x = Not x
EnumPoint (WrapProof  Pred) InfiniteBoth x = Not x
EnumPoint (WrapProof  Succ) InfiniteBoth x = Not x

record TaggedEnumPoints (ty : Type) (prd : ty -> ty) (suc : ty -> ty)
    (toNat : ty -> Nat) (t : EnumCaseTag) where
    constructor MkPoints
    predFixedPoint : EnumPoint (FixedProof Pred) t (HasFixedPoint prd)
    succFixedPoint : EnumPoint (FixedProof Succ) t (HasFixedPoint suc)
    predWrapPoint  : EnumPoint (WrapProof Pred) t (WrapPoint Pred prd suc toNat)
    succWrapPoint  : EnumPoint (WrapProof Succ) t (WrapPoint Succ prd suc toNat)

------------------------------------------------------------------------------
-- Special points of toNat
------------------------------------------------------------------------------

||| A point, other than fixed or wrap points of `pred`/`succ`, beyond which
||| `toNat` misbehaves. This does not actually prove that `val` is the /first/
||| such point, though.
||| @ty The type
||| @f e.g. `pred` or `succ`; the direction in which the misbehaviour persists
||| @val the first value which exhibits misbehaviour
IsToNatPoint :  (toNat : ty -> Nat)
             -> (f : ty -> ty)
             -> (val : ty)
             -> Type
IsToNatPoint toNat f val = (Not (val = f val), toNat val = toNat (f val))

HasToNatPoint : (toNat : ty -> Nat) -> (f : ty -> ty) -> Type
HasToNatPoint {ty} toNat f = DPair ty (IsToNatPoint toNat f)

ToNatPoint :  (ty : Type)
           -> (prd : ty -> ty)
           -> (toNat : ty -> Nat)
           -> (hasToNatPoint : Bool)
           -> Type
ToNatPoint _ prd toNat True  = HasToNatPoint toNat prd
ToNatPoint _ prd toNat False = Not (HasToNatPoint toNat prd)

------------------------------------------------------------------------------
-- EnumPoints
------------------------------------------------------------------------------

||| A data structure holding proofs about points where the functions in an
||| `Enum` implementation have odd behaviour.
data EnumPoints :  (ty : Type)
                -> (prd : ty -> ty)
                -> (suc : ty -> ty)
                -> (toNat : ty -> Nat)
                -> Type where
    ||| Both `pred` and `succ` have fixed points; `toNat` has no odd behaviour.
    ||| Example: `Fin (S n)` (fixed points at `0` and `n`)
    FixedBothPoints    :  TaggedEnumPoints ty prd suc toNat FixedBoth
                       -> ToNatPoint ty prd toNat False
                       -> EnumPoints ty prd suc toNat
    ||| Both `pred` and `succ` have wrap points; `toNat` has no odd behaviour.
    ||| Example: `Bits8` (wraps at `0` and `255`).
    WrapBothPoints     :  TaggedEnumPoints ty prd suc toNat WrapBoth
                       -> ToNatPoint ty prd toNat False
                       -> EnumPoints ty prd suc toNat
    ||| Both `pred` and `succ` have wrap points; `toNat` has odd behaviour
    ||| at some point and all points accessible from that point with `pred`
    ||| down until the lower wrap point. Example: `Int` (wraps at `2^-63` and
    ||| `2^63-1`; `toNat` gives `Z` on all the negative numbers).
    WrapBothPointsNeg  :  TaggedEnumPoints ty prd suc toNat WrapBoth
                       -> ToNatPoint ty prd toNat True
                       -> EnumPoints ty prd suc toNat
    ||| `pred` has no fixed or wrap point; `succ` has a fixed point; `toNat` has
    ||| odd behaviour at some point and all points accessible from that point
    ||| with `pred`.
    InfinitePredPoints :  TaggedEnumPoints ty prd suc toNat InfinitePred
                       -> ToNatPoint ty prd toNat True
                       -> EnumPoints ty prd suc toNat
    ||| `succ` has no fixed or wrap point; `pred` has a fixed point; `toNat` has
    ||| no odd behaviour. Example: `Nat` itself.
    InfiniteSuccPoints :  TaggedEnumPoints ty prd suc toNat InfiniteSucc
                       -> ToNatPoint ty prd toNat False    
                       -> EnumPoints ty prd suc toNat

    ||| Neither `pred` nor `succ` has a fixed point; `toNat` has odd behaviour
    ||| at some point and all points accessible from that point with `pred`.
    ||| Example: `Integer` (infinite size, but `toNat` gives `Z` on all the
    ||| negative numbers).
    InfiniteBothPoints :  TaggedEnumPoints ty prd suc toNat InfiniteBoth
                       -> ToNatPoint ty prd toNat True
                       -> EnumPoints ty prd suc toNat

------------------------------------------------------------------------------
-- Proof that a value is a special point of an enumeration
------------------------------------------------------------------------------

MinPoint : (c : EnumPoints ty prd suc toNat) -> Maybe ty
MinPoint (FixedBothPoints    pts _) = Just $ fst $ predFixedPoint pts
MinPoint (WrapBothPoints     pts _) = Just $ fst $ predWrapPoint pts
MinPoint (WrapBothPointsNeg  pts _) = Just $ fst $ predWrapPoint pts
MinPoint (InfinitePredPoints pts _) = Nothing
MinPoint (InfiniteSuccPoints pts _) = Just $ fst $ predFixedPoint pts
MinPoint (InfiniteBothPoints pts _) = Nothing

MaxPoint : (c : EnumPoints ty prd suc toNat) -> Maybe ty
MaxPoint (FixedBothPoints    pts _) = Just $ fst $ succFixedPoint pts
MaxPoint (WrapBothPoints     pts _) = Just $ fst $ succWrapPoint pts
MaxPoint (WrapBothPointsNeg  pts _) = Just $ fst $ succWrapPoint pts
MaxPoint (InfinitePredPoints pts _) = Just $ fst $ succFixedPoint pts
MaxPoint (InfiniteSuccPoints pts _) = Nothing
MaxPoint (InfiniteBothPoints pts _) = Nothing

||| Type of a proof that the given value is a minimum point of some enumeration.
||| `Void` where prohibited (when the enumeration has no minimum point).
||| @c proof about some enumeration's behaviour
||| @x a value within the type being enumerated
IsMin : (c : EnumPoints ty prd suc toNat) -> (x : ty) -> Type
IsMin (FixedBothPoints    pts _) x = x = fst $ predFixedPoint pts
IsMin (WrapBothPoints     pts _) x = x = fst $ predWrapPoint pts
IsMin (WrapBothPointsNeg  pts _) x = x = fst $ predWrapPoint pts
IsMin (InfinitePredPoints _   _) _ = Void
IsMin (InfiniteSuccPoints pts _) x = x = fst $ predFixedPoint pts
IsMin (InfiniteBothPoints _   _) _ = Void

||| Type of a proof that the given value is a minimum point of some enumeration.
||| `Void` where prohibited (when the enumeration has no minimum point).
||| @c proof about some enumeration's behaviour
||| @x a value within the type being enumerated
IsFixedMin : (c : EnumPoints ty prd suc toNat) -> (x : ty) -> Type
IsFixedMin (FixedBothPoints    pts _) x = x = fst $ predFixedPoint pts
IsFixedMin (WrapBothPoints     _   _) x = Void
IsFixedMin (WrapBothPointsNeg  _   _) x = Void
IsFixedMin (InfinitePredPoints _   _) _ = Void
IsFixedMin (InfiniteSuccPoints pts _) x = x = fst $ predFixedPoint pts
IsFixedMin (InfiniteBothPoints _   _) _ = Void

||| Type of a proof that the given value is a minimum point of some enumeration.
||| `Void` where prohibited (when the enumeration has no maximum point).
||| @c proof about some enumeration's behaviour
||| @x a value within the type being enumerated
IsMax : (c : EnumPoints ty prd suc toNat) -> (x : ty) -> Type
IsMax (FixedBothPoints    pts _) x = x = fst (succFixedPoint pts)
IsMax (WrapBothPoints     pts _) x = x = fst (succWrapPoint pts)
IsMax (WrapBothPointsNeg  pts _) x = x = fst (succWrapPoint pts)
IsMax (InfinitePredPoints pts _) x = x = fst (succFixedPoint pts)
IsMax (InfiniteSuccPoints _   _) _ = Void
IsMax (InfiniteBothPoints _   _) _ = Void

||| Type of a proof that the given value is a minimum point of some enumeration.
||| `Void` where prohibited (when the enumeration has no maximum point).
||| @c proof about some enumeration's behaviour
||| @x a value within the type being enumerated
IsFixedMax : (c : EnumPoints ty prd suc toNat) -> (x : ty) -> Type
IsFixedMax (FixedBothPoints    pts _) x = x = fst (succFixedPoint pts)
IsFixedMax (WrapBothPoints     _   _) x = Void
IsFixedMax (WrapBothPointsNeg  _   _) x = Void
IsFixedMax (InfinitePredPoints pts _) x = x = fst (succFixedPoint pts)
IsFixedMax (InfiniteSuccPoints _   _) _ = Void
IsFixedMax (InfiniteBothPoints _   _) _ = Void

||| Type of a proof that a given value is below the minimum point at which
||| `toNat` is well-behaved.
BelowToNatMin : (c : EnumPoints ty prd suc toNat) -> (x : ty) -> Type
BelowToNatMin (FixedBothPoints    _ _) _ = Void
BelowToNatMin (WrapBothPoints     _ _) _ = Void
BelowToNatMin {toNat} (WrapBothPointsNeg  _ p) x with (p)
    | (y ** _) = (Not (x = y), toNat x = toNat y)
BelowToNatMin {toNat} (InfinitePredPoints _ p) x with (p)
    | (y ** _) = (Not (x = y), toNat x = toNat y)
BelowToNatMin (InfiniteSuccPoints _ _) _ = Void
BelowToNatMin {toNat} (InfiniteBothPoints _ p) x with (p)
    | (y ** _) = (Not (x = y), toNat x = toNat y)

||| Type of a proof that `x` is a 'special point' of this enumeration `c`.
||| `Void` where prohibited (when the enumeration has no minimum or maximum).
||| @c proof about some enumeration's behaviour
||| @x a value within the type being enumerated
data IsSpecialPoint : (c : EnumPoints ty p s toNat) -> (x : ty) -> Type where
    SpecialMin : IsMin c x -> IsSpecialPoint c x
    SpecialMax : IsMax c x -> IsSpecialPoint c x

