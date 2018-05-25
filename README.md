# verifiedenum

An attempt at figuring out some laws for `Enum`. The implementations on `Fin` were a real (painful) learning experience.

Public interface:

* `Data.Enum.Verified`: some basic laws
* `Data.Enum.Verified.WithOrd`: additional laws for types with an `Ord` implementation
* `Data.Enum.Verified.WithBounded`: additional laws for types with a `MinBound` and/or `MaxBound` instance. Work in progress.

Some internals:

* `Data.Enum.Verified.Types`: some structures for holding proofs of whether given `Enum` implementations have fixed points or other spots where they behave oddly. I hope this exhausts all strange `Enum` behaviour, though I expect to be proven wrong.
* `Data.Enum.Verified.Lemmas`: a bunch of stuff, mostly related to `Fin` 
