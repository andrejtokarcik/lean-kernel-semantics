# A K semantics of fully elaborated Lean terms

[Lean][1] is an interactive theorem prover based on dependent type theory.  For
additional trust, Lean can [export the generated proofs][2] so that they can be
independently verified.  This is an executable formal semantics of these proofs
(fully elaborated terms) implemented using [K Framework][3].

Update the `RV_PATH` variable in `Makefile` so that it points to the location of
an installed K distribution.  Then run `make` to execute all the tests.
In order to type-check a custom Lean-exported file, copy it to the `lean-kernel-semantics`
top directory, rename the file to `readme.lean-export` and run `make runme`.

[1]: https://leanprover.github.io/
[2]: https://github.com/leanprover/lean/blob/master/doc/export_format.md
[3]: http://www.kframework.org/

## Other checkers

* [trepplein](https://github.com/gebner/trepplein), a type-checker written in Scala.
* [tc](https://github.com/dselsam/tc), a type-checker written in Haskell.
* [leanchecker](https://github.com/leanprover/lean/tree/master/src/checker), a bare-bones version of the Lean kernel.
