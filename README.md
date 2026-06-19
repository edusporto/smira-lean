# smira-lean

Proofs of type soundness (progress and preservation) of the Simple MIRA language [1].

This project translates the original mechanized proofs written in Twelf (available [here](http://compilers.cs.ucla.edu/ralf/twelf/)) into Lean 4. The current implementation is an almost 1:1 translation of the original Twelf logic.

## Report

See the [`report.pdf`](./report.pdf) file in the repository for a report on the project, including information on the original proofs and on the structure of the translations.

## Checking proofs

This project requires an installation of [Lean 4](https://lean-lang.org/install/).

You can check the proofs by running the following command:
```bash
lake build
```

## References

[1] Nandivada, V. Krishna, Fernando Magno Quintão Pereira, and Jens Palsberg. “A Framework for End-to-End Verification and Evaluation of Register Allocators.” In Static Analysis, edited by Hanne Riis Nielson and Gilberto Filé. Springer, 2007. https://doi.org/10.1007/978-3-540-74061-2_10.
