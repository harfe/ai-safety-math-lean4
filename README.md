# Formalized AI Safety Math Collection

A collection of mathematical definitions, theorem statements and conjectures in AI safety,
formalized in Lean 4.

## Articles

In `Articles/` is a collection of brief mathematical articles.
These follow some (cited) source material, but focus on a brief but mathematical
description of the core definitions and theorem statements,
while omitting proofs and intuitions.

### Topics covered so far

- Quantilizers
- A conjecture about Natural Latents
- Small parts of Infra-Bayesianism

## Targets

For each article, there exists a corresponding `.lean` file in `AISafetyMath/Targets`.
The `.lean` file follows the `.md` file.
These target files focus on definitions and theorem statements,
with most of the proofs replaced by `sorry`.
There are also some additional sanity check lemmas,
to provide additional evidence that the definitions are correct.
These target `.lean` files are human-written.

## Solutions

Some target files have corresponding solution files
in `AISafetyMath/Solutions` which contain the proofs
(or import other solution files which contain the proofs).
These proofs are often AI-generated (but verified).

## Getting started

This section assumes you have already [installed Lean](https://lean-lang.org/install/).

Run `lake exe cache get` to avoid compiling the entirety of Mathlib.
You can then run `lake build`, which would build the target (but not solution) files.
Note  that the target files contain a lot of `sorry`.

## Verifying solutions with Comparator

To verify that the Solutions are correct and match the Target file
we use the [Comparator](https://github.com/leanprover/comparator) tool.
The required configuration files for Comparator are in `comparator_configs`.

Note that Comparator recommends to not build solution files,
to defend against solution files changing the target files or other parts of the system.
Comparator itself builds solution files only in a sandbox.

Once you have installed comparator and the binary is in `$PATH`,
you can execute `./scripts/run_comparator.sh` or
you can run comparator for individual targets with
```
$ lake env comparator comparator_configs/Quantilizers.json
```
where `Quantilizers.json` can be replaced with any `.json` file in that directory.

