
Implementation of refinement type inference
===========================================

This repository contains the source code for my Master's project at the University of Cambridge.

This project implements type checking for LTR, a language based on [Economou et al., 2022. Focusing on Liquid Refinement Typing][1].

Usage
-----

Use Scala SBT to compile the project.

Make sure the Z3 SMT solver is available in PATH before running the type checker.
The main entry point for a REPL interface for the type checker is in `src/main/scala/Main`.
Entering the line `!!path/to/file` will process the file `$(pwd)/path/to/file`.

Some example functions are given in the `lib` directory.
These files must be included in the correct order: `boolean.ltr`, `natural.ltr`, `list.ltr`.
Alternatively, the file `test.ltr` will include the three files in the correct order if the type checker was started from the project root directory.

LTR Syntax
----------

LTR syntax is given in the file `syntax.pdf`.

Benchmarks
----------

The file `src/main/scala/Benchmark` benchmarks the processing of the three example files.
My results are included in the file `benchmark.log`.

[1]: https://arxiv.org/abs/2209.13000 (Economou et al., 2022. Focusing on Liquid Refinement Typing)
