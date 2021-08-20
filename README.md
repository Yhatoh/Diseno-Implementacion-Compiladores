# CDI-reference
Starter code for [first OCaml homework](https://users.dcc.uchile.cl/~etanter/CC5116/hw_0_enunciado.html)

## Requirements & Setup

See the [detailed description](https://users.dcc.uchile.cl/~etanter/CC5116/#%28part._materials%29) on the page of the course.

In this homework we're not yet building a compiler, so we just use the OCaml part of the instructions, including `dune` for build management, `alcotest` for testing and `containers` as a library (for parsing s-expressions).

## Organization of the repository

The organization of the repository is as follows 

- `dev/`: source code for the interpreter, separated in several modules: `Ast`, `Parse`, `Interp`, and `Lib`. 
Each module is in its own file (eg. `ast.ml`). See the `dune` file for the declaration of the modules, and the dependencies.
- `execs/`: top-level executables for the interpreter and tests. See the `dune` file for the declaration of the modules, and the dependencies.
- `dune-workspace`, `dune-project`: root configuration for the dune package manager
- `Makefile`: shortcuts to build and test

Dune will build everything inside the `_build/` directory.

## Makefile targets

- `make init`: generate .merlin files for autocompletion in IDE

- `make test`: execute the tests defined in the `Test` module
  variants include: 
  * `make ctest` for compact representation of the tests execution
  * you can also add `F=<pat>` where `<pat>` is a pattern to filter which tests should be executed (eg. `make test F=arith` to run only test files whose name contains `arith`)
  
- `make clean`: cleans everything


## Writing tests

Tests are written using the [alcotest](https://github.com/mirage/alcotest) unit-testing framework. Examples can be found in `execs/test.ml`. *You must add your additional tests to this file.*

Alcotests executes a battery of unit-tests through the `run` function that takes a name (a string) and a list of items to be tested.

Each such item is composed itself from an identifier (a string) together with a list of unit-test obtained with the `test_case` function.
`test_case` takes a description of the test, a mode (either ``` `Quick ``` or ``` `Slow ```---use ``` `Quick ``` by default) and the test itself as a function `unit -> unit`.

A test is built with the `check` function which takes the following parameters:
- a way to test results of type `result_type testable`,
- an error message to be displayed when the test fails,
- the program to be tested, and the expected value (both of type `result_type`)


## Execution

There is a sample source file `example.src`, with a simple expression in it. 
To run it, use `dune exec execs/run.exe prog.src`.

To execute your interpreter interactively, use `dune utop` in a terminal, and then load the interpreter (`open Compiler.Interp;;`).

## Resources

Documentation for ocaml libraries:
- [containers](http://c-cube.github.io/ocaml-containers/last/)
- [alcotest](https://mirage.github.io/alcotest/alcotest/index.html)

