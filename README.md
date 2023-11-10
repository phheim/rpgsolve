# rpgsolve

This is a solving tool, designed when implementing the algorithm for solving [reactive program games](https://arxiv.org/abs/2305.16118).

## Building

You will first need the Haskell build tool [Stack](https://docs.haskellstack.org/en/stable/). Once you have that, you can run
```
    make
```

To build the library and the tools. The build tools will be placed in a new folder, 'builds/'. To get a clean configuration, you can run
```
    make clean
```

## Usage

`rpgsolve` solves reactive program games. The game is read on STDIN, and the result is returned on STDOUT. Log messages are written to STDERR. By default line-cropped log messages are produced and no program extracted. Also the default SMT solver is z3. Possible command line arguments to changes this are:
- `--generate-program` enables program extraction.
- `--disable-log` turns off logging completely.
- `--disable-query-log` disables logging of the SMT queries.
- `--enable-full-log` enables the generation of full-length logs. This option is only recommended for small and easy problems as it might heavily impact performance.
- `--skolemize-only` enables pure Skolemization without explicit quantifier elimination. The default uses quantifier elimination.
- `--smt-solver SOLVER` allows to set the SMT solver (Warning: unstable).


