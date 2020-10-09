# LambdaCompiler
## Building
### Prerequisites
The only dependency should be the Haskell Tool Stack.
See https://docs.haskellstack.org/en/stable/README/, or https://www.archlinux.org/packages/community/x86_64/stack/.
    
### Running the build
Simply run `make` to build the executable (which currently is `_build/bin/lambdac`) . Alternatively, you can execute `make run` in order to
additionally call `lambdac` if it was successfully compiled. You can run `make clean` to delete all files created by the build.

### Explanations
The build is run using a custom build system, MetaBuilder. It has to be first compiled from its source in `buildsystem/MetaBuilder`.
This is done the first time you run any `make` command automatically. And every subsequent call checks if MetaBuilder needs to be rebuild,
and does so automatically as well.
