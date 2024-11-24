# idris-snocvect
SnocVect type and companions.

A Vect type that has the semantics of a reversed vector.

## Usage

You can depend on this package in one of 3 ways.

### Pack
Make sure you have Pack installed, `snocvect` in your package's dependencies
list, and then build your project via Pack.

### Idris install
Clone this repository and run the following commands to install it into your local Idris 2 package directory:
```shell
idris2 --build snocvect.ipkg
idris2 --install snocvect.ipkg
```

Then add it to your project's `ipkg` file under `depends` or use the `-p snocvect` flag when invoking `idris2`.

### Local dependency
Build this package as described under the previous section but instead of installing it to your Idris 2 package directory you can copy the contents of the build/ttc folder into a `depends` directory within your project folder.
