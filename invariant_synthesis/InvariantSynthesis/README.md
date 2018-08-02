# Invariant Synthesis Project

## Structure

  - ``InvariantSynthesis``: Contains the source code for the InvariantSynthesis project (F#).
  - ``InvariantSynthesis_DotNet4``: Contains the project settings for compilation under Windows.
  - ``InvariantSynthesis_Linux``: Contains the project settings for compilation under Linux.
  - ``Parser``: Contains the source code for the IVy Parser (OCaml).
  - ``z3-*``: Contains the binaries for Z3. The linux version is compiled for Ubuntu
  (you can replace it with other binaries if needed).

## Compiling and testing on Linux

### Compiling the parser

The parser must be compiled first. For that, you must have ``opam`` and ``ocamlbuild`` installed
(``ocamlbuild`` can be installed through ``opam`` with the command ``opam install ocamlbuild``).
Then, you just have to run ``make`` in the ``Parser`` folder. If some opam packages are missing,
you can install it with ``opam install <package_name>``.

### Compiling the Invariant Synthesis Project

You must install ``dotnet`` in order to compile and run this project.
You can visit https://docs.microsoft.com/fr-fr/dotnet/core/linux-prerequisites?tabs=netcore2x
for instructions.
Then, just go in the ``InvariantSynthesis_Linux`` folder and run ``make``.
Make sure that the parser has been previously compiled and that the Z3 binaries are compatible with your
linux distribution.

### Testing the project

You can test the project by running ``make test`` in the folder ``InvariantSynthesis_Linux``.
You should specify the path to the IVy code to analyze through the parameter ``ARGS``
(``make test ARGS=/home/.../file.ivy``).