This repository provides an example of use of the vscode extension for the Coreact YADE editor (https://github.com/amblafont/vscode-coreact-yade).

A video demonstrating the capabalities of the software for `distributivelaw.v` can be found at https://github.com/amblafont/vscode-yade-example/releases/download/v0.1/demo-yade-example.mp4.

## Requirements
- Coq (tested with v8.20.0)
- Coq-lsp and coreact-yade vscode extensions
- Coq hierarchy builder for the file `distributivelaw.v` 

Here are some installation commands based on opam (https://opam.ocaml.org/doc/Install.html). The above mentioned vscode extensions still need to be installed from vscode.
```
opam pin add coq 8.20.0
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-lsp
```
and `opam install coq-hierarchy-builder` for the file `distributivelaw.v`.


## Instructions
- `make` to compile
- open the directory with vscode
- open the file `example.v` or `distributivelaw.v` (for the latter, `make distributivelaw` first).

## Troubleshootings
Tested on Linux MINT and MacOS.
### Note on MacOS

If the coq-lsp extension fails to start on vscode, try the following.
1) install vscode with homebrew: ``brew install visual-studio-code`
2) If you use opam, run `opam switch` and checks the output (it may instruct you to run an `eval` command to synchronise the shell)
3) run `code .` in the same shell, assuming you are in this directory.
