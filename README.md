# ASL to Sail

This tool generates [Sail][sail] code from ASL specifications.  It uses
[asl-interpreter][asli] to parse and type-check ASL.

For more information, see the [Sail web page][sail-www] and the paper:

[ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS][popl2019]. Alasdair
Armstrong, Thomas Bauereiss, Brian Campbell, Alastair Reid, Kathryn E. Gray,
Robert M. Norton, Prashanth Mundkur, Mark Wassell, Jon French, Christopher
Pulte, Shaked Flur, Ian Stark, Neel Krishnaswami, and Peter Sewell. In POPL
2019, Proc. ACM Program. Lang. 3, POPL, Article 71.

## Building

With [asl-interpreter][asli] (at least version a896dd1) and [Sail][sail] (at
least version b9860a9bc) installed, use *make* to build the tool.

## Usage

Make sure that asl-interpreter can parse and type-check the ASL files you want
to translate, and then call this tool with the list of files.

### Patching

If we encounter things in the ASL that can't be converted to sail
automatically, they need *patching*. The tool is interactive, when it
encounters a bad definition it will show the ASL code, the translated sail
code, a trace showing why the translated code didn't typecheck and the type
error. There are various options available, but the most useful is to open an
editor with the patch and manually edit it - for this either the $VISUAL or
$EDITOR environment variables must be set. By default patches are stored in the
patches/ directory (which you may need to create). A custom patch directory can
also be used.

### Overrides

If there are multiple definitions of a function in the ASL sources the desired
one can be specified using an overrides file and option.  Each line of an
overrides file names a function and the file that its definition should be
taken from, separated by a space.

## Licence and contributions

This tool is distributed under the 2-clause BSD licence in [LICENCE][licence].

This version of the tool was written by Alasdair Armstrong, Thomas Bauereiss,
and Peter Sewell.  Earlier versions had an internal ASL parser instead of using
asl-interpreter;  Alastair Reid, Kathryn Gray, and Anthony Fox contributed to
those versions.

## Funding

This software was developed within the Rigorous Engineering of
Mainstream Systems (REMS) project, partly funded by EPSRC grant
EP/K008528/1, at the University of Cambridge.
This project has received funding from the European Research Council (ERC)
under the European Union’s Horizon 2020 research and innovation programme
(grant agreement No 789108, ELVER).
This software was developed by the University of
Cambridge Computer Laboratory (Department of Computer Science and
Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV").

[asli]: https://github.com/rems-project/asl-interpreter
[sail]: https://github.com/rems-project/sail
[sail-www]: https://www.cl.cam.ac.uk/~pes20/sail/
[popl2019]: https://www.cl.cam.ac.uk/~pes20/sail/popl2019.html
[licence]: LICENCE
