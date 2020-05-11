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

## Licence and contributions

This tool is distributed under the 2-clause BSD licence in [LICENCE][licence].

This version of the tool was written by Alasdair Armstrong, Thomas Bauereiss,
and Peter Sewell.  Earlier versions had an internal ASL parser instead of using
asl-interpreter;  Alastair Reid, Kathryn Gray, and Anthony Fox contributed to
those versions.

[asli]: https://github.com/rems-project/asl-interpreter
[sail]: https://github.com/rems-project/sail
[sail-www]: https://www.cl.cam.ac.uk/~pes20/sail/
[popl2019]: https://www.cl.cam.ac.uk/~pes20/sail/popl2019.html
[licence]: LICENCE
