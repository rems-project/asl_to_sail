# ASL to Sail

## Building

This tool generates [Sail][sail] code from ASL specifications.  It uses
[asl-interpreter][asli] to parse and type-check ASL.  Earlier versions of this
tool had an internal ASL parser;  Alastair Reid, Kathryn Gray, and Anthony Fox
contributed to those versions.

With asl-interpreter (at least version a896dd1) and Sail (at least version
b9860a9bc) installed, use *make* to build the tool.

## Usage

Make sure that asl-interpreter can parse and type-check the ASL files you want
to translate, and then call this tool with the list of files.

### Patching

If we encounter things in the ASL that can't be converted to sail
automatically, they need *patching*. ASL parser is interactive, when it
encounters a bad definition it will show the ASL code, the translated sail
code, a trace showing why the translated code didn't typecheck and the type
error. There are various options available, but the most useful is to open an
editor with the patch and manually edit it - for this either the $VISUAL or
$EDITOR environment variables must be set. By default patches are stored in the
patches/ directory (which you may need to create). A custom patch directory can
also be used.

[asli]: https://github.com/rems-project/asl-interpreter
[sail]: https://github.com/rems-project/sail
