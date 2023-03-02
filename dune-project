(lang dune 3.4)

(name asl_to_sail)

(generate_opam_files true)

(source
 (github rems-project/asl_to_sail))

(authors
  "Alasdair Armstrong"
  "Thomas Bauereiss"
  "Peter Sewell"
  "Brian Campbell")

(maintainers "Sail Devs <cl-sail-dev@lists.cam.ac.uk>")

(license LICENCE)

(package
 (name asl_to_sail)
 (synopsis "ASL to Sail translation tool")
 (description "This tool generates Sail code from ASL specifications. It uses asl-interpreter to parse and type-check ASL.")
 (depends ocaml dune sail asli))
