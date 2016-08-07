tar -cvf files-wo-proof.tar \
"LICENSE" \
"README" \
"FM9001.announcement" \
"TAGS" \
"intro-overview.ps" \
"files-wo-proof.csh" \
"sysdef.lisp" \
"sysload.lisp" \
"do-files.lisp" \
"do-events-recursive.lisp" \
"disable.lisp" \
"macros.lisp" \
"expand.lisp" \
"vector-macros.lisp" \
"primp-database.lisp" \
"primitives.lisp" \
"control.lisp" \
"expand-fm9001.lisp" \
"monotonicity-macros.lisp" \
"translate.lisp" \
"purify.lisp" \
"bags.events" \
"naturals.events" \
"integers.events" \
"math-disable.events" \
"intro.events" \
"list-rewrites.events" \
"indices.events" \
"hard-specs.events" \
"value.events" \
"memory.events" \
"dual-port-ram.events" \
"fm9001-memory.events" \
"tree-number.events" \
"f-functions.events" \
"dual-eval.events" \
"predicate-help.events" \
"predicate-simple.events" \
"predicate.events" \
"primitives.events" \
"unbound.events" \
"vector-module.events" \
"translate.events" \
"examples.events" \
"example-v-add.events" \
"pg-theory.events" \
"tv-if.events" \
"t-or-nor.events" \
"fast-zero.events" \
"v-equal.events" \
"v-inc4.events" \
"tv-dec-pass.events" \
"reg.events" \
"alu-specs.events" \
"pre-alu.events" \
"tv-alu-help.events" \
"post-alu.events" \
"core-alu.events" \
"fm9001-spec.events" \
"asm-fm9001.events" \
"store-resultp.events" \
"control-modules.events" \
"control.events" \
"regfile.events" \
"flags.events" \
"extend-immediate.events" \
"pad-vectors.events" \
"fm9001-hardware.events" \
"chip.events" \
"expand-fm9001.events" \
"proofs.events" \
"approx.events" \
"final-reset.events" \
"well-formed-fm9001.events" \
"math-enable.events" \
"alu-interpretation.events" \
"flag-interpretation.events" \
"more-alu-interpretation.events" \
"high-level-spec.events" \
"rtl-level-spec.events" \
"dual-eval-spec.events" \
"compressed-netlist.events" \
"predicate.tests"\
"CHIP.NET"

cp files-wo-proof.tar fm9001.tar
gzip -f fm9001.tar

mv files-wo-proof.tar fm9001.tar
compress -f fm9001.tar
