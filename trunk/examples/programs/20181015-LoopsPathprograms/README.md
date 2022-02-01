Pathprograms dumped with SVCOMP 18 settings
Dump path program if setting did not manage to find perfect interpolant. 

Settings: 
	2d08e6ec3e36004f097ba37155c553f0080c6df7
	../../../trunk/examples/settings/default/automizer/svcomp-Reach-32bit-Automizer_Default.epf
    <option name="--traceabstraction.dump.automata.to.the.following.directory">dump</option>
    <option name="--rcfgbuilder.size.of.a.code.block">SingleStatement</option>
    <option name="--cacsl2boogietranslator.bitprecise.bitfields">false</option>
	Local modification: BasicCegarLoop.DUMP_DIFFICULT_PATH_PROGRAMS = true

SVCOMP:
	71cbe82a5a5422097484cc9a21bd43693a5e4235
    <includesfile>../../../trunk/examples/svcomp/ReachSafety-Loops.set</includesfile>
	
Benchexec
	benchexec/equality-vmcai19-loops-dumppp.xml
