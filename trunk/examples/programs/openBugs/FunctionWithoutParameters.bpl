// #Unsafe
// Reveals of issue #443.
// https://github.com/ultimate-pa/ultimate/issues/443
//
// Functions without parameters are legal in Boogie (see Section 3 of "This is Boogie 2"
// https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml178.pdf)
//
// Boogie and die ICFG distinguish between constants and functions.
// In SMT-LIB constants and 0-ary functions coincide.
// 
// The construction algorithm of the Transformula fails because it expects that
// "myFunction" is a constant.
//
//
// java.lang.AssertionError: not in const set: myFunction
//	at de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.doConstantConsistencyCheck(UnmodifiableTransFormula.java:133)
//	at de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.<init>(UnmodifiableTransFormula.java:110)
//	at de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder.finishConstruction(TransFormulaBuilder.java:272)
//	at de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Statements2TransFormula.constructTransFormula(Statements2TransFormula.java:229)
// 
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2019-08-23

procedure ULTIMATE.start() returns () {
	assert myFunction() >= 23;
}

function myFunction() returns (out : int);

