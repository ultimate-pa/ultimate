//???safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-06-15
 * 
 * Simplified version of RelevantVariablesBug01.c
 * 
 * java.lang.AssertionError: notEqual
 *  at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.RelevantVariables.computePredecessorRvCall_NonPending(RelevantVariables.java:627)
 *  at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.RelevantVariables.computeBackwardRelevantVariables(RelevantVariables.java:501)
 *  at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.RelevantVariables.computeBackwardRelevantVariables(RelevantVariables.java:477)
 *  at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.RelevantVariables.<init>(RelevantVariables.java:76)
 *  at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerSpWp.computeInterpolantsUsingUnsatCore(TraceCheckerSpWp.java:266)
 * 
 * settings/svcomp2017/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf
 * toolchains/AutomizerBpl.xml
 * 
 */


implementation ULTIMATE.start() returns (){
	mem[p] := 0bv32;
    call list_add(p);
	assert (mem[{ base: 0bv32, offset: ~bvadd32(0bv32, 4bv32) }] != 0bv32);
}

type { :isUnsigned false } { :bitsize 32 } C_INT = bv32;


implementation foo(~next : C_INT) returns (){
    mem[{ base: 0bv32, offset: ~bvadd32(~next, 4bv32) }] := 1bv32;
}

implementation list_add(head : $Pointer$) returns (){
    var tmp : C_INT;
    tmp := mem[{ base: head!base, offset: head!offset }];
    call foo(tmp);
}


var p : $Pointer$;


var mem : [$Pointer$]C_INT;


type $Pointer$ = { base : C_INT, offset : C_INT };

procedure foo(#in~next : C_INT) returns ();
modifies mem;

procedure list_add(head : $Pointer$) returns ();
modifies mem;


procedure ULTIMATE.start() returns ();
modifies p, mem;
modifies mem;

function { :builtin "bvadd" } ~bvadd32(in0 : C_INT, in1 : C_INT) returns (out : C_INT);

