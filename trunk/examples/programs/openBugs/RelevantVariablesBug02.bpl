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
    assume(mem[g] == 0bv32);
    call list_add(g);
    assert mem[0bv32] != 0bv32;
    return;
}

implementation foo(p : bv32) returns (){
    mem := mem[p := 1bv32];
    return;
}

implementation list_add(p : bv32) returns (){
    var tmp : bv32;
    tmp := mem[p];
    call foo(tmp);
    return;
}

var g : bv32;

var mem : [bv32]bv32;

procedure foo(p : bv32) returns ();
modifies mem;

procedure list_add(p : bv32) returns ();
modifies mem;

procedure ULTIMATE.start() returns ();
modifies g, mem;
modifies mem;

