/**
 * 2017-10-18 DD: Example for "unknown constant" bug in SSD quantifier elimination 
 * Run with
 *   -tc examples/toolchains/AutomizerC.xml
 *   -s  examples/settings/ai/eq-bench/svcomp-Reach-32bit-Automizer_Taipan+AI_EQ.epf 
 *   -i  examples/svcomp/array-examples/standard_running_true-unreach-call.i
 *
 * Exception:
 *   de.uni_freiburg.informatik.ultimate.logic.SMTLIBException: line 17728 column 26: unknown constant v_prenex_2
 *  	at de.uni_freiburg.informatik.ultimate.smtsolver.external.Parser$Action$.CUP$do_action(Parser.java:1362)
 *  	at de.uni_freiburg.informatik.ultimate.smtsolver.external.Parser.do_action(Parser.java:582)
 *  	at com.github.jhoenicke.javacup.runtime.LRParser.parse(LRParser.java:419)
 *  	at de.uni_freiburg.informatik.ultimate.smtsolver.external.Executor.parse(Executor.java:206)
 *  	at de.uni_freiburg.informatik.ultimate.smtsolver.external.Executor.parseSuccess(Executor.java:222)
 *  	at de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor.assertTerm(Scriptor.java:146)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript.assertTerm(ManagedScript.java:133)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IncrementalPlicationChecker.checkPlication(IncrementalPlicationChecker.java:120)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Elim1Store.checkEqualityStatus(Elim1Store.java:617)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Elim1Store.analyzeIndexEqualities(Elim1Store.java:709)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Elim1Store.elim1(Elim1Store.java:285)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ElimStorePlain.doElimOneRec(ElimStorePlain.java:219)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ElimStorePlain.doElimAllRec(ElimStorePlain.java:240)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ElimStorePlain.elimAllRec(ElimStorePlain.java:198)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination.elim(PartialQuantifierElimination.java:270)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination.tryToEliminate(PartialQuantifierElimination.java:101)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer$QuantifierEliminationPostprocessor.postprocess(IterativePredicateTransformer.java:243)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.applyPostprocessors(IterativePredicateTransformer.java:445)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.computeStrongestPostconditionSequence(IterativePredicateTransformer.java:198)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckSpWp.computeInterpolantsUsingUnsatCore(TraceCheckSpWp.java:283)
 */

void __VERIFIER_assert(int cond) {       ERROR: __VERIFIER_error();   }
void main ( ) {
  int a[1];
   
  int i = 0;
  while ( i < 100000 ) {
    if ( a[i] >= 0 ) ;
    else ;
    i = i + 1;
  }
   
  i = 0;
  while ( i < 100000 ) {
     
    if ( a[i] < 0     ) ;
    i = i + 1;
  }
  __VERIFIER_assert ( 0 );
   
}