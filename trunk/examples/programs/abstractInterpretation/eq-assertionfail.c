//#Safe 
/*
 * 2017-10-12 Dietsch: Example for assertion error in WeqCongruenceClosure
 * Run with 
 *  AbstractInterpretationC.xml
 *  ai/eq-bench/svcomp-Reach-32bit-Automizer_Taipan+AI_EQ.epf
 *  
 * java.lang.AssertionError
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.WeqCongruenceClosure.elementIsFullyRemoved(WeqCongruenceClosure.java:1086)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.EqConstraint.removeElement(EqConstraint.java:380)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.EqConstraintFactory.projectExistentially(EqConstraintFactory.java:328)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.EqState.removeVariables(EqState.java:106)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.EqState.removeVariables(EqState.java:1)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider.applyLocals(RcfgVariableProvider.java:227)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider.removeLocals(RcfgVariableProvider.java:213)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider.defineVariablesAfterReturn(RcfgVariableProvider.java:159)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider.defineVariablesAfter(RcfgVariableProvider.java:107)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider.defineVariablesAfter(RcfgVariableProvider.java:1)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.DisjunctiveAbstractState.lambda$13(DisjunctiveAbstractState.java:309)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.DisjunctiveAbstractState.crossProduct(DisjunctiveAbstractState.java:401)
 *  	at de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.DisjunctiveAbstractState.defineVariablesAfter(DisjunctiveAbstractState.java:309)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine.calculateAbstractPost(FixpointEngine.java:237)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine.calculateFixpoint(FixpointEngine.java:134)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine.run(FixpointEngine.java:105)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter.runFuture(AbstractInterpreter.java:190)
 *  	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.AbstractInterpretationRcfgObserver.process(AbstractInterpretationRcfgObserver.java:71)
 */

void main() {
     
    int k;
     
    if (!(0 <= k    )) ;

}