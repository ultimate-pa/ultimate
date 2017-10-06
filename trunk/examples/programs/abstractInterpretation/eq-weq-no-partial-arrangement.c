/*
 * 2017-10-06: Shows bug in VPDomain WeakEquivalenceGraph: 
 * java.lang.AssertionError: weq edge source is not known to partial arrangement
 *	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeakEquivalenceGraph.sanityCheck(WeakEquivalenceGraph.java:682)
 *	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeakEquivalenceGraph.projectFunction(WeakEquivalenceGraph.java:214)
 *	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.WeqCongruenceClosure.removeSimpleElement(WeqCongruenceClosure.java:791)
 *	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraint.removeElement(EqConstraint.java:377)
 *	at de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory.projectExistentially(EqConstraintFactory.java:331)
 * 
 * Use AbstractInterpretationC.xml and  settings/ai/eq-bench/svcomp-Reach-32bit-Automizer_Camel+AI_EQ.epf with -ea 
 */
void __VERIFIER_error() __attribute__ ((__noreturn__));

struct dummy {
  int a, b;
};

void check(int  ad1, int b)
{
   
}

void main()
{
  struct dummy ad1[1],  ad2;
  int i, j, *pa;

    ad1[0].a = 0;
    pa = &ad1[0].a;
     
       0 < *pa ;  
        check(ad1, 0) ;  

  ERROR: __VERIFIER_error();
   
}
