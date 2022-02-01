//Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-06-15
 * 
 * java.lang.AssertionError: notEqual
 *  at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.RelevantVariables.computePredecessorRvCall_NonPending(RelevantVariables.java:627)
 *  at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.RelevantVariables.computeBackwardRelevantVariables(RelevantVariables.java:501)
 *  at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.RelevantVariables.computeBackwardRelevantVariables(RelevantVariables.java:477)
 *  at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.RelevantVariables.<init>(RelevantVariables.java:76)
 *  at de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerSpWp.computeInterpolantsUsingUnsatCore(TraceCheckerSpWp.java:266)
 * 
 * settings/svcomp2017/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf
 * toolchains/AutomizerC.xml
 * 
 */



struct list_head {
 int  next,  prev;
};
 
int gl_list  ;
void inspect(const struct list_head *head)
{

        if (! head->prev     ) __VERIFIER_error();;       

}
void __list_add(int  new,
         int  prev,
         struct list_head *next)
{
 next->prev = 1;

}
 
void list_add(int  new, struct list_head *head)
{
 __list_add(0, 0, head->next);
}
 


void main()
{
    list_add( 0, &gl_list);
    inspect(0);

}
