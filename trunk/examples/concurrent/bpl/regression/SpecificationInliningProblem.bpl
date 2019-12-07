//#Safe
/*
 * Our BoogieProcedureInliner translates the call of the increment 
 * procedure into the following lines.
 *       increment_old_g := g;
 *       assume { :begin_inline_increment } true;
 *       havoc g;
 *       assume g == increment_old_g + 1;
 *       assume { :end_inline_increment } true;
 * 
 * This is a problem our analysis of concurrent programs because the
 * analysis allows a context switch after the havoc.
 * 
 * We can avoid the problem if we switch of the inlining for procedures
 * that do not have an implementation.
 *
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-10-28
 * 
 */

var g : int;


procedure ULTIMATE.start() returns ()
modifies g;
{
	g := 2;
	fork 23 pineappleThread();
	assert g == 2 || g == 3;
}

procedure pineappleThread() returns ()
modifies g;
{
	call increment();
}

procedure increment() returns ();
ensures g == old(g) + 1;
modifies g;






