/*
 * 2016-12-12 DD
 * ClassCastException: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListResult cannot be cast to de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult
 *
 * Extracted from svcomp/loop-industry-pattern/aiob_1_true-unreach-call.c
 *
 * Ok according to gcc -std=c11 --pedantic (4.9.3)
 * __VERIFIER_assert(int i) can be defined as expected; ommited for brevity 
 */
int main()
{
	("14_6632_4294986964" , __VERIFIER_assert(0));
}