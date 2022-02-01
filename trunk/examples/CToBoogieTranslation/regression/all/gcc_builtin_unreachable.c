//#Safe
/*
 * 2016-12-12 DD
 * 
 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html see for __builtin_unreachable()
 * We should support this function.
 * 
 * Proposal: 
 * Introduce setting IGNORE/ASSERT/ASSUME 
 * IGNORE: Ignore the function (remove) 
 * ASSERT: replace with assert false
 * ASSUME: replace with assume false 
 * 
 * Current solution: replace with assume false (best for us)
 */
void napi_enable() 
{ 
    __builtin_unreachable();
	__VERIFIER_error();
}