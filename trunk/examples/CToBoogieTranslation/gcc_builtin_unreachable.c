/*
 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html see for __builtin_unreachable()
 * We should support this function.
 * 
 * Proposal: 
 * - Introduce setting IGNORE/ASSERT
 * IGNORE: Ignore the function (remove) 
 * ASSERT: replace with assert false
 */
void napi_enable() 
{ 
    __builtin_unreachable();
}