//#Safe

/*
 * Test duplicate typedefs, see also C11 6.7.3.
 *
 * Date: 2026-10-02
 * Author: schuessf@informatik.uni-freiburg.de
 */

typedef signed char __int8_t;
typedef signed char int8_t;
typedef __int8_t int8_t;

int main();
