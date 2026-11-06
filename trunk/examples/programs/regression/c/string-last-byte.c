// #Safe
/*
 * Test that the terminating byte of a string is always zero,
 * and that we are also able to check this for long strings that
 * are overapproximated.
 *
 * Author: schuessf@informatik.uni-freiburg.de
 * Date: 2026-11-03
 */

int main()
{
    char* str = "123456789";
    char lastByte = str[9];
    //@ assert lastByte == 0;
}
