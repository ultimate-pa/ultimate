//#Safe
/*
 * Date: 2025-05-05
 * Author: bentele@informatik.uni-freiburg.de
 *
 * See https://github.com/ultimate-pa/ultimate/issues/715
 */

int main(void)
{
    int b = 0b00000001;
    //@ assert b == 1;

    return 0;
}
