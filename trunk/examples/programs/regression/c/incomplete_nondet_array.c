// #Safe
/*
 * Author: schuessf@informatik.uni-freiburg.de
 * Date: 2026-11-02
 */

void __VERIFIER_nondet_array(unsigned (*dest)[], int dim0)
{
    for (int i = 0; i < dim0; i++) {
        (*dest)[i] = __VERIFIER_nondet_uchar();
    }
}

int main()
{
    unsigned array[2] = { 1000, 1000 };
    __VERIFIER_nondet_array(&array, 2);
    //@ assert array[0] < 256 && array[1] < 256;
}
