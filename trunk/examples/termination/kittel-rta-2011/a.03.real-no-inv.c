void assume(int);
int nondef(void);

void test_fun(int L, int R, int N)
{
    int I, J;
    assume (N >= 2);
    L = N / 2;
    L = L + 1;
    if (L >= 2) {
        L = L - 1;
    } else {
        R = R - 1;
    }
    while (R >= 2) {
        I = L;
        J = 2*I;
        while (J <= R) {
            if (J <= R - 1) {
                if (nondef()) {
                    J = J + 1;
                }
            }
            if (nondef()) {
                break;
            } else {
                I = J;
                J = 2*J;
            }
        }
        if (L >= 2) {
            L = L - 1;
        } else {
            R = R - 1;
        }
    }
}
