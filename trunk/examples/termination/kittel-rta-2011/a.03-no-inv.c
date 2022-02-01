void assume(int);
int nondef(void);

void test_fun(int L, int R, int I, int J, int N, int cont)
{
    assume (N >= 2);
    L = nondef();
    assume (N - 2*L >= 0);
    assume (N - 2*L <= 1);
    L = L + 1;
    if (L >= 2) {
        L = L - 1;
    } else {
        R = R - 1;
    }
    while (R >= 2) {
        I = L;
        J = 2*I;
        cont = 1;
        while ((J <= R) && (cont > 0)) {
            if (J <= R - 1) {
                if (nondef()) {
                    J = J + 1;
                } else {
                    
                }
            } else {
                
            }
            if (nondef()) {
                cont = 0;
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
