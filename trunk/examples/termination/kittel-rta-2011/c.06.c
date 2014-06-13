int nondef(void);

void test_fun(int i, int j, int an, int bn, int cn)
{
    while ((i < an) || (j < bn)) {
        if (i >= an) {
            cn = cn + 1;
            j = j + 1;
        } else {
            if (j >= bn) {
                cn = cn + 1;
                i = i + 1;
            } else {
                if (nondef()) {
                    cn = cn + 1;
                    i = i + 1;
                } else {
                    cn = cn + 1;
                    j = j + 1;
                }
            }
        }
    }
}
