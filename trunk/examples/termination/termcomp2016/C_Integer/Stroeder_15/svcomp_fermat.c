//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int MAX;
    int a, b, c;
    MAX = 1000;
    a = 1;
    b = 1;
    c = 1;
    while (((a*a*a) != ((b*b*b)+(c*c*c))) && c <= MAX) {
        a = a + 1;
        if (a>MAX) {
            a = 1;
            b = b + 1;
        }
        if (b>MAX) {
            b = 1;
            c = c + 1;
        }
    }
    return 0;
}
