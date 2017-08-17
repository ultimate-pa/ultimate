//#termcomp16-someonesaidyes
//#termcomp16-someonesaidyes
/* An example that looks simple, given to me by Genady Trifon
 * Date: 15.12.2013
 * Author: Amir Ben-Amram, amirben@cs.mta.ac.il
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int i, j;
    j = 1;
    i = 10000;
    while (i-j >= 1) {
        j = j + 1;
        i = i - 1;
    }  
    return 0;
}
