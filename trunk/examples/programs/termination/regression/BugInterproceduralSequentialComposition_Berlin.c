//#nonterminating
/*
 * Date: 2016-09-07
 * Author: Matthias Heizmann
 * 
 */ 
extern int __VERIFIER_nondet_int(void);


void bubblesort() {
    while (1) {
    }
}

int main() {
    int n = __VERIFIER_nondet_int();
     if (n < 1) {
         n = 1;
     }
    int *a = malloc(n * sizeof(int));
    bubblesort();
}

