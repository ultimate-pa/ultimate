//#Unsafe
/*
 * Date: 24.9.2020
 * Author: Daniel Dietsch
 * 
 * Bug in function pointer handling. Uninitialized function pointers are not detected. 
 */
int funcA(int x) {
    return 0;
}

int funcB(int x) {
    return 0;
}

int main() {
    int (* pA)(int) = &funcA;
    int (* pB)(int) = &funcB;
    int (* pC)(int);
    int z = pC(1);
    //@assert z == 0;
}
