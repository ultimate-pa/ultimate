/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * Function pointers.
 */
int funcA() {
}

int funcB() {
}

int main() {
    int (* pA)() = &funcA;
    int (* pB)() = &funcB;
}
