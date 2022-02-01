/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * Pointer comparison with '0' is not supported.
 */
int main() {
    int c;
    int* pc = &c;
    if (pc == 0) {
        return 1;
    }

    return 0;
}
