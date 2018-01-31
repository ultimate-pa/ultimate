#include "foo.h"

int (*src)(int) = randomNumber;

int main() {
    // Use a function from the header
    int pick = randomNumber(3);
    
    // Test function pointers to check their syntax.
    int otherPick = src(4);

    // Use a constant from the header
    if (pick == VERIFIED_RANDOM) {
        return 1; // This number is random
    } else {
        return 0; // This number is not known to be random
    }
}
