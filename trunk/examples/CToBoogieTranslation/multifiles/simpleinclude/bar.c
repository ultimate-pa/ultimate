#include "foo.h"

int main() {
    // Use a function from the header
    int pick = randomNumber(3);

    // Use a constant from the header
    if (pick == VERIFIED_RANDOM) {
        return 1; // This number is random
    } else {
        return 0; // This number is not known to be random
    }
}
