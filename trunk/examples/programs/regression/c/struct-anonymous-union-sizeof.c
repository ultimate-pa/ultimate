// #Safe
/*-----------------------------------------------------------------------------
 * Test that sizeof works as expected for anonymous structs / unions.
 *-----------------------------------------------------------------------------
 * Author: schuessf@informatik.uni-freiburg.de
 *   Date: 15.10.2026
 *---------------------------------------------------------------------------*/

struct u {
    struct {
        int x;
        int y;
    };
    union {
        long long a;
        int b;
    };
    long z;
};

int main()
{
    if (sizeof(struct u) != 2 * sizeof(int) + sizeof(long long) + sizeof(long)) {
        reach_error();
    }
}
