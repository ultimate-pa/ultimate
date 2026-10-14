// #Safe
/*-----------------------------------------------------------------------------
 * Positional and designated initializers assign the same values to a struct
 * with anonymous struct members.
 *-----------------------------------------------------------------------------
 *   Date: 2026-10-13
 * Author: schuessf@informatik.uni-freiburg.de
 *---------------------------------------------------------------------------*/

struct s {
    int x;
    struct {
        int y;
        int z;
    };
};

int main()
{
    struct s s1 = { 1, 2, 3 };
    struct s s2 = { .z = 3, .y = 2, .x = 1 };
    //@ assert s1.x == s2.x;
    //@ assert s1.y == s2.y;
    //@ assert s1.z == s2.z;
    return 0;
}
