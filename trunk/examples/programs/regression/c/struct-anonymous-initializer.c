// #Safe
/*-----------------------------------------------------------------------------
 * Initialization of a struct with anonymous struct members.
 *-----------------------------------------------------------------------------
 *   Date: 2026-10-15
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
    struct s s2 = { 1, { 2, 3 } };
    struct s s3 = { .z = 3, .y = 2, .x = 1 };
    //@ assert s1.x == 1 && s1.y == 2 && s1.z == 3; 
    //@ assert s2.x == 1 && s2.y == 2 && s2.z == 3; 
    //@ assert s3.x == 1 && s3.y == 2 && s3.z == 3; 
}
