// #Safe
/*-----------------------------------------------------------------------------
 * Union with an anonymous struct member and an additional named union member.
 * Writing to the anonymous struct member must not change the named member
 * (they are distinct storage in the union).
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 14.10.2026
 *---------------------------------------------------------------------------*/

union u {
    struct {
        int x;
        int y;
    };
    long z;
};

int main()
{
    union u u1;
    u1.x = 1;
    u1.y = 2;
    //@ assert u1.x == 1;
    //@ assert u1.y == 2;
    u1.z = 0;
    //@ assert u1.x == 0;
    return 0;
}
