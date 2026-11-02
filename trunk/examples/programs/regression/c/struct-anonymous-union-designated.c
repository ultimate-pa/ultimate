// #Safe
/*-----------------------------------------------------------------------------
 * Designated initializer for a member of an anonymous union member of a
 * union (C11 6.7.9.9: the initializer initializes the member of the
 * anonymous union, the remaining members of the union are initialized
 * like in a struct).
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
    union u u1 = { .x = 1, .y = 2 };
    //@ assert u1.x == 1;
    //@ assert u1.y == 2;
}
