// #Safe
/*-----------------------------------------------------------------------------
 * Global (static storage) initialization of a struct with anonymous members.
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 14.10.2026
 *---------------------------------------------------------------------------*/

struct s {
    int a;
    struct {
        int b;
        int c;
    };
};

struct s g = { 1, 2, 3 };

int main()
{
    //@ assert g.a == 1;
    //@ assert g.b == 2;
    //@ assert g.c == 3;
}
