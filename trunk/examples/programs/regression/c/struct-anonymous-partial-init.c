// #Safe
/*-----------------------------------------------------------------------------
 * Partial initialization of a struct with anonymous members: members that
 * are not initialized explicitly are zero-initialized (C11 6.7.9.19).
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
    int d;
};

int main()
{
    struct s s1 = { 1, 2 };
    //@ assert s1.a == 1;
    //@ assert s1.b == 2;
    //@ assert s1.c == 0;
    //@ assert s1.d == 0;
}
