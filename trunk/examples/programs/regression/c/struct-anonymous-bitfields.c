// #Safe
/*-----------------------------------------------------------------------------
 * Bitfields inside an anonymous struct member.
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 14.10.2026
 *---------------------------------------------------------------------------*/

struct s {
    int a;
    struct {
        int b : 3;
        int c : 5;
    };
};

int main()
{
    struct s s1;
    s1.a = 7;
    s1.b = 5;
    s1.c = 17;
    //@ assert s1.a == 7;
    //@ assert s1.b == 5;
    //@ assert s1.c == 17;
    return 0;
}
