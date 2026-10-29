// #Safe
/*-----------------------------------------------------------------------------
 * Mixed nesting: an anonymous struct containing an anonymous union, and an
 * anonymous union containing an anonymous struct.
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 14.10.2026
 *---------------------------------------------------------------------------*/

struct s {
    struct {
        int a;
        union {
            int b;
            long c;
        };
    };
    union {
        int d;
        struct {
            int e;
            int f;
        };
    };
};

int main()
{
    struct s s1;
    s1.a = 1;
    s1.b = 2;
    //@ assert s1.a == 1;
    //@ assert s1.b == 2;
    s1.e = 5;
    s1.f = 6;
    //@ assert s1.e == 5;
    //@ assert s1.f == 6;
}
