/* #Safe
 *-----------------------------------------------------------------------------
 * Example with (nested) anonymous structs in an outer struct as part of a typedef
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 14.11.2025
 *---------------------------------------------------------------------------*/

typedef struct {
    int a;
    struct {
        int b;
    };
    struct {
        struct {
            int c;
        };
        int d;
    };
} foo_t;

int main()
{
    foo_t f;
    f.a = 10;
    f.b = 20;
    f.c = 30;
    f.d = 40;
    int a = f.a;
    int b = f.b;
    int c = f.c;
    int d = f.d;
    //@ assert (a == 10 && b == 20 && c == 30 && d == 40);
    return f.a + f.b + f.c + f.d;
}
