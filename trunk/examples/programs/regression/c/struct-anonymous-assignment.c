// #Safe
/*-----------------------------------------------------------------------------
 * Struct assignment (copy) with anonymous members, both on the stack and on
 * the heap.
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

int main()
{
    struct s s1 = { 1, 2, 3 };
    struct s s2 = s1;
    //@ assert s2.a == 1;
    //@ assert s2.b == 2;
    //@ assert s2.c == 3;
    struct s *p1 = malloc(sizeof(struct s));
    if (p1 == NULL) {
        return -1;
    }
    p1->a = 4;
    p1->b = 5;
    p1->c = 6;
    struct s *p2 = malloc(sizeof(struct s));
    if (p2 == NULL) {
        return -1;
    }
    *p2 = *p1;
    //@ assert p2->a == 4;
    //@ assert p2->b == 5;
    //@ assert p2->c == 6;
    return 0;
}
