// #Safe
/*-----------------------------------------------------------------------------
 * Anonymous struct member that is not the first member, accessed via a heap
 * object (pointer). Checks that the offset of the anonymous member is
 * computed correctly on the heap.
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 14.10.2026
 *---------------------------------------------------------------------------*/

struct s {
    int a;
    struct {
        int b;
    };
    int c;
};

int main()
{
    struct s *p = malloc(sizeof(struct s));
    if (p == NULL) {
        return -1;
    }
    p->a = 1;
    p->b = 2;
    p->c = 3;
    //@ assert p->a == 1;
    //@ assert p->b == 2;
    //@ assert p->c == 3;
}
