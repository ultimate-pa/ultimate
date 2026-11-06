// #Safe
/*
 * Author: schuessf@informatik.uni-freiburg.de
 *   Date: 2026-10-15
 */

struct s {
     int arr[1];
};

int main()
{
    struct s *s1 = malloc(sizeof(struct s));
    if (s1 == NULL) return 0;
    s1->arr[0] = 10;
    //@ assert s1->arr[0] == 10;
}
