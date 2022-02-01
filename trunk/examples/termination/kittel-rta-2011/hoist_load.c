struct S
{
    int i;
    int j;
};

void f(struct S *s)
{
    int c;
    s->j = 1;
    for (c = 0; c < s->i; ++c) {
        s->j = s->j * c;
    }
}
