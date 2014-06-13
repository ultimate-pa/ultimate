void assume(int);

void swap(int *A, int i, int j)
{
    int tmp = A[i];
    A[i] = A[j];
    A[j] = tmp;
}

int get_split(int *A, int begin, int end)
{
    int ptr = begin;
    int split = begin + 1;
    while (++ptr != end) {
        assume(ptr <= end);        
        if (A[ptr] < A[begin]) {
            swap(A, ptr, split);
            ++split;
        }
    }
    return split;
}

void quicksort(int *A, int begin, int end)
{
    int split;
    if (end - begin <= 1)
        return;
    split = get_split(A, begin, end);
    swap(A, begin, split - 1);
    assume(split > begin);
    assume(split <= end);
    quicksort(A, begin, split - 1);
    quicksort(A, split, end);
}
