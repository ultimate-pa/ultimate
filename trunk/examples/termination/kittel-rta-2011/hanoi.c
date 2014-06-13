/*
 * The Towers Of Hanoi
 * C
 * Copyright (C) 1998 Amit Singh. All Rights Reserved.
 *
 * Tested with, ah well ... :)
 */

#include <stdio.h>
#include <stdlib.h>

#define FROM  1
#define TO    3
#define USING 2

void dohanoi(int N, int from, int to, int using)
{
    if (N > 0) {
        dohanoi(N-1, from, using, to);
        printf ("move %d --> %d\n", from, to);
        dohanoi(N-1, using, to, from);
    }
}

int main (int argc, char **argv)
{
    int N;

    if (argc != 2) {
        fprintf(stderr, "usage: %s N\n", argv[0]);
        return 1;
    }

    N = atoi(argv[1]);

    /* a bit of error checking */
    if (N <= 0) {
        fprintf(stderr, "illegal value for number of disks\n");
        return 2;
    }

    dohanoi(N, FROM, TO, USING);

    return 0;
}
