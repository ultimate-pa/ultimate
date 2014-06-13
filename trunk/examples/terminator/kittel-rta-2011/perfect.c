#include <stdlib.h>
#include <stdio.h>

void assume(int);

/* Copyright 1997 Sourcery Consulting, Uppsala. All rights reserved.
   This program is in the public domain. It may be used,
   redistributed, modified, extended, limited, mangled, thrashed, fed
   to rats, or stomped on as long as this copyright notice is
   maintained.

   There is NO WARRANTY of any sort, it may not work, might kill your
   rats, cause mudslides, make your wife leave you. Who knows. */

int main(int ac, char** av) {
    int j, sum, dcnt, limit, newlimit;
    int number, max;

    if (ac != 2) {
        fprintf(stderr, "Usage: %s <number>\n", av[0]);
        return 2;
    } else {
        max = atoi(av[1]);
    }

    /* Optimization: we can skip odd numbers, these are never perfect (proof?). */
    for (number = 2 ; number < max ; number += 2) {
        /* Optimization: We only need to search to half the range for divisors. */
        dcnt = sum = j = 0;
        limit = number;
        while (++j < limit) {
            if (number % j == 0) {
                sum += j;
                dcnt++;
                /* Optimization: Each time we find a divisor we get one for 
                 free. We can then decrease the upper limit to the higher of
                 the divisors. */
                if (number / j != number) {
                    sum += number / j;
                    newlimit = number / j;
                    assume (newlimit < limit);
                    limit = newlimit;
                    dcnt++;
                }
            }
        }

        if (sum == number)
            printf("%4d : perfect!\t\t%4d divisors\n", number, dcnt);
#ifndef ONLY_PERFECT
        else
            printf("%4d : NOT perfect\t%4d divisors\n", number, dcnt);
#endif
    }

    return 0;
}
