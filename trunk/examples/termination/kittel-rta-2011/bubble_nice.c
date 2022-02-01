#include <stdio.h>
#include <stdlib.h>

void swap(int *x, int *y)
{
    int temp;
    temp = *x;
    *x = *y;
    *y = temp;
}

void bublesort(int list[], int n)
{
    int i,j;
    for(i=0;i<(n-1);i++)
        for(j=0;j<(n-(i+1));j++)
            if(list[j] > list[j+1])
                swap(&list[j],&list[j+1]);
}

void printlist(int list[],int n)
{
    int i;
    for(i=0;i<n;i++)
        printf("%d\t",list[i]);
}

int main()
{
    const int MAX_ELEMENTS = 10;
    int list[MAX_ELEMENTS];

    int i = 0;
    
    // generate random numbers and fill them to the list
    for(i = 0; i < MAX_ELEMENTS; i++ )
        list[i] = rand();

    printf("The list before sorting is:\n");
    printlist(list,MAX_ELEMENTS);

    // sort the list
    bublesort(list,MAX_ELEMENTS);

    // print the result
    printf("The list after sorting using bubble sorting algorithm:\n");
    printlist(list,MAX_ELEMENTS);

    return 0;
}
