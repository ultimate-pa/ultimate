#include <stdio.h>
#include <stdlib.h> 

void swap(int *x,int *y)
{
    int temp;
    temp = *x;
    *x = *y;
    *y = temp;
}

void selection_sort(int list[], int n)
{
    int i, j, min;

    for (i = 0; i < n - 1; i++)
    {
        min = i;
        for (j = i+1; j < n; j++)
        {
            if (list[j] < list[min])
            {          
                min = j;
            }
        }
        swap(&list[i], &list[min]);
    }
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
    selection_sort(list,MAX_ELEMENTS);

    // print the result
    printf("The list after sorting:\n");
    printlist(list,MAX_ELEMENTS);

    return 0;
}
