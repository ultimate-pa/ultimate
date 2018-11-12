/*
 * excerpted from forester-heap/dll-01_false-unreach-call_false-valid-memcleanup.i
 */
#include<stdlib.h>

typedef struct TSLL
{
 struct TSLL* next;
 struct TSLL* prev;
 struct TSLL* inner;
} SLL;

int main() {
   SLL* list = malloc(sizeof(SLL));

   void *p = list->inner->next;

}
