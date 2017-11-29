/*
DD 2017-11-29 SMTLIBException: generated interpolants did not pass sanity check

*/

typedef struct TSLL
{
 int  next;

 int data;
} SLL;

void main()
{

 SLL* head  ;

 head->data = 0;

 SLL* x = head;

 x->data = 1;
 x->next = 0;

 x = head;

 while (1 != x->data)
 {
           __VERIFIER_error();

 }

}

