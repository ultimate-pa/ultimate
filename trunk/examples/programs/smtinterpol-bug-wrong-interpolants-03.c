/*
DD 2017-11-29
Generated interpolants did not pass sanity check

*/

typedef struct node {
  int val;
  int  next;
} node_t;
void* new_ll(int n)
{
  if (n == 0)
    return 0;
  node_t* head = malloc(sizeof(node_t));
  head->val = 0;
  head->next = new_ll(n-1);
  return head;
}

void  append(node_t* x, int  y)
{

  while (x->next    )
    ;

}
int main ()
{
  int n  ;
  if (n < 0) {
      return 0;
  }
  int* x = new_ll(1);
    new_ll(n);
    append(x, 0);

}

