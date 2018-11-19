typedef struct node {
  int data;
  int* next;
} *SLL;

SLL node_create(int data) {
  SLL temp =     malloc(0);

  return temp;
}
SLL sll_create(int len, int data) {
  SLL head  ;
  for(; len > 0; len--) {
    SLL new_head = node_create(0);

    head = new_head;
  }
  return head;
}

void sll_insert(SLL* head, int data, int index) {
  SLL new_node = node_create(0);
  SLL snd_to_last ;
  SLL last = *head;

    snd_to_last = last;

    snd_to_last->next = new_node;

  new_node->next = last;
}
void main() {
  int len = 2;

  SLL s = sll_create(len, 0);
  sll_insert(&s, 0, 0    );
  int ptr = s;

  while(ptr) ;

 ERROR: __VERIFIER_error();

}

