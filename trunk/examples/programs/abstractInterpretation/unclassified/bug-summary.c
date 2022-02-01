typedef struct node {
  int h;
  int  n;
} *List;

void main() {
  List a =      1;
   
  List t;
  List p = a;
  while (__VERIFIER_nondet_int()) {
    p->h = 1;
    t =     malloc(sizeof(int));
     
    p->n = t;
    p = 0;
  }
  p->h = 1;
   
  p = a;
        
    if (p->h != 1) {
      ERROR: __VERIFIER_error();
    }
}
