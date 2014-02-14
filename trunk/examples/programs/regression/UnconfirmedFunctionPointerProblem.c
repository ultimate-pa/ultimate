// Matthias: example that might reveal problems in translation
// and verification of the result.
// Delete this example if it seems to be redundant.

extern void *malloc(unsigned long sz );
extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);


struct ssl_st {
   int version ;
};


typedef struct ssl_st SSL;

struct ssl_method_st {
   int (*ssl_connect)(SSL *s ) ;
};


int main(void) 
{ SSL *s = (SSL*)malloc(sizeof(SSL)) ;

  {
  return (0);
}
}