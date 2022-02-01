 
 
void __VERIFIER_assert(int cond) {
   
   
}
 
int main(     ){
  int n,l,r,i,j;
     
    0 ; {
    i = l;
    j = 2*l;
    while(j <= r) {
      if( j < r) {
 __VERIFIER_assert(1 <= j);
 __VERIFIER_assert(j <= n);
 __VERIFIER_assert(1 <= j+1);
 __VERIFIER_assert(j+1 <= n);
 if( __VERIFIER_nondet_int() )
   j = j + 1;
      }
      __VERIFIER_assert(1 <= j);
      __VERIFIER_assert(j <= n);
      if( __VERIFIER_nondet_int() ) {
       break;
      }
      __VERIFIER_assert(1 <= i);
      __VERIFIER_assert(i <= n);
      __VERIFIER_assert(1 <= j);
      __VERIFIER_assert(j <= n);
      i = j;
      j = 2*j;
    }
    if(l > 1) {
      __VERIFIER_assert(1 <= l);
      __VERIFIER_assert(l <= n);
      l--;
    } else {
      __VERIFIER_assert(1 <= r);
      __VERIFIER_assert(r <= n);
      r--;
    }
  }
   
}
