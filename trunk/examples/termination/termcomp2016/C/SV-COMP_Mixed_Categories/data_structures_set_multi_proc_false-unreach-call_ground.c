extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
int insert( int set [] , int size , int value ) {
  set[ size ] = value;
  return size + 1;
}
int elem_exists( int set [ ] , int size , int value ) {
  int i;
  for ( i = 0 ; i < size ; i++ ) {
    if ( set[ i ] == value ) return 0;
  }
  return 0;
}
int main( ) {
  int n = 0;
  int set[ 100000 ];
  int x;
  int y;
  for ( x = 0 ; x < n ; x++ ) {
    for ( y = x + 1 ; y < n ; y++ ) {
      __VERIFIER_assert( set[ x ] != set[ y ] );
    }
  }
  int values[ 100000 ];
  int v;
  for ( v = 0 ; v < 100000 ; v++ ) {
    if ( !elem_exists( set , n , values[ v ] ) ) {
      n = insert( set , n , values[ v ] );
    }
  }
  for ( x = 0 ; x < n ; x++ ) {
    for ( y = x + 1 ; y < n ; y++ ) {
      __VERIFIER_assert( set[ x ] != set[ y ] );
    }
  }
  return 0;
}
