int __VERIFIER_nondet_int();
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "psyco_io_1.c", 4, "reach_error"); }

// method ids
int m_flush = 1;
int m_PipedOutputStream = 2;
int m_close = 3;
int m_write = 4;
int m_connect_1 = 5;
int m_connect_2 = 6;
 

int main() {

  int q = 0;
  int method_id;

  // variables
    int this_sink = 0;
    int this_sinkConnected = 0;
   

  while (1) {

    // parameters
        int P1=__VERIFIER_nondet_int();
        int P2=__VERIFIER_nondet_int();
        int P3=__VERIFIER_nondet_int();
        int P4=__VERIFIER_nondet_int();


    // states
        if (q == 0){      
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1 ){ 
                    // record method id
                    method_id = 2;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    this_sink=0; this_sinkConnected=0; 
                  }
                  continue;
                }

          continue;
        }
        if (q == 1){      
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1 ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (this_sink != 0) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 1;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P2 != 1) && (P1 != 0)) ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( ((P2 != 1) && ((this_sink == 0) && (P1 != 0))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 1;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !((P2 != 1) && (P1 != 0)) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 1;
                    // post condition
                    break;
                  }
                  continue;
                }

          continue;
        }
        if (q == 2){      
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& ((this_sink != 0) || 0) ){ 
                    // record method id
                    method_id = 1;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    this_sink=this_sink; this_sinkConnected=this_sinkConnected; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& ((this_sink != 0) || 0)&& ((this_sink == 0) || 0) ){ 
                    // record method id
                    method_id = 1;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    this_sink=this_sink; this_sinkConnected=this_sinkConnected; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& ((this_sink != 0) || 0) ){ 
                    // record method id
                    method_id = 3;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    this_sink=this_sink; this_sinkConnected=this_sinkConnected; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& ((this_sink != 0) || 0)&& ((this_sink == 0) || 0) ){ 
                    // record method id
                    method_id = 3;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    this_sink=this_sink; this_sinkConnected=this_sinkConnected; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1 ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (this_sink != 0) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 1;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P2 != 1) && (P1 != 0)) ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( (((this_sink != 0) && (P1 != 0)) && ((P2 != 1) && (P1 != 0))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_sink=P1; this_sinkConnected=1; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !((P2 != 1) && (P1 != 0)) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 1;
                    // post condition
                    break;
                  }
                  continue;
                }

          continue;
        }
        if (q == 3){      
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& ((this_sink != 0) || 0) ){ 
                    // record method id
                    method_id = 1;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_sink=this_sink; this_sinkConnected=this_sinkConnected; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& ((this_sink != 0) || 0)&& ((this_sink == 0) || 0) ){ 
                    // record method id
                    method_id = 1;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_sink=this_sink; this_sinkConnected=this_sinkConnected; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& ((this_sink != 0) || 0) ){ 
                    // record method id
                    method_id = 3;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_sink=this_sink; this_sinkConnected=this_sinkConnected; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& ((this_sink != 0) || 0)&& ((this_sink == 0) || 0) ){ 
                    // record method id
                    method_id = 3;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_sink=this_sink; this_sinkConnected=this_sinkConnected; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1 ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (this_sink == 0) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_sink=this_sink; this_sinkConnected=this_sinkConnected; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P2 != 1) && (P1 != 0)) ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( ((P2 != 1) && ((this_sink == 0) && (P1 != 0))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 1;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !((P2 != 1) && (P1 != 0)) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 1;
                    // post condition
                    break;
                  }
                  continue;
                }

          continue;
        }
   

  } // end while

  return 0;

 ERROR:  {reach_error();abort();}
}
