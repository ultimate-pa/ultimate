int __VERIFIER_nondet_int();
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "psyco_security.c", 4, "reach_error"); }

// method ids
int m_initSign = 1;
int m_initVerify = 2;
int m_Signature = 3;
int m_sign = 4;
int m_verify = 5;
int m_update = 6;
 

int main() {

  int q = 0;
  int method_id;

  // variables
    int this_state = 0;
   

  while (1) {

    // parameters

    // states
        if (q == 0){      
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1 ){ 
                    // record method id
                    method_id = 3;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    this_state=0; 
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
                    if ( (this_state == 2) ) {
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
                  if ( 1 ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( (this_state == 3) ) {
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
                  if ( 1 ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( (((this_state == 2) && (this_state != 3)) || (this_state == 3)) ) {
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
                  if ( 1 ){ 
                    // record method id
                    method_id = 1;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_state=2; 
                  }
                  continue;
                }
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
                    q = 4;
                    // post condition
                    this_state=3; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1 ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (this_state == 2) ) {
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
                  if ( 1 ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( (this_state == 3) ) {
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
                  if ( 1 ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( (((this_state == 2) && (this_state != 3)) || (this_state == 3)) ) {
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
                  if ( 1 ){ 
                    // record method id
                    method_id = 1;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_state=2; 
                  }
                  continue;
                }
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
                    q = 4;
                    // post condition
                    this_state=3; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1 ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (this_state != 2) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_state=this_state; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1 ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( (this_state == 3) ) {
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
                  if ( 1&& (((this_state == 2) && (this_state != 3)) || ((this_state != 2) && (this_state != 3))) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( ((this_state != 2) && (this_state != 3)) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_state=this_state; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& (((this_state == 2) && (this_state != 3)) || ((this_state != 2) && (this_state != 3)))&& ((this_state == 3) || ((this_state != 2) && (this_state != 3))) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( ((this_state != 2) && (this_state != 3)) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_state=this_state; 
                  }
                  continue;
                }

          continue;
        }
        if (q == 4){      
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1 ){ 
                    // record method id
                    method_id = 1;
                    // non-conformance condition 
                    if ( 0 ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_state=2; 
                  }
                  continue;
                }
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
                    q = 4;
                    // post condition
                    this_state=3; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1 ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (this_state == 2) ) {
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
                  if ( 1 ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( (this_state != 3) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 4;
                    // post condition
                    this_state=this_state; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& (((this_state == 2) && (this_state != 3)) || ((this_state != 2) && (this_state != 3))) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( ((this_state != 2) && (this_state != 3)) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 4;
                    // post condition
                    this_state=this_state; 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( 1&& (((this_state == 2) && (this_state != 3)) || ((this_state != 2) && (this_state != 3)))&& ((this_state == 3) || ((this_state != 2) && (this_state != 3))) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( ((this_state != 2) && (this_state != 3)) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 4;
                    // post condition
                    this_state=this_state; 
                  }
                  continue;
                }

          continue;
        }
   

  } // end while

  return 0;

 ERROR:  {reach_error();abort();}
}
