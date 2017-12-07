int __VERIFIER_nondet_int();
extern void __VERIFIER_error() __attribute__((noreturn));

// method ids
int m_Protocol = 1;
int m_msg_2 = 2;
int m_recv_ack_2 = 3;
int m_msg_1_1 = 4;
int m_msg_1_2 = 5;
int m_recv_ack_1_1 = 6;
int m_recv_ack_1_2 = 7;
 

int main() {

  int q = 0;
  int method_id;

  // variables
    int this_expect = 0;
    int this_buffer_empty = 0;
   

  while (1) {

    // parameters
        int P1=__VERIFIER_nondet_int();
        int P2=__VERIFIER_nondet_int();
        int P3=__VERIFIER_nondet_int();
        int P4=__VERIFIER_nondet_int();
        int P5=__VERIFIER_nondet_int();
        int P6=__VERIFIER_nondet_int();
        int P7=__VERIFIER_nondet_int();
        int P8=__VERIFIER_nondet_int();
        int P9=__VERIFIER_nondet_int();


    // states
        if (q == 0){      
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
                    q = 1;
                    // post condition
                    this_expect=0; this_buffer_empty=1; 
                  }
                  continue;
                }

          continue;
        }
        if (q == 1){      
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !((P1 % 2) != (0 % 2)) ){ 
                    // record method id
                    method_id = 2;
                    // non-conformance condition 
                    if ( (((((P1 % 2) != (this_expect % 2)) && (this_buffer_empty == 1)) && !((P1 % 2) != (0 % 2))) || ((this_buffer_empty != 1) && !((P1 % 2) != (0 % 2)))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 3;
                    // post condition
                    this_expect=(this_expect + 1); this_buffer_empty=(1 - this_buffer_empty); 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !(P1 != (((0 + 1) - 1) % 2)) ){ 
                    // record method id
                    method_id = 3;
                    // non-conformance condition 
                    if ( (((P3 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && !(P3 != (((0 + 1) - 1) % 2))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( (((P1 % 2) != (0 % 2)) && (((P1 % 2) != ((0 + 1) % 2)) && ((P1 % 2) != (0 % 2)))) ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (((((P4 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && ((P4 % 2) != (0 % 2))) && (((P4 % 2) != (0 % 2)) && (((P4 % 2) != ((0 + 1) % 2)) && ((P4 % 2) != (0 % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( (((P1 % 2) != (0 % 2)) && !(((P1 % 2) != ((0 + 1) % 2)) && ((P1 % 2) != (0 % 2)))) ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( (((((P6 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && ((P6 % 2) != (0 % 2))) && (((P6 % 2) != (0 % 2)) && !(((P6 % 2) != ((0 + 1) % 2)) && ((P6 % 2) != (0 % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P1 != (((0 + 1) - 1) % 2)) && ((P1 != ((((0 + 1) + 1) - 1) % 2)) && (P1 != (((0 + 1) - 1) % 2)))) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( ((((P8 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && (P8 != (((0 + 1) - 1) % 2))) && ((P8 != (((0 + 1) - 1) % 2)) && ((P8 != ((((0 + 1) + 1) - 1) % 2)) && (P8 != (((0 + 1) - 1) % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P1 != (((0 + 1) - 1) % 2)) && !((P1 != ((((0 + 1) + 1) - 1) % 2)) && (P1 != (((0 + 1) - 1) % 2)))) ){ 
                    // record method id
                    method_id = 7;
                    // non-conformance condition 
                    if ( ((((P9 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && (P9 != (((0 + 1) - 1) % 2))) && ((P9 != (((0 + 1) - 1) % 2)) && !((P9 != ((((0 + 1) + 1) - 1) % 2)) && (P9 != (((0 + 1) - 1) % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
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
                  if ( !((P1 % 2) != (0 % 2)) ){ 
                    // record method id
                    method_id = 2;
                    // non-conformance condition 
                    if ( ((((P1 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && !((P1 % 2) != (0 % 2))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !(P1 != (((0 + 1) - 1) % 2)) ){ 
                    // record method id
                    method_id = 3;
                    // non-conformance condition 
                    if ( (((P3 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && !(P3 != (((0 + 1) - 1) % 2))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( (((P1 % 2) != (0 % 2)) && (((P1 % 2) != ((0 + 1) % 2)) && ((P1 % 2) != (0 % 2)))) ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (((((P4 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && ((P4 % 2) != (0 % 2))) && (((P4 % 2) != (0 % 2)) && (((P4 % 2) != ((0 + 1) % 2)) && ((P4 % 2) != (0 % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( (((P1 % 2) != (0 % 2)) && !(((P1 % 2) != ((0 + 1) % 2)) && ((P1 % 2) != (0 % 2)))) ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( (((((P6 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && ((P6 % 2) != (0 % 2))) && (((P6 % 2) != (0 % 2)) && !(((P6 % 2) != ((0 + 1) % 2)) && ((P6 % 2) != (0 % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P1 != (((0 + 1) - 1) % 2)) && ((P1 != ((((0 + 1) + 1) - 1) % 2)) && (P1 != (((0 + 1) - 1) % 2)))) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( ((((P8 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && (P8 != (((0 + 1) - 1) % 2))) && ((P8 != (((0 + 1) - 1) % 2)) && ((P8 != ((((0 + 1) + 1) - 1) % 2)) && (P8 != (((0 + 1) - 1) % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P1 != (((0 + 1) - 1) % 2)) && !((P1 != ((((0 + 1) + 1) - 1) % 2)) && (P1 != (((0 + 1) - 1) % 2)))) ){ 
                    // record method id
                    method_id = 7;
                    // non-conformance condition 
                    if ( ((((P9 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && (P9 != (((0 + 1) - 1) % 2))) && ((P9 != (((0 + 1) - 1) % 2)) && !((P9 != ((((0 + 1) + 1) - 1) % 2)) && (P9 != (((0 + 1) - 1) % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
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
                  if ( !((P1 % 2) != (0 % 2)) ){ 
                    // record method id
                    method_id = 2;
                    // non-conformance condition 
                    if ( ((((P1 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && !((P1 % 2) != (0 % 2))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !(P1 != (((0 + 1) - 1) % 2)) ){ 
                    // record method id
                    method_id = 3;
                    // non-conformance condition 
                    if ( (((this_buffer_empty == 1) && !(P3 != (((0 + 1) - 1) % 2))) || (((P3 != ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && !(P3 != (((0 + 1) - 1) % 2)))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 4;
                    // post condition
                    this_expect=this_expect; this_buffer_empty=(1 - this_buffer_empty); 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( (((P1 % 2) != (0 % 2)) && (((P1 % 2) != ((0 + 1) % 2)) && ((P1 % 2) != (0 % 2)))) ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (((((P4 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && ((P4 % 2) != (0 % 2))) && (((P4 % 2) != (0 % 2)) && (((P4 % 2) != ((0 + 1) % 2)) && ((P4 % 2) != (0 % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( (((P1 % 2) != (0 % 2)) && !(((P1 % 2) != ((0 + 1) % 2)) && ((P1 % 2) != (0 % 2)))) ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( (((((P6 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && ((P6 % 2) != (0 % 2))) && (((P6 % 2) != (0 % 2)) && !(((P6 % 2) != ((0 + 1) % 2)) && ((P6 % 2) != (0 % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P1 != (((0 + 1) - 1) % 2)) && ((P1 != ((((0 + 1) + 1) - 1) % 2)) && (P1 != (((0 + 1) - 1) % 2)))) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( ((((P8 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && (P8 != (((0 + 1) - 1) % 2))) && ((P8 != (((0 + 1) - 1) % 2)) && ((P8 != ((((0 + 1) + 1) - 1) % 2)) && (P8 != (((0 + 1) - 1) % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P1 != (((0 + 1) - 1) % 2)) && !((P1 != ((((0 + 1) + 1) - 1) % 2)) && (P1 != (((0 + 1) - 1) % 2)))) ){ 
                    // record method id
                    method_id = 7;
                    // non-conformance condition 
                    if ( ((((P9 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && (P9 != (((0 + 1) - 1) % 2))) && ((P9 != (((0 + 1) - 1) % 2)) && !((P9 != ((((0 + 1) + 1) - 1) % 2)) && (P9 != (((0 + 1) - 1) % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }

          continue;
        }
        if (q == 4){      
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !((P1 % 2) != (0 % 2)) ){ 
                    // record method id
                    method_id = 2;
                    // non-conformance condition 
                    if ( ((((P1 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && !((P1 % 2) != (0 % 2))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !(P1 != (((0 + 1) - 1) % 2)) ){ 
                    // record method id
                    method_id = 3;
                    // non-conformance condition 
                    if ( (((P3 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && !(P3 != (((0 + 1) - 1) % 2))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( (((P1 % 2) != (0 % 2)) && (((P1 % 2) != ((0 + 1) % 2)) && ((P1 % 2) != (0 % 2)))) ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (((((P4 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && ((P4 % 2) != (0 % 2))) && (((P4 % 2) != (0 % 2)) && (((P4 % 2) != ((0 + 1) % 2)) && ((P4 % 2) != (0 % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( (((P1 % 2) != (0 % 2)) && !(((P1 % 2) != ((0 + 1) % 2)) && ((P1 % 2) != (0 % 2)))) ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( ((((((P6 % 2) != (this_expect % 2)) && (this_buffer_empty == 1)) && ((P6 % 2) != (0 % 2))) && (((P6 % 2) != (0 % 2)) && !(((P6 % 2) != ((0 + 1) % 2)) && ((P6 % 2) != (0 % 2))))) || (((this_buffer_empty != 1) && ((P6 % 2) != (0 % 2))) && (((P6 % 2) != (0 % 2)) && !(((P6 % 2) != ((0 + 1) % 2)) && ((P6 % 2) != (0 % 2)))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 5;
                    // post condition
                    this_expect=(this_expect + 1); this_buffer_empty=(1 - this_buffer_empty); 
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P1 != (((0 + 1) - 1) % 2)) && ((P1 != ((((0 + 1) + 1) - 1) % 2)) && (P1 != (((0 + 1) - 1) % 2)))) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( ((((P8 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && (P8 != (((0 + 1) - 1) % 2))) && ((P8 != (((0 + 1) - 1) % 2)) && ((P8 != ((((0 + 1) + 1) - 1) % 2)) && (P8 != (((0 + 1) - 1) % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P1 != (((0 + 1) - 1) % 2)) && !((P1 != ((((0 + 1) + 1) - 1) % 2)) && (P1 != (((0 + 1) - 1) % 2)))) ){ 
                    // record method id
                    method_id = 7;
                    // non-conformance condition 
                    if ( ((((P9 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && (P9 != (((0 + 1) - 1) % 2))) && ((P9 != (((0 + 1) - 1) % 2)) && !((P9 != ((((0 + 1) + 1) - 1) % 2)) && (P9 != (((0 + 1) - 1) % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }

          continue;
        }
        if (q == 5){      
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !((P1 % 2) != (0 % 2)) ){ 
                    // record method id
                    method_id = 2;
                    // non-conformance condition 
                    if ( ((((P1 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && !((P1 % 2) != (0 % 2))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( !(P1 != (((0 + 1) - 1) % 2)) ){ 
                    // record method id
                    method_id = 3;
                    // non-conformance condition 
                    if ( (((P3 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && !(P3 != (((0 + 1) - 1) % 2))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( (((P1 % 2) != (0 % 2)) && (((P1 % 2) != ((0 + 1) % 2)) && ((P1 % 2) != (0 % 2)))) ){ 
                    // record method id
                    method_id = 4;
                    // non-conformance condition 
                    if ( (((((P4 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && ((P4 % 2) != (0 % 2))) && (((P4 % 2) != (0 % 2)) && (((P4 % 2) != ((0 + 1) % 2)) && ((P4 % 2) != (0 % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( (((P1 % 2) != (0 % 2)) && !(((P1 % 2) != ((0 + 1) % 2)) && ((P1 % 2) != (0 % 2)))) ){ 
                    // record method id
                    method_id = 5;
                    // non-conformance condition 
                    if ( (((((P6 % 2) == (this_expect % 2)) && (this_buffer_empty == 1)) && ((P6 % 2) != (0 % 2))) && (((P6 % 2) != (0 % 2)) && !(((P6 % 2) != ((0 + 1) % 2)) && ((P6 % 2) != (0 % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P1 != (((0 + 1) - 1) % 2)) && ((P1 != ((((0 + 1) + 1) - 1) % 2)) && (P1 != (((0 + 1) - 1) % 2)))) ){ 
                    // record method id
                    method_id = 6;
                    // non-conformance condition 
                    if ( ((((P8 == ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && (P8 != (((0 + 1) - 1) % 2))) && ((P8 != (((0 + 1) - 1) % 2)) && ((P8 != ((((0 + 1) + 1) - 1) % 2)) && (P8 != (((0 + 1) - 1) % 2))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 2;
                    // post condition
                    break;
                  }
                  continue;
                }
                if(__VERIFIER_nondet_int()){
                  // assume guard
                  if ( ((P1 != (((0 + 1) - 1) % 2)) && !((P1 != ((((0 + 1) + 1) - 1) % 2)) && (P1 != (((0 + 1) - 1) % 2)))) ){ 
                    // record method id
                    method_id = 7;
                    // non-conformance condition 
                    if ( ((((this_buffer_empty == 1) && (P9 != (((0 + 1) - 1) % 2))) && ((P9 != (((0 + 1) - 1) % 2)) && !((P9 != ((((0 + 1) + 1) - 1) % 2)) && (P9 != (((0 + 1) - 1) % 2))))) || ((((P9 != ((this_expect - 1) % 2)) && (this_buffer_empty != 1)) && (P9 != (((0 + 1) - 1) % 2))) && ((P9 != (((0 + 1) - 1) % 2)) && !((P9 != ((((0 + 1) + 1) - 1) % 2)) && (P9 != (((0 + 1) - 1) % 2)))))) ) {
                      goto ERROR;
                    }
                    // state update
                    q = 1;
                    // post condition
                    this_expect=this_expect; this_buffer_empty=(1 - this_buffer_empty); 
                  }
                  continue;
                }

          continue;
        }
   

  } // end while

  return 0;

 ERROR:  __VERIFIER_error();
}
