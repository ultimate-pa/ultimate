//#Unsafe
/*
 * 2020-04-10
 * Delta-debugged example from ldv-linux-3.0/usb_urb-drivers-input-tablet-kbtab.ko.cil.out.i
 * For IsEmptyHeuristic: AssertionError: IsEmptyHeuristic did not match IsEmpty
 * 
 * Author: dietsch@cs.uni-freiburg.de
 */

void  ( __attribute__((__always_inline__)) kmalloc)(int size ,
                                                                    int flags )
{

      __kmalloc(0, 0);

}

void *kzalloc(int size , int flags )
{

      kmalloc(0,     0);

}

void usb_free_coherent(int *dev , int size , int *addr , int dma ) __attribute__((__ldv_model__)) ;

void *input_allocate_device( ) {
       return kzalloc(0, 0);
}

void kbtab_probe(int  intf , int  id )
{

      kzalloc(0, 0);

      input_allocate_device();

  fail2:
  {
  usb_free_coherent(0,     0, 0, 0);
  }

}

void main( )
{

              kbtab_probe(0, 0);

}
void ldv_blast_assert( )
{

  ERROR: __VERIFIER_error();

}

void usb_free_coherent(int *dev , int size , int *addr , int dma )
{

        ldv_blast_assert();

}

void *__kmalloc(int arg0, int arg1) {

}



