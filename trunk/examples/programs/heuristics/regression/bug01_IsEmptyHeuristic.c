//#Unsafe
/*
 * 2020-04-03
 * Delta-debugged example from ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-43_2a-drivers--md--dm-cache.ko-entry_point.cil.out.i 
 * For IsEmptyHeuristic: AssertionError: IsEmptyHeuristic did not match IsEmpty
 * 
 * Author: dietsch@cs.uni-freiburg.de
 */

void  ldv_init_zalloc(int size )
{
      calloc(0, 0);
}

void ldv_check_alloc_flags(  ) ;

int  ldv_mempool_alloc_29(int *ldv_func_arg1 , int flags ) ;

void  alloc_migration(int  cache )
{

      ldv_mempool_alloc_29(0, 0);

}

void prealloc_data_structs(int  cache , int  p )
{

        alloc_migration(0);

}

void process_deferred_bios(int  cache )
{

  ldv_36104:
      prealloc_data_structs(0, 0);

}

void do_worker(int  ws )
{

    process_deferred_bios(0);

}

void invoke_work_1( )
{

  switch (0) {
  case 0:

    do_worker(0);

  }

}

void main( )
{

      ldv_init_zalloc(0);

      ldv_init_zalloc(0);

  switch (0) {
  case 0:

    invoke_work_1();

  }

}

void *ldv_mempool_alloc_29(int *ldv_func_arg1 , int flags )
{

  ldv_check_alloc_flags(0);

}

void ldv_error( )
{

  __VERIFIER_error();

}

void ldv_check_alloc_flags(int flags )
{

    ldv_error();

}

