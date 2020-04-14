//#Unsafe
/*
 * 2020-04-10
 * Delta-debugged example from ldv-commit-tester/m0_drivers-hwmon-ibmpex-ko--130_7a--d631323.i
 * For IsEmptyHeuristic: AssertionError: IsEmptyHeuristic did not match IsEmpty
 * 
 * Author: dietsch@cs.uni-freiburg.de
 */

struct ibmpex_bmc_data {

   int *bmc_device ;

};

void  __kmalloc(int size, int t)
{

}

void  kmalloc(int size , int flags )
{

      __kmalloc(0, 0);

}

void  kzalloc(int size , int flags )
{

      kmalloc(0,     0);

}

void ibmpex_find_sensors(struct ibmpex_bmc_data *data )
{

      kzalloc(0, 0);

  ldv_17688:

  ldv_17685:

  ldv_17691:

      ldv_device_create_file_6(data->bmc_device, (int *)0);

}
void ibmpex_register_bmc(int iface , int  dev )
{

      kzalloc(0, 0);

      ibmpex_find_sensors(0);

}

void main( )
{

  ldv_17796:

  switch (0) {
  case 0:

  ibmpex_register_bmc(0, 0);

  }

}

int ldv_device_create_file_6(int *ldv_func_arg1 , int *ldv_func_arg2 )
{

      ldv_device_create_file_dev_attr_of_sensor_device_attribute(ldv_func_arg2);

}

void ldv_error( )
{

  ERROR: __VERIFIER_error();

}

int ldv_device_create_file_dev_attr_of_sensor_device_attribute(int *attr )
{

      ldv_error();

}
