/*
 * DD 2016-10-11
 * Cast necessary for floating point constant and integer constant does not work as expected. 
 *
 */
union X
{
  double z;
};

int main( ) {

 union X var;
 var.z = 0x1.4p+4;

}