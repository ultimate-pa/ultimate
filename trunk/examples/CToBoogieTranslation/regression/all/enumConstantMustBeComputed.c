////#Safe
/*
 * author: nutz
 */

#include<stddef.h>
//taken from ldv-linux3.0/module_get_put-drivers-atm-eni.ko_true-unreach-call.cil.out.i.pp.cil.c
enum netdev_tx {
    __NETDEV_TX_MIN = (-0x7FFFFFFF-1),
    NETDEV_TX_OK = 0,
    NETDEV_TX_BUSY = 16,
    NETDEV_TX_LOCKED = 32
} ;

int main() {
  enum netdev_tx enu;

  return 0;
}
