//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 13.8.2010
 *
 * Precedural version of the "Locking Example" which occurs in e.g.
 *
 * Thomas A. Henzinger, Ranjit Jhala, Rupak Majumdar, Grégoire Sutre: Lazy abstraction. POPL 2002
 * Kenneth L. McMillan: Lazy Abstraction with Interpolants. CAV 2006
 *
 * The assert statement before the break statement violates correctness of this example.
 */

var lock: int;
var counter: int;

procedure Main();
modifies lock, counter;
requires lock ==0;


implementation Main()
{
  var new, auld: int;
  
  counter := 0;
  
  while (true) {
    call lock();
    auld := new;
    if (*) {
      call unlock();
      new := new + 1;
    }
    if (new == auld) {
      assert(counter != 0 || lock==0);
      break;
    }
    counter := counter + 1;
  } 
}


procedure lock();
modifies lock;
requires lock == 0;

implementation lock() {
  lock := 1;
}
 

procedure unlock();
modifies lock;
requires lock == 1;

implementation unlock() {
  lock := 0;
}
