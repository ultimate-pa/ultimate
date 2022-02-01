#include <vcc.h>

void foo(bool a, bool b) 
  requires(a && !b)
{
  assert(b <== b);
  assert(a <== b);
  assert(a <== a);
  assert(!(b <== a));
  assert(b <== b <== a);
  assert(a <== b <== a);
  assert(b <== a <== b);
  assert(a <== a <== b);
  assert(!(b <== a <== a));
  assert(a <== a <== a);
  assert(a <== b <== b);
  assert(b <== b <== b);
  assert(!(a <== a ==> b));
  assert(!((a <== a) ==> b));
  assert(a <== (a ==> b));
}
