//#Safe

/*
 * Extracted from: svcomp/pthread-ext/06_ticket.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-02-11
 *
 */

var next_ticket, now_serving, c: int;

procedure thread() returns()
modifies next_ticket, now_serving, c;
{
  var my_ticket : int;
  
  atomic {
    assume (next_ticket + 1) % 3 != now_serving;
    my_ticket := next_ticket;
    next_ticket := (next_ticket + 1) % 3;
  }
  assume now_serving == my_ticket;
  c := c + 1;
  assert c == 1;
  c := c - 1;
  now_serving := now_serving + 1;
}

procedure ULTIMATE.start() returns()
modifies next_ticket, now_serving, c;
{
  next_ticket := 0;
  now_serving := 0;
  c := 0;

  while (true) {
    fork 0 thread();
  }
}