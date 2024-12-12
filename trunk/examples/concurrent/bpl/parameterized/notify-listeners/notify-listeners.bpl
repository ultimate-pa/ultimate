//#Safe

var notifications : [int]int;
var current : int;

procedure notifier()
modifies notifications, current;
{
  var prev, data : int;
  prev := 0;

  while (*) {
    // generate data
    havoc data;
    assume data > prev;
    prev := data;

    // notify listeners of new data
    notifications[current] := data;
    current := current + 1;
  }
}

// listener threads
procedure ULTIMATE.start()
{
  var idx : int;
  var prev, msg : int;

  // begin listening
  idx := current;
  prev := 0;

  while (*) {
    // receive notification of new data (msg)
    assume idx < current;
    msg := notifications[idx];
    idx := idx + 1;

    // check that notifications are as expected
    assert prev < msg;
    prev := msg;
  }
}