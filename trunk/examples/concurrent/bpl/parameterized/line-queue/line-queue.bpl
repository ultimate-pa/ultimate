//#Safe

var ctr : int;

var queue : [int][int]int;
var write_ptr : [int]int;

function { :const_array } init(value : int) returns ([int]int);

procedure source()
free requires ctr == 1 && write_ptr == init(0);
modifies queue, write_ptr;
{
  var idx : int;

  idx := 0;
  while (true) {
    // enqueue values 0, 1, 2, ...
    queue[0][write_ptr[0]] := idx;
    write_ptr[0] := write_ptr[0] + 1;

    idx := idx + 1;
  }
}

procedure ULTIMATE.start()
free requires ctr == 1 && write_ptr == init(0);
modifies ctr, queue, write_ptr;
{
  var id : int;
  var read_ptr : int;
  var value : int;
  var prev : int;

  // take thread ID
  atomic {
    id := ctr;
    ctr := ctr + 1;
  }

  // initialize pointer to input queue
  read_ptr := 0;

  prev := -1;
  while (true) {
    // dequeue from input queue
    assume read_ptr < write_ptr[id-1];
    value := queue[id-1][read_ptr];
    read_ptr := read_ptr + 1;

    // check values are increasing
    assert value > prev;
    prev := value;

    // forward value to output queue
    queue[id][write_ptr[id]] := value;
    write_ptr[id] := write_ptr[id]+1;
  }
}