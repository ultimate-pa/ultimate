var stack: [int]int;
var stack.length: int;


procedure stack.push(i: int)
modifies stack, stack.length;
{
  stack.length := stack.length + 1;
  stack[stack.length] := i;
}

procedure stack.pop() returns (i: int)
modifies stack, stack.length;
{
  i:= stack[stack.length];
  stack.length := stack.length - 1;
}

procedure main()
modifies stack, stack.length;
{
var r:int;

call stack.push(1);
call r:= stack.pop();
assert(r==1);
}
