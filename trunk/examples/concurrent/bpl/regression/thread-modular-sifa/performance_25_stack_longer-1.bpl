const unique MAX_MEM_SIZE:int;
axiom MAX_MEM_SIZE==641;

var memory:[int]int;
var next_alloc_idx:int;
var top:int;
var state:int;

procedure nondet_int() returns (x:int)
  modifies ;
{
  havoc x;
}

procedure index_malloc() returns (curr_alloc_idx:int)
  modifies next_alloc_idx;
{
  curr_alloc_idx := -1;
  if(next_alloc_idx + 1 >= MAX_MEM_SIZE){
    curr_alloc_idx := 0;
  }else{
    curr_alloc_idx := next_alloc_idx;
    next_alloc_idx := next_alloc_idx + 2;
  }
}

procedure EBStack_init()
  modifies top;
{
  top := 0;
}

procedure push(d:int) returns (ret:int)
  modifies memory, top, next_alloc_idx;
{
  var newTop:int;
  var oldTop:int;
  call newTop := index_malloc();
  if(newTop == 0){
    ret := 0;
    return;
  }
  memory[newTop] := d;
  oldTop := top;
  memory[newTop + 1] := oldTop;
  top := newTop;
  ret := 1;
}

procedure __VERIFIER_atomic_assert(r:int)
  modifies ;
{
  assert !((r == 0) || (top != 0));
}

procedure push_loop()
  modifies memory, top, next_alloc_idx;
{
  var r:int;
  var arg:int;
  while (1 == 1)
  {
    call arg := nondet_int();
    call r := push(arg);
    call __VERIFIER_atomic_assert(r);
  }
}

procedure thr1()
  modifies memory, top, next_alloc_idx, state;
{
  if(state == 0){
    call EBStack_init();
    state := 1;
  }
  call push_loop();
}

procedure main()
  modifies memory, top, next_alloc_idx, state;
{
  while (1 == 1)
  {
    call thr1();
  }
}

