//#Safe
/*
*/

var block  : int;
var busy   : int;
var inode  : int;
var l_inode: int;
var l_busy : int;


procedure ULTIMATE.start()
  modifies block, busy, inode, l_inode, l_busy;
{
  assume inode == busy;

  l_inode := 0;
  l_busy  := 0;
  block   := 0;

  fork 1 allocator();
  fork 2 de_allocator();
}


procedure allocator()
  modifies block, busy, inode, l_inode, l_busy;
{
  atomic {
    assume l_inode == 0;
    l_inode := 1;
  }

  if (inode == 0) {
    atomic {
      assume l_busy == 0;
      l_busy := 1;
    }

    busy := 1;

    l_busy := 0;

    inode := 1;
  }

  block := 1;
  assert block == 1;

  l_inode := 0;
}



procedure de_allocator()
  modifies block, busy, inode, l_inode, l_busy;
{
  atomic {
    assume l_busy == 0;
    l_busy := 1;
  }

  if (busy == 0) {
    block := 0;
    assert block == 0;
  }

  l_busy := 0;
}

