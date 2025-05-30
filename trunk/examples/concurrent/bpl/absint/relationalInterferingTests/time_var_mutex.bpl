//#Safe
/*
*/

var block  : int;
var busy   : int;
var inode  : int;
var l_inode: bool;
var l_busy : bool;


procedure ULTIMATE.start()
  modifies block, busy, inode, l_inode, l_busy;
{
  assume inode == busy;

  l_inode := false;
  l_busy  := false;
  block   := 0;

  fork 1 allocator();
  fork 2 de_allocator();
}


procedure allocator()
  modifies block, busy, inode, l_inode, l_busy;
{
  atomic {
    assume !l_inode;
    l_inode := true;
  }

  if (inode == 0) {
    atomic {
      assume !l_busy;
      l_busy := true;
    }

    busy := 1;

    l_busy := false;

    inode := 1;
  }

  block := 1;
  assert block == 1;

  l_inode := false;
}



procedure de_allocator()
  modifies block, busy, inode, l_inode, l_busy;
{
  atomic {
    assume !l_busy;
    l_busy := true;
  }

  if (busy == 0) {
    block := 0;
    assert block == 0;
  }

  l_busy := false;
}

