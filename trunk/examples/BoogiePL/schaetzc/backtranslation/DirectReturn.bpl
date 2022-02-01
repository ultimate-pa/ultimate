// TODO: disable inlining of procedure b in preferences

procedure a()
{
  call bb();
  call b();
  assert false;
}


procedure bb()
{
  call b();
}


procedure b()
{
  assert true;
}

