//#Unsafe

procedure f() {
  assert false;
}

procedure ULTIMATE.start() {
  call f();
  loop:
  goto loop;
}

