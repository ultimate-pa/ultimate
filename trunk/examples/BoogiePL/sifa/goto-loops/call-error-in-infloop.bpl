//#Unsafe

procedure f() {
  assert false;
}

procedure ULTIMATE.start() {
  loop:
  call f();
  goto loop;
}

