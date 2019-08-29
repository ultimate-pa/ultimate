//#Unsafe

procedure f() {
  loop:
  goto loop;
}

procedure ULTIMATE.start() {
  assert false;
  call f();
}

