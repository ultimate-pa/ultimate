//#Safe

procedure f() {
  assert false;
}

procedure ULTIMATE.start() {
  loop:
  goto loop;
  call f();
}

