//#Safe

procedure f() {
  loop:
  goto loop;
}

procedure ULTIMATE.start() {
  call f();
  assert false;
}

