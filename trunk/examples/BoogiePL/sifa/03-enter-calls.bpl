procedure ULTIMATE.start() returns () {
	// "if *" only there so that we don't have to compute summaries
	if (*) {
		call f();
	} else {
		call g();
	}
}

procedure f() returns () {
	call h(8);
}

procedure g() returns () {
	call h(-5);
}

procedure h(i : int) returns () {
  assert i > 0;
}
