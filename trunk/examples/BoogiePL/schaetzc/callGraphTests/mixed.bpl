procedure a() {
  call b();
  call c();
}

procedure b() {
  call c();
}

procedure c() {
  call i();
  call d();
}

procedure d() {
  call e();
}

procedure e() {
  call f();
}

procedure f() {
  call forall a();
  call e();
  call d();
}

procedure g() {
  call g();
  call h();
  call f();
}

procedure h();

procedure i() {
}

procedure j() {
  call k();
  call l();
  call forall m();
}

procedure k() {
}

procedure l();

procedure m() {
}

procedure n() {
  call n();
}

procedure o();

procedure p() {
}

procedure q() {
  call forall q();
}

procedure r() {
  call forall r();
  call r();
}

