//#Unsafe

procedure f() {
	  var i : int;
	  call i := g();
	  call h();
	  assert false;
}

procedure g() returns (x : int);

implementation g() returns (y : int) {

}

procedure h() {

}