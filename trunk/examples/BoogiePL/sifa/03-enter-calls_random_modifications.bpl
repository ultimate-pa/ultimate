procedure ULTIMATE.start() returns () {
	// "if *" only there so that we don't have to compute summaries
    var x : int;
    while(x>0){
        assert x>0;
        x:=x-1;
    }
    assert x<=0;
    
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
    var x : int;
    if(x>0){
        call h(x);
    } else{
        call h(1);
    }
	//call h(-5);
}

procedure h(i : int) returns () {
  assert i > 0;
  
}
