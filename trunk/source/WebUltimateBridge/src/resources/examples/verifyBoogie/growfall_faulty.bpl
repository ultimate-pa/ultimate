procedure growfallExample() {
	var x,x_new,x_old,t,t_new,t_old: real;
	
	assume (t == 0.0 && x == 0.0);
	
grow: 
		t_old := t;
		x_old := x;
		
		assume (t_old <= 5.0);
		
		havoc t_new;
		havoc x_new;
		
		assume (t_new >= t_old);
		assume ((2.0 * (t_new - t_old)) == (x_new - x_old));
		assume (t_new <= 5.0);
		
		t := t_new;
		x := x_new;
		
		if (*) {
			goto grow;
		} else if (*) {
			assume (t >= 5.0);
			t := 0.0;
			goto fall;
		} else {
			goto end;
		}
	
fall:
		t_old := t;
		x_old := x;
		
		assume (t_old <= 10.0);
		
		havoc t_new;
		havoc x_new;
		
		assume (t_new >= t_old);
		assume ((t_old - t_new) == (x_old - x_new)); // (x_new - x_old)); // faulty mutation
		assume (t_new <= 10.0);
		
		t := t_new;
		x := x_new;
		
		if (*) {
			goto fall;
		} else if (*) {
			assume (t >= 10.0);
			t := 0.0;
			goto grow;
		} else {
			goto end;
		}
	
end:
	assert (x >= 0.0 && x <= 10.0);
}