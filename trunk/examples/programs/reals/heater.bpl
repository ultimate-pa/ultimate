procedure heaterExample() {
	var t,t_new,t_old,t_on,t_off: real;
	
	t_on := 1.0;
	t_off:= 10.0;
	assume (t >= t_on && t <= t_off);
	
heating: 
		t_old := t;
		
		assume (t_old >= t_on);
		
		havoc t_new;
		
		assume (t_new <= t_old);
		assume (t_new >= t_on);
		
		t := t_new;
		if (*) {
			goto heating;
		} else if (*) {
		 	assume (t <= t_on);
			goto cooling;
		} else {
			goto end;
		}
	
cooling:
		t_old := t;
		
		assume (t_old <= t_off);
		
		havoc t_new;
		
		assume (t_new >= t_old);
		assume (t_new <= t_off);
		
		t := t_new;
		
		if (*) {
			goto heating;
		} else if (*) {
			assume (t >= t_off);
			goto cooling;
		} else {
			goto end;
		}
	
end:
	assert (t >=1.0 && t <= 10.0);
}