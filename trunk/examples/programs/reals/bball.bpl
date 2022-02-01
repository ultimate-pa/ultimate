procedure BouncingBallExample() {
	var x_old,v_old,x_tmp,v_tmp,x,v,x_new,v_new: real;
	
	assume (x>=10.0 && x<=10.2 && v==0.0);
	//x:=10.0;
	//v:=0.0;
	while (*) 
	invariant (x>=1.0); {
	
		x_old := x;
		x_new := x - v;
		//x_new := x - 1.0 * 0.1 * 0.1 * 0.5 + v * 0.1;
		assume(x_new >= 0.0);
		
		havoc x_tmp;
		
		if (x_new > x_old)
		{
			assume(x_tmp>=x_old && x_tmp<=x_new);
		} else {
			assume(x_tmp<=x_old && x_tmp>=x_new);
		}
		x := x_tmp;
		
		v_old := v;
		v_new := v + 1.0;	
		//v_new := (0.0-1.0) * 0.1 + v;
		
		havoc v_tmp;
		
		if (v_new > v_old)
		{
			assume(v_tmp>=v_old && v_tmp<=v_new);
		} else {
			assume(v_tmp<=v_old && v_tmp>=v_new);
		}
		v := v_tmp;

		if (x == 0.0) {
			v := (0.0-0.75)*v;
		}
	}
}
