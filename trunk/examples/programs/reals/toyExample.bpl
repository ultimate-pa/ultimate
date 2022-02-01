procedure nav01Example() {
	var x1,x1_new,x1_old : real ;
	var x2,x2_new,x2_old : real ;
	var t,t_new,t_old : real ;
	var eps : real ;
	
	// initial state
	assume ( 0.0000 <= x1 && x1 <= 1.0000 );
	assume ( 0.0000 <= x2 && x2 <= 1.0000 );
	assume ( t == 0.0 );
	assume ( eps == 0.0 );
	
	goto loc_0;
	
loc_0:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 0.0 - eps && x1_old <= 1.0 + eps);
		assume (x2_old >= 0.0 - eps && x2_old <= 1.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old + t_new && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 0.0 - eps && x1_new <= 1.0 + eps);
		assume (x2_new >= 0.0 - eps && x2_new <= 1.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_0;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 1.0 - eps );
			// assignment
			t := 0.0;
			goto loc_1;
		} else {
			goto end;
		}
		
loc_1:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 1.0 - eps && x1_old <= 2.0 + eps);
		assume (x2_old >= 0.0 - eps && x2_old <= 1.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old + t_new && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 1.0 - eps && x1_new <= 2.0 + eps);
		assume (x2_new >= 0.0 - eps && x2_new <= 1.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_1;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 2.0 - eps );
			// assignment
			t := 0.0;
			goto loc_2;
		} else {
			goto end;
		}
		
loc_2:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 2.0 - eps && x1_old <= 3.0 + eps);
		assume (x2_old >= 0.0 - eps && x2_old <= 1.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old + t_new && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 2.0 - eps && x1_new <= 3.0 + eps);
		assume (x2_new >= 0.0 - eps && x2_new <= 1.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_2;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 3.0 - eps );
			// assignment
			t := 0.0;
			goto loc_3;
		} else {
			goto end;
		}
		
loc_3:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 3.0 - eps && x1_old <= 4.0 + eps);
		assume (x2_old >= 0.0 - eps && x2_old <= 1.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old + t_new && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 3.0 - eps && x1_new <= 4.0 + eps);
		assume (x2_new >= 0.0 - eps && x2_new <= 1.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_3;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 4.0 - eps );
			// assignment
			t := 0.0;
			goto loc_4;
		} else {
			goto end;
		}
		
loc_4:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 4.0 - eps && x1_old <= 5.0 + eps);
		assume (x2_old >= 0.0 - eps && x2_old <= 1.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old && x2_new == x2_old + t_new );
		
		// invariant
		assume (x1_new >= 4.0 - eps && x1_new <= 5.0 + eps);
		assume (x2_new >= 0.0 - eps && x2_new <= 1.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_4;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x2 == 1.0 - eps );
			// assignment
			t := 0.0;
			goto loc_9;
		} else {
			goto end;
		}
		
loc_9:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 4.0 - eps && x1_old <= 5.0 + eps);
		assume (x2_old >= 1.0 - eps && x2_old <= 2.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old && x2_new == x2_old + t_new );
		
		// invariant
		assume (x1_new >= 4.0 - eps && x1_new <= 5.0 + eps);
		assume (x2_new >= 1.0 - eps && x2_new <= 2.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_9;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x2 == 2.0 - eps );
			// assignment
			t := 0.0;
			goto loc_14;
		} else {
			goto end;
		}
		
loc_14:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 4.0 - eps && x1_old <= 5.0 + eps);
		assume (x2_old >= 2.0 - eps && x2_old <= 3.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old && x2_new == x2_old + t_new );
		
		// invariant
		assume (x1_new >= 4.0 - eps && x1_new <= 5.0 + eps);
		assume (x2_new >= 2.0 - eps && x2_new <= 3.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_14;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x2 == 3.0 - eps );
			// assignment
			t := 0.0;
			goto loc_19;
		} else {
			goto end;
		}
		
loc_19:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 4.0 - eps && x1_old <= 5.0 + eps);
		assume (x2_old >= 3.0 - eps && x2_old <= 4.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old && x2_new == x2_old + t_new );
		
		// invariant
		assume (x1_new >= 4.0 - eps && x1_new <= 5.0 + eps);
		assume (x2_new >= 3.0 - eps && x2_new <= 4.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_19;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x2 == 4.0 - eps );
			// assignment
			t := 0.0;
			goto loc_24;
		} else {
			goto end;
		}
		
loc_24:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 4.0 - eps && x1_old <= 5.0 + eps);
		assume (x2_old >= 4.0 - eps && x2_old <= 5.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old - t_new && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 4.0 - eps && x1_new <= 5.0 + eps);
		assume (x2_new >= 4.0 - eps && x2_new <= 5.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_24;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 4.0 - eps );
			// assignment
			t := 0.0;
			goto loc_23;
		} else {
			goto end;
		}
		
loc_23:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 3.0 - eps && x1_old <= 4.0 + eps);
		assume (x2_old >= 4.0 - eps && x2_old <= 5.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old - t_new && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 3.0 - eps && x1_new <= 4.0 + eps);
		assume (x2_new >= 4.0 - eps && x2_new <= 5.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_23;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 3.0 - eps );
			// assignment
			t := 0.0;
			goto loc_22;
		} else {
			goto end;
		}
		
loc_22:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 2.0 - eps && x1_old <= 3.0 + eps);
		assume (x2_old >= 4.0 - eps && x2_old <= 5.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old - t_new && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 2.0 - eps && x1_new <= 3.0 + eps);
		assume (x2_new >= 4.0 - eps && x2_new <= 5.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_22;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 2.0 - eps );
			// assignment
			t := 0.0;
			goto loc_21;
		} else {
			goto end;
		}
		
loc_21:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 1.0 - eps && x1_old <= 2.0 + eps);
		assume (x2_old >= 4.0 - eps && x2_old <= 5.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old - t_new && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 1.0 - eps && x1_new <= 2.0 + eps);
		assume (x2_new >= 4.0 - eps && x2_new <= 5.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_21;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 1.0 - eps );
			// assignment
			t := 0.0;
			goto loc_20;
		} else {
			goto end;
		}
		
loc_20:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 0.0 - eps && x1_old <= 1.0 + eps);
		assume (x2_old >= 4.0 - eps && x2_old <= 5.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old && x2_new == x2_old - t_new );
		
		// invariant
		assume (x1_new >= 0.0 - eps && x1_new <= 1.0 + eps);
		assume (x2_new >= 4.0 - eps && x2_new <= 5.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_20;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x2 == 4.0 - eps );
			// assignment
			t := 0.0;
			goto loc_15;
		} else {
			goto end;
		}
		
loc_15:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 0.0 - eps && x1_old <= 1.0 + eps);
		assume (x2_old >= 3.0 - eps && x2_old <= 4.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume (  x1_new == x1_old && x2_new == x2_old - t_new );
		
		// invariant
		assume (x1_new >= 0.0 - eps && x1_new <= 1.0 + eps);
		assume (x2_new >= 3.0 - eps && x2_new <= 4.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_15;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x2 == 3.0 - eps );
			// assignment
			t := 0.0;
			goto loc_10;
		} else {
			goto end;
		}
		
loc_10:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 0.0 - eps && x1_old <= 1.0 + eps);
		assume (x2_old >= 2.0 - eps && x2_old <= 3.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old + t_new  && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 0.0 - eps && x1_new <= 1.0 + eps);
		assume (x2_new >= 2.0 - eps && x2_new <= 3.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_10;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 1.0 - eps );
			// assignment
			t := 0.0;
			goto loc_11;
		} else {
			goto end;
		}
		
loc_11:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 1.0 - eps && x1_old <= 2.0 + eps);
		assume (x2_old >= 2.0 - eps && x2_old <= 3.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old + t_new  && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 1.0 - eps && x1_new <= 2.0 + eps);
		assume (x2_new >= 2.0 - eps && x2_new <= 3.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_11;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 2.0 - eps );
			// assignment
			t := 0.0;
			goto loc_12;
		} else {
			goto end;
		}
		
loc_12:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 2.0 - eps && x1_old <= 3.0 + eps);
		assume (x2_old >= 2.0 - eps && x2_old <= 3.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old + t_new  && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 2.0 - eps && x1_new <= 3.0 + eps);
		assume (x2_new >= 2.0 - eps && x2_new <= 3.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_12;
		} else if (*) {
			// guard
			assume ( t < 1.0 );
			assume ( x1 == 3.0 - eps );
			// assignment
			t := 0.0;
			goto loc_13;
		} else {
			goto end;
		}
		
loc_13:
		x1_old := x1;
		x2_old := x2;
		t_old := t;
		
		// invariant
		assume (x1_old >= 3.0 - eps && x1_old <= 4.0 + eps);
		assume (x2_old >= 2.0 - eps && x2_old <= 3.0 + eps);
		assume (t_old >= 0.0 && t_old <= 1.0);
		
		havoc x1_new;
		havoc x2_new;
		havoc t_new;
		
		// flow
		assume ( x1_new == x1_old && x2_new == x2_old );
		
		// invariant
		assume (x1_new >= 3.0 - eps && x1_new <= 4.0 + eps);
		assume (x2_new >= 2.0 - eps && x2_new <= 3.0 + eps);
		assume (t_new >= 0.0 && t_new <= 1.0);
		
		x1 := x1_new;
		x2 := x2_new;
		t := t_new;
		// transitions
		if (*) {
			// guard
			assume ( t == 1.0 );
			// assignment
			t := 0.0;
			goto loc_13;
		} else {
			goto end;
		}
		
end:
		assert !( x1 > 0.0 &&  x1 < 1.0 && x2 > 1.0 && x2 < 2.0 );
}