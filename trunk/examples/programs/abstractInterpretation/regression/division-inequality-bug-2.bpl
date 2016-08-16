//#Unsafe
// 29.06.16: Post is unsound because the term-transformation of the following triple is not valid: 
// Pre: {(and (>= ULTIMATE.start_x 1) (<= ULTIMATE.start_x 10))}
// (and 
//		(= (mod v_ULTIMATE.start_y_1 2) 0) 
//		(not (= v_ULTIMATE.start_y_1 0)) 
//		(<= 2 (* 2 v_ULTIMATE.start_x_2)) 
//		(<= (* 2 v_ULTIMATE.start_x_2) 20) 
//		(= (div v_ULTIMATE.start_x_2 v_ULTIMATE.start_y_1) 5))
// Post: {false}
procedure ULTIMATE.start()
{
	var x, y, z : int;

	assume x>= 1 && x<=10;
	assert true;
	assume (y % 2 == 0 && !(y == 0)) && -x - x <= -2 && x - -x <= 20;
	assume x / y == 5;
	assert false;
}


