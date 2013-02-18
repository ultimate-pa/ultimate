int main() {
	_Bool is_room_x = 1;
	int room_x = 4;
	int room_y = 0;
	
	_Bool is_left_gripper = 1;
	int gripper_left = 0;
	int gripper_right = 0;
	
	int tmp_1 = __VERIFIER_nondet_int();
	int tmp_2 = __VERIFIER_nondet_int();
	int tmp_3 = __VERIFIER_nondet_int();
	int tmp_4 = __VERIFIER_nondet_int();
	int tmp_5 = __VERIFIER_nondet_int();

	while(tmp_1)
	{
		tmp_1 = __VERIFIER_nondet_int();
		tmp_2 = __VERIFIER_nondet_int();
		tmp_3 = __VERIFIER_nondet_int();
		tmp_4 = __VERIFIER_nondet_int();
		tmp_5 = __VERIFIER_nondet_int();

		if (room_y < 0 || room_x < 0) {
			goto ERROR;
		}
	
		if (tmp_2) {
			// toggle room
			if (is_room_x == 1) {
				is_room_x = 0;
			} else {
				is_room_x = 1;
			}
		}
		else if (tmp_3) {
			// toggle gripper
			if (is_left_gripper == 1) {
				is_left_gripper = 0;
			} else {
				is_left_gripper = 1;
			}
		}
		else if (tmp_4) {
			// pick up: room
			if ( is_room_x == 1) {
					room_x = room_x - 1;
			} else {
					room_y = room_y - 1;
			}
			// pick up: gripper
			if ( is_left_gripper == 1 ) {
				gripper_left = gripper_left + 1;
			} else {
				gripper_right = gripper_right + 1;
			}
		}
		else if (tmp_5) {
			// drop: gripper
			if ( is_left_gripper == 1) {
				gripper_left = gripper_left - 1;
			} else {
				gripper_right = gripper_right - 1;
			}
			// drop: room
			if ( is_room_x == 1 ) {
				room_x = room_x + 1;
			} else {
				room_y = room_y + 1;
			}
		}
	}
END:
	return 0;
ERROR:
	return -1;
}
