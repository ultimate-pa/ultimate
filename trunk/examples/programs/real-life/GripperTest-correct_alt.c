int __BLAST_NONDET;

main() {
	int is_room_x;
	int room_x;
	int room_y;
	
	int is_left_gripper;
	int gripper_left;
	int gripper_right;
	
	is_room_x = 1;
	is_left_gripper = 1;
	room_x = 4;
	room_y = 0;
	gripper_left = 0;
	gripper_right = 0;
	
	while(__BLAST_NONDET)
	{
		if (room_y == -1) {ERROR: goto ERROR;} 
	
		if (__BLAST_NONDET) {
			// toggle room
			if (is_room_x == 1) {
				is_room_x = 0;
			} else {
				is_room_x = 1;
			}
		}
		if (__BLAST_NONDET) {
			// toggle gripper
			if (is_left_gripper == 1) {
				is_left_gripper = 0;
			} else {
				is_left_gripper = 1;
			}
		}
		if (__BLAST_NONDET) {
			// pick up: room
			if ( is_room_x == 1) {
				if (room_x > 1) {
					room_x = room_x - 1;
				}
			} else {
				if (room_y > 1) {
					room_y = room_y - 1;
				}
			}
			// pick up: gripper
			if ( is_left_gripper == 1 ) {
				gripper_left = gripper_left + 1;
			} else {
				gripper_right = gripper_right + 1;
			}
		}
		if (__BLAST_NONDET) {
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
}