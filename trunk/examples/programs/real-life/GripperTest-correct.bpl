//#Safe

procedure main() {
	var is_room_x: bool;
	var room_x: int;
	var room_y: int;
	
	var is_left_gripper: bool;
	var gripper_left: int;
	var gripper_right: int;
	
	is_room_x := true;
	is_left_gripper := true;
	room_x := 4;
	room_y := 0;
	gripper_left := 0;
	gripper_right := 0;
	
	while(*)
	// invariant((room_x + room_y + gripper_left + gripper_right) == 4); {
	invariant(room_y != -1); {
		if (*) {
			// toggle room
			if (is_room_x == true) {
				is_room_x := false;
			} else {
				is_room_x := true;
			}
		} else if (*) {
			// toggle gripper
			if (is_left_gripper == true) {
				is_left_gripper := false;
			} else {
				is_left_gripper := true;
			}
		} else if (*) {
			// pick up: room
			if ( true == is_room_x ) {
				if (room_x > 1) {
					room_x := room_x - 1;
				}
			} else {
				if (room_y > 1) {
					room_y := room_y - 1;
				}
			}
			// pick up: gripper
			if ( true == is_left_gripper ) {
				gripper_left := gripper_left + 1;
			} else {
				gripper_right := gripper_right + 1;
			}
		} else if (*) {
			// drop: gripper
			if ( true == is_left_gripper ) {
				gripper_left := gripper_left - 1;
			} else {
				gripper_right := gripper_right - 1;
			}
			// drop: room
			if ( true == is_room_x ) {
				room_x := room_x + 1;
			} else {
				room_y := room_y + 1;
			}
		}
	}
}