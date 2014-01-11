//#Safe
//author: unknown
//added by nutz

	var is_room_x: bool;
	var room_y: int;
	var room_x: int;

procedure main() 
modifies is_room_x, room_y, room_x;
{
	
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
	invariant(room_y != -1); {
		if (*) {
			// toggle room
			if (is_room_x == true) {
				is_room_x := false;
			} else {
				is_room_x := true;
			}
		} else if (*) {
			// drop: room
			if ( true == is_room_x ) {
				room_x := room_x + 1;
			} else {
				room_y := room_y + 1;
			}
		}
	}
}