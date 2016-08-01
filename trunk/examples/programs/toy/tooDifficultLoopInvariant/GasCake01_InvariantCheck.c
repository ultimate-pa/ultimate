
typedef float float32;


// extern boolean tclRange_b(boolean _min_b, boolean _max_b);
// extern char8 tclRange_c8(char8 _min_c8, char8 _max_c8);
// extern sint8 tclRange_s8(sint8 _min_s8, sint8 _max_s8);
// extern sint16 tclRange_s16(sint16 _min_s16, sint16 _max_s16);
// extern sint32 tclRange_s32(sint32 _min_s32, sint32 _max_s32);
// extern uint8 tclRange_u8(uint8 _min_u8, uint8 _max_u8);
// extern uint16 tclRange_u16(uint16 _min_u16, uint16 _max_u16);
// extern uint32 tclRange_u32(uint32 _min_u32, uint32 _max_u32);
// extern float32 tclRange_f32(float32 _min_f32, float32 _max_f32);
// extern float64 tclRange_f64(float64 _min_f64, float64 _max_f64);



float32 tclRange_f32(float32 min, float32 max) {
	float32 result;
	if (result >= min && result <= max) {
		return result;
	} else {
		while (1) {}
	}
}


void holdsInitially(void) {
	float32 input_f32;
	float32 output_f32 = 0;
	float32 internal_f32 = 0;
 	//@ assert ((internal_f32 * 0.9 + output_f32 >= -0.00001) && (internal_f32 * 0.9 + output_f32 <= 100.00001) && (output_f32 >= -0.00001) && (output_f32 <= 100.00001) && (internal_f32 >= -56.0));
}

void isInductive(void) {
	float32 input_f32;
	float32 output_f32;
	float32 internal_f32;
	float32 outputOld_f32;
	
	if (((internal_f32 * 0.9 + outputOld_f32 >= -1.0) && (internal_f32 * 0.9 + outputOld_f32 <= 101.0) && (outputOld_f32 >= -1.0) && (outputOld_f32 <= 101.0) && (internal_f32 >= -57.0))) {
		
		input_f32 = tclRange_f32(0.0, 100.0);
		output_f32 = outputOld_f32 + (internal_f32 * 0.02F);
		internal_f32 = (input_f32 * 0.02469135802F)
		+ ((outputOld_f32 * 0.02469135802F * -1.F)
		+ internal_f32 * 0.9555555556F);
		outputOld_f32 = output_f32;
		
		//@ assert ((internal_f32 * 0.9 + outputOld_f32 >= -1.0) && (internal_f32 * 0.9 + outputOld_f32 <= 101.0) && (outputOld_f32 >= -1.0) && (outputOld_f32 <= 101.0) && (internal_f32 >= -57.0));
	}
}



void isSafe(void) {
	float32 input_f32;
	float32 output_f32 = 0;
	float32 internal_f32 = 0;
 	if (((internal_f32 * 0.9 + output_f32 >= -0.00001) && (internal_f32 * 0.9 + output_f32 <= 100.00001) && (output_f32 >= -0.00001) && (output_f32 <= 100.00001) && (internal_f32 >= -56.0))) {
		//@ assert (output_f32 >= -0.00001 && output_f32 <= 100.00001);
	}
}
