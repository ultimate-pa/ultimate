//#Safe
/* Encodes invariant inductivity check for some larger example program.
 * 
 * Use large block encoding and Mathsat.
 * Verification took 350s on my computer.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-07-26
 */
typedef float float32;


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
	float32 outputOld_f32 = 0;
 	//@ assert ((internal_f32 * 0.9 + outputOld_f32 >= -1.0) && (internal_f32 * 0.9 + outputOld_f32 <= 101.0) && (outputOld_f32 >= -1.0) && (outputOld_f32 <= 101.0) && (internal_f32 >= -57.0));
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
	float32 output_f32;
	float32 internal_f32;
	float32 outputOld_f32;
	outputOld_f32 = output_f32;
 	if (((internal_f32 * 0.9 + outputOld_f32 >= -1.0) && (internal_f32 * 0.9 + outputOld_f32 <= 101.0) && (outputOld_f32 >= -1.0) && (outputOld_f32 <= 101.0) && (internal_f32 >= -57.0))) {
		//@ assert (output_f32 >= -1.0 && output_f32 <= 101.0);
	}
}
