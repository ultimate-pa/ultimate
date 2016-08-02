/*
 * GasCake01 is an example for a PDT1-style filter. 
 * 
 * Author: heizmann@informatik.uni-freiburg.de, dietsch@informatik.uni-freiburg.de 
 * Date: 2016-07-25
 */

typedef unsigned char boolean;
typedef unsigned char uint8;
typedef signed char sint8;
typedef char char8;
typedef unsigned short int uint16;
typedef signed short int sint16;
typedef unsigned long int uint32;
typedef signed long int sint32;
typedef unsigned long long uint64;
typedef signed long long sint64;
typedef float float32;
typedef double float64;

extern void tclSinkb_v(const boolean _value_b);
extern void tclSinkc8_v(const char8 _value_c8);
extern void tclSinks8_v(const sint8 _value_s8);
extern void tclSinks16_v(const sint16 _value_s16);
extern void tclSinks32_v(const sint32 _value_s32);
extern void tclSinks64_v(const sint64 _value_s64);
extern void tclSinku8_v(const uint8 _value_u8);
extern void tclSinku16_v(const uint16 _value_u16);
extern void tclSinku32_v(const uint32 _value_u32);
extern void tclSinku64_v(const uint64 _value_u64);
extern void tclSinkf32_v(const float32 _value_f32);
extern void tclSinkf64_v(const float64 _value_f64);
extern void tclSinkpb_v(const boolean * _value_b);
extern void tclSinkpc8_v(const char8 * _value_c8);
extern void tclSinkps8_v(const sint8 * _value_s8);
extern void tclSinkps16_v(const sint16 * _value_s16);
extern void tclSinkps32_v(const sint32 * _value_s32);
extern void tclSinkps64_v(const sint64 * _value_s64);
extern void tclSinkpu8_v(const uint8 * _value_u8);
extern void tclSinkpu16_v(const uint16 * _value_u16);
extern void tclSinkpu32_v(const uint32 * _value_u32);
extern void tclSinkpu64_v(const uint64 * _value_u64);
extern void tclSinkpf32_v(const float32 * _value_f32);
extern void tclSinkpf64_v(const float64 * _value_f64);
extern void tclSinkComment_v(const char8 * _comment_pc8);
extern void tclSinkMemory_v(const uint8 * _memory_pc8, uint32 _size_u32);
extern boolean tclRange_b(boolean _min_b, boolean _max_b);
extern char8 tclRange_c8(char8 _min_c8, char8 _max_c8);
extern sint8 tclRange_s8(sint8 _min_s8, sint8 _max_s8);
extern sint16 tclRange_s16(sint16 _min_s16, sint16 _max_s16);
extern sint32 tclRange_s32(sint32 _min_s32, sint32 _max_s32);
extern uint8 tclRange_u8(uint8 _min_u8, uint8 _max_u8);
extern uint16 tclRange_u16(uint16 _min_u16, uint16 _max_u16);
extern uint32 tclRange_u32(uint32 _min_u32, uint32 _max_u32);
extern float32 tclRange_f32(float32 _min_f32, float32 _max_f32);
extern float64 tclRange_f64(float64 _min_f64, float64 _max_f64);

boolean tclRange_b(boolean min, boolean max) {
	boolean result;
	if (result >= min && result <= max) {
		return result;
	} else {
		while (1) {}
	}
}

float32 tclRange_f32(float32 min, float32 max) {
	float32 result;
	if (result >= min && result <= max) {
		return result;
	} else {
		while (1) {}
	}
}

float32 NStablePDT1Float(float32 input_f32)
{
	float32 output_f32;
	boolean reset_b;
	static float32 outputOld_f32 = 0;
	static float32 internal_f32 = 0;
	reset_b = tclRange_b(0, 1);
	if (reset_b) 
	{
		output_f32 = input_f32;
		internal_f32 = 0.F;
	}
	else 
	{
		output_f32 = outputOld_f32 + (internal_f32 * 0.02F);
		internal_f32 = (input_f32 * 0.02469135802F)
		  + ((outputOld_f32 * 0.02469135802F * -1.F)
		  + internal_f32 * 0.9555555556F);
	}
	outputOld_f32 = output_f32;
	return output_f32;
}

void main(){
	
	while(1){
		float32 input_f32;
		float32 output_f32;
		input_f32 = tclRange_f32(0.0, 100.0);
		output_f32 = NStablePDT1Float(input_f32);
		 // @assert 0.0 <= output_f32 && output_f32 <= 100.0;
	}
}
