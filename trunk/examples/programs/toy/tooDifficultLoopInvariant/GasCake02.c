/*
 * GasCake02 is an example for a PDT1-style filter. 
 *
 * This test case implements a design error.
 * Two (redundant) inputs are separately debounced (on/off delay). 
 * The inputs are identical in most cases. The inputs change rarely.
 * The asumption is, that the debounced comparison of
 * the debounced inputs will not show inequality. The problem is that if the
 * two inputs differ in one step, the debouncing can lead to different debounced
 * states of the inputs if the inputs continously change exactly after debounce
 * time.
 *
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
 
void TclAssert(boolean condition)
{
	 //@assert condition;
}
 
uint8 debounce_u8(uint8 _signal_u8, uint8 _debounceThresh_u8,
			   uint8 _lastOutput_u8, uint8 * _delay_u8)
{
	uint8 output_u8 = _lastOutput_u8;
	if (_delay_u8 != NULL)
	{
		if (_signal_u8 != _lastOutput_u8)
		{
			(*_delay_u8)++;
			if (*_delay_u8 >= _debounceThresh_u8)
			{
				*_delay_u8 = 0;
				output_u8 = _signal_u8;
			}
		} else {
			*_delay_u8 = 0;
		}
		return output_u8;
	} else {
		return _signal_u8;
	}
}

void PDebounceValidation(void)
{
	static uint8 signal_u8 = 0;
	static uint8 plausiSignal_u8 = 0;
	static uint8 signalDeb_u8 = 0;
	static uint8 plausiSignalDeb_u8 = 0;
	static uint8 signalDelay_u8 = 0;
	static uint8 plausiSignalDelay_u8 = 0;
	static uint8 comparisonDelay_u8 = 0;
	static uint8 comparisonDeb_u8 = (1==1);

	uint8 comparison_u8 = 0;

	while (tclRange_b(0,1))
	{
		if (tclRange_u8(0,255)== 0) {
			signal_u8 = tclRange_u8(0,255);
			if (tclRange_u8(0,255)== 0) {
				plausiSignal_u8 = tclRange_u8(0,255);
			}
			else {
				plausiSignal_u8 = signal_u8;
			}
		}
		signalDeb_u8 = debounce_u8(signal_u8, 10, signalDeb_u8, &signalDelay_u8);
		plausiSignalDeb_u8 = debounce_u8(plausiSignal_u8, 10, plausiSignalDeb_u8, &plausiSignalDelay_u8);

		comparison_u8 = (signalDeb_u8 == plausiSignalDeb_u8);
		comparisonDeb_u8 = debounce_u8(comparison_u8, 10, comparisonDeb_u8, &comparisonDelay_u8);
		TclAssert(comparisonDeb_u8 > 0); /* <- Bug position */
	}
}

void main()
{
	PDebounceValidation();	
}