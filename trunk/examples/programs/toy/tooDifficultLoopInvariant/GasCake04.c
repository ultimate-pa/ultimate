/*
 * GasCake04.c
 *
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
 


static boolean tclTestRandomFunc_b(void) {
	return (boolean)(rand() & 0x01);
}

static uint8 tclTestRandomFunc_u8(void) {
	return (uint8)(rand() & 0xFF);
}

static sint8 tclTestRandomFunc_s8(void) {
	return (sint8)(rand() & 0xFF);
}

static char8 tclTestRandomFunc_c8(void) {
	return (char8)(rand() & 0xFF);
}


static uint16 tclTestRandomFunc_u16(void) {
	return (uint16)(rand() & 0xFFFF);
}

static sint16 tclTestRandomFunc_s16(void) {
	return (sint16)(rand() & 0xFFFF);
}

static uint32 tclTestRandomFunc_u32(void) {
	return (uint32)(rand());
}

static sint32 tclTestRandomFunc_s32(void) {
	return (sint32)(rand());
}

static float32 tclTestRandomFunc_f32(void) {

	float32 value_f32;
	sint32 value_s32;
	value_s32 = (sint32)(rand());
	memcpy((void*)&value_f32,(void*) &value_s32, sizeof(value_f32));
	return value_f32;
}

static float64 tclTestRandomFunc_f64(void) {

	float64 value_f64;
	sint32 value_ps32[2];
	value_ps32[0] = (sint32)(rand());
	value_ps32[1] = (sint32)(rand());

	memcpy((void*)&value_f64,(void*) value_ps32, sizeof(value_f64));
	return value_f64;
}


void RBitfieldAlignment(void)
{
    union {
	  struct{
		  uint32 CrcDcDcOutputRq_bf8   	      : 8;
		  uint32 SqcDcDcOutputRq_bf4      	  : 4;
		  uint32 Rsrv1DcDcOutputRq_bf2        : 2;
		  uint32 DcDcMdRq_bf2                 : 2;
		  uint32 DcDcPnhvOutVoltRq_bf13       : 13;
		  uint32 DcDcPnlvOutCurrRq_bf11      : 11;
		  /*<-BugSource: DcDcPnlvOutCurrRq_bf11 can overlap 2 storage units or
		    start in next storage unit. It is compiler dependent. So total
		    size of union might be 8 or 12 bytes.*/
		  uint32 DcDcPnlvOutVoltRq_bf10      : 10;
		  uint32 DcDcPnhvOutCurrRq_bf14      : 14;
	  } msg_str;
		  uint8 raw_pu8[8];
		  uint16 raw_pu16[4];
		  uint32 raw_pu32[2];
  } DcDcOutputRq_u;

  uint16 outCurrRq_u16;
  uint8 idx_u8;


  for (idx_u8 = 0; idx_u8 < 8; idx_u8++){
	  DcDcOutputRq_u.raw_pu8[idx_u8] =tclRange_u8(0,255);
  }

  outCurrRq_u16 = DcDcOutputRq_u.msg_str.DcDcPnhvOutCurrRq_bf14;
  /* <-BugPosition: If total size of union is 12 bytes, this element has not
   * been initialized. */

  tclSinku16_v(outCurrRq_u16);
}

int main(void)
{
    while (tclRange_b(0,1))
    {
        if (tclRange_b(0,1)) RBitfieldAlignment();
    }
    return 0;
}
