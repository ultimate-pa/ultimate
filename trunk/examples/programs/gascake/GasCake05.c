/*
 * GasCake05.c / PUncheckedReturn
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




static void convert(sint32 decimalNumber_s32);
static void printHex(uint32 d[], uint32 c);


void PUncheckedReturn(void) {
    sint32 decimalNumber_s32;
    printf("Enter decimal number:  ");
    fflush(stdout);
    scanf("%ld", &decimalNumber_s32);
    convert(decimalNumber_s32); /*<-BugPosition: Unchecked scanf return, might result in a non-initialized variable*/
}

static void convert(sint32 decimalNumber_s32)
 {

     if(decimalNumber_s32>=0){
         printf("Case 1: Positive Integer\n");
          uint32 a_u32[100],i_u32=0;
          sint32 b_s32=decimalNumber_s32;
          while (b_s32 > 15)
          {
           a_u32[i_u32]=b_s32 %16;
           b_s32 = b_s32/16;
           i_u32++;

          }
          a_u32[i_u32]=b_s32;
          printf("Hexadecimal equivalent is  ");
          printHex(a_u32, i_u32);

     }
     else {
         printf("Case 2: Negative Integer\n");
         //1- convert first to two´s complement signed binary

         // Convert number to binary
         uint32 c_u32=0,a_u32[100];
         sint32 i_s32=0;
         uint64 b_u64=  -((sint64)decimalNumber_s32);
         while (b_u64>1)
         {
            a_u32[i_s32]=b_u64%2;
            b_u64 = b_u64/2;
            i_s32++;
            c_u32++;
         }
         a_u32[i_s32]=b_u64;
         printf("Binary Conversion: ");
         for (i_s32=c_u32;i_s32>=0;--i_s32)
         {
             printf("%lu",a_u32[i_s32]);
         }
         printf("\n");
         // add 0s to have an 8 digit binary number
         if(c_u32<7){
             for(i_s32=1; i_s32<= (7-c_u32); i_s32++){
                 a_u32[c_u32+i_s32] = 0;
             }
             c_u32 = 7;
         }

         // convert to two´s complement by complementing the number and adding 1
         for (i_s32=c_u32;i_s32>=0;--i_s32)
         {
             if(a_u32[i_s32] == 0)
                 a_u32[i_s32] = 1;
             else
                 a_u32[i_s32] = 0;
         }

         // addition of 1

         for (i_s32=0 ; i_s32<=c_u32; ++i_s32)
         {
             if(a_u32[i_s32]==0)
             {
                 a_u32[i_s32]=1;
                 i_s32 = c_u32+1;

             }

            else
            {
                if(a_u32[i_s32]==1)
                {
                    a_u32[i_s32]=0;
                }
            }
         }
         printf("Two`s Complement: ");
         for (i_s32=c_u32;i_s32>=0;--i_s32)
         {
             printf("%lu",a_u32[i_s32]);
         }


         //2- convert that binary value to hexadecimal
         uint32 j_u32 = ((c_u32+1)/4);
         uint32 sum_u32 = 0;
         uint32 hex_u32[100];

         for (i_s32=c_u32 ; i_s32>=0; i_s32 = i_s32-4){

                 if(a_u32[i_s32] == 1){
                     a_u32[i_s32] = 8;

                 }
                 if(i_s32 - 1 >= 0){
                     if(a_u32[i_s32-1] == 1){
                         a_u32[i_s32-1] = 4;
                     }
                 }
                 else{
                     sum_u32 = a_u32[i_s32];
                     hex_u32[j_u32] = sum_u32;
                     break;
                 }


                 if(i_s32 - 2 >= 0){
                     if(a_u32[i_s32-2] == 1){
                         a_u32[i_s32-2] = 2;
                     }
                 }
                 else{
                     sum_u32 = a_u32[i_s32] + a_u32[i_s32-1];
                     hex_u32[j_u32] = sum_u32;
                     break;
                 }


                 if(i_s32 - 3 >= 0){
                     if(a_u32[i_s32-3] == 1){
                         a_u32[i_s32-3] = 1;
                         sum_u32 = a_u32[i_s32] + a_u32[i_s32-1] + a_u32[i_s32-2] + a_u32[i_s32-3];
                         hex_u32[j_u32] = sum_u32;
                     }
                 }
                 else{
                     sum_u32 = a_u32[i_s32] + a_u32[i_s32-1] + a_u32[i_s32-2];
                     hex_u32[j_u32] = sum_u32;
                     break;
                 }
                 j_u32--;
         }
         printf("\nHexadecimal equivalent is  ");
         printHex(hex_u32, ((c_u32+1)/4));


     }
     return;
 }

static void printHex(uint32 hex_u32[], uint32 c_u32){
     sint32 i_s32;
     for (i_s32=c_u32 ; i_s32>=0; --i_s32)
     {
                 if (hex_u32[i_s32]==10)
                     printf("A");
                 else if (hex_u32[i_s32]==11)
                     printf("B");
                 else if (hex_u32[i_s32]==12)
                     printf("C");
                 else if (hex_u32[i_s32]==13)
                     printf("D");
                 else if (hex_u32[i_s32]==14)
                     printf("E");
                 else if (hex_u32[i_s32]==15)
                     printf("F");
                 else
                     printf("%lu",hex_u32[i_s32]);
    }

 }

int main(void)
{
    while (tclRange_b(0,1))
    {
        if (tclRange_b(0,1)) PUncheckedReturn();
    }

    return 0;
}
