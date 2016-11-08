/*
 * DD 2016-10-11
 * SVCOMP benchmark ldv-linux-4.2-rc1\linux-4.2-rc1.tar.xz-43_2a-drivers--block--DAC960.ko-entry_point_true-unreach-call.cil.out.c contains struct with unnamed fields, which violates C11 
 * https://gcc.gnu.org/onlinedocs/gcc/Unnamed-Fields.html
 *
 */

struct __anonstruct_Write_308 {
   unsigned int;
   unsigned char;
};
 
union DAC960_GEM_InboundDoorBellRegister {
    struct __anonstruct_Write_308 Write ;
};

typedef union DAC960_GEM_InboundDoorBellRegister DAC960_GEM_InboundDoorBellRegister_T;

int main() 
{ 
  DAC960_GEM_InboundDoorBellRegister_T InboundDoorBellRegister ;
}
