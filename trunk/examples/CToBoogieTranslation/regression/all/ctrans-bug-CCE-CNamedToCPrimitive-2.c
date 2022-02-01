typedef unsigned int UINT16;
struct __anonstruct_S_SYS_TLN_STATES_72 {
   UINT16 Batt_Fail : 1 ;
};
typedef struct __anonstruct_S_SYS_TLN_STATES_72 S_SYS_TLN_STATES;
union __anonunion_U_SYS_TLN_STATES_73 {
   S_SYS_TLN_STATES sStates ;
};
typedef union __anonunion_U_SYS_TLN_STATES_73 U_SYS_TLN_STATES;
struct __anonstruct_S_SYS_TLN_91 {
   U_SYS_TLN_STATES uState ;
};
typedef struct __anonstruct_S_SYS_TLN_91 S_SYS_TLN;
S_SYS_TLN sSYS_Me ;
void ADC_CheckEventMessage(      )
{
    sSYS_Me.uState.sStates.Batt_Fail = 0;
}
