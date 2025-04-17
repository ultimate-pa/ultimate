//#SAFE
/*---------------------------------------------------------------------------------------------------------------------
 * Program skeleton of a firmware for an PSoC microcontroller with interrupt handling to read out a force sensor.
 * The interrupt service routines from the interrupt-driven program are transformed to a behavior equivalent
 * thread-based program. The thread-based program can be verified by Ultimate Automizer and GemCutter.
 *---------------------------------------------------------------------------------------------------------------------
 * Author: Manuel Bentele
 * Author: Jan Körner
 *-------------------------------------------------------------------------------------------------------------------*/

void __assert (const char *, int, const char *)
     __attribute__ ((__noreturn__));
void __assert_func (const char *, int, const char *, const char *)
     __attribute__ ((__noreturn__));
typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef short int __int16_t;
typedef short unsigned int __uint16_t;
typedef long int __int32_t;
typedef long unsigned int __uint32_t;
typedef long long int __int64_t;
typedef long long unsigned int __uint64_t;
typedef signed char __int_least8_t;
typedef unsigned char __uint_least8_t;
typedef short int __int_least16_t;
typedef short unsigned int __uint_least16_t;
typedef long int __int_least32_t;
typedef long unsigned int __uint_least32_t;
typedef long long int __int_least64_t;
typedef long long unsigned int __uint_least64_t;
typedef long long int __intmax_t;
typedef long long unsigned int __uintmax_t;
typedef int __intptr_t;
typedef unsigned int __uintptr_t;

typedef __int8_t int8_t ;
typedef __uint8_t uint8_t ;
typedef __int16_t int16_t ;
typedef __uint16_t uint16_t ;
typedef __int32_t int32_t ;
typedef __uint32_t uint32_t ;
typedef __int64_t int64_t ;
typedef __uint64_t uint64_t ;
typedef __intmax_t intmax_t;
typedef __uintmax_t uintmax_t;
typedef __intptr_t intptr_t;
typedef __uintptr_t uintptr_t;
typedef __int_least8_t int_least8_t;
typedef __uint_least8_t uint_least8_t;
typedef __int_least16_t int_least16_t;
typedef __uint_least16_t uint_least16_t;
typedef __int_least32_t int_least32_t;
typedef __uint_least32_t uint_least32_t;
typedef __int_least64_t int_least64_t;
typedef __uint_least64_t uint_least64_t;
  typedef int int_fast8_t;
  typedef unsigned int uint_fast8_t;
  typedef int int_fast16_t;
  typedef unsigned int uint_fast16_t;
  typedef int int_fast32_t;
  typedef unsigned int uint_fast32_t;
  typedef long long int int_fast64_t;
  typedef long long unsigned int uint_fast64_t;

typedef enum
{
    CY_RSLT_TYPE_INFO = 0U,
    CY_RSLT_TYPE_WARNING = 1U,
    CY_RSLT_TYPE_ERROR = 2U,
    CY_RSLT_TYPE_FATAL = 3U
} cy_en_rslt_type_t;
typedef enum
{
    CY_RSLT_MODULE_DRIVER_SAR = 0x0001,
    CY_RSLT_MODULE_DRIVER_DFU = 0x0006,
    CY_RSLT_MODULE_DRIVER_CAPSENSE = 0x0007,
    CY_RSLT_MODULE_DRIVER_USB_DEV = 0x0008,
    CY_RSLT_MODULE_DRIVER_CTB = 0x000b,
    CY_RSLT_MODULE_DRIVER_CRYPTO = 0x000c,
    CY_RSLT_MODULE_DRIVER_SYSPM = 0x0010,
    CY_RSLT_MODULE_DRIVER_SYSLIB = 0x0011,
    CY_RSLT_MODULE_DRIVER_SYSCLK = 0x0012,
    CY_RSLT_MODULE_DRIVER_DMA = 0x0013,
    CY_RSLT_MODULE_DRIVER_FLASH = 0x0014,
    CY_RSLT_MODULE_DRIVER_SYSINT = 0x0015,
    CY_RSLT_MODULE_DRIVER_GPIO = 0x0016,
    CY_RSLT_MODULE_DRIVER_SYSANALOG = 0x0017,
    CY_RSLT_MODULE_DRIVER_CTDAC = 0x0019,
    CY_RSLT_MODULE_DRIVER_EFUSE = 0x001a,
    CY_RSLT_MODULE_DRIVER_EM_EEPROM = 0x001b,
    CY_RSLT_MODULE_DRIVER_PROFILE = 0x001e,
    CY_RSLT_MODULE_DRIVER_I2S = 0x0020,
    CY_RSLT_MODULE_DRIVER_IPC = 0x0022,
    CY_RSLT_MODULE_DRIVER_LPCOMP = 0x0023,
    CY_RSLT_MODULE_DRIVER_PDM_PCM = 0x0026,
    CY_RSLT_MODULE_DRIVER_RTC = 0x0028,
    CY_RSLT_MODULE_DRIVER_SCB = 0x002a,
    CY_RSLT_MODULE_DRIVER_SMIF = 0x002c,
    CY_RSLT_MODULE_DRIVER_TCPWM = 0x002d,
    CY_RSLT_MODULE_DRIVER_PROT = 0x0030,
    CY_RSLT_MODULE_DRIVER_TRIGMUX = 0x0033,
    CY_RSLT_MODULE_DRIVER_WDT = 0x0034,
    CY_RSLT_MODULE_DRIVER_MCWDT = 0x0035,
    CY_RSLT_MODULE_DRIVER_LIN = 0x0037,
    CY_RSLT_MODULE_DRIVER_LVD = 0x0039,
    CY_RSLT_MODULE_DRIVER_SD_HOST = 0x003a,
    CY_RSLT_MODULE_DRIVER_USBFS = 0x003b,
    CY_RSLT_MODULE_DRIVER_DMAC = 0x003f,
    CY_RSLT_MODULE_DRIVER_SEGLCD = 0x0040,
    CY_RSLT_MODULE_DRIVER_CSD = 0x0041,
    CY_RSLT_MODULE_DRIVER_SMARTIO = 0x0042,
    CY_RSLT_MODULE_DRIVER_CSDIDAC = 0x0044,
    CY_RSLT_MODULE_DRIVER_CANFD = 0x0045,
    CY_RSLT_MODULE_DRIVER_PRA = 0x0046,
    CY_RSLT_MODULE_DRIVER_MSC = 0x0047,
    CY_RSLT_MODULE_DRIVER_ADCMIC = 0x0048,
    CY_RSLT_MODULE_DRIVER_MSCLP = 0x0049,
    CY_RSLT_MODULE_DRIVER_EVTGEN = 0x004a,
    CY_RSLT_MODULE_DRIVER_SAR2 = 0x004b,
    CY_RSLT_MODULE_DRIVER_KEYSCAN = 0x0072,
    CY_RSLT_MODULE_DRIVER_PDM_PCM2 = 0x0073,
    CY_RSLT_MODULE_DRIVER_CRYPTOLITE = 0x0074,
    CY_RSLT_MODULE_DRIVER_SYSFAULT = 0x0076,
    CY_RSLT_MODULE_DRIVER_LVD_HT = 0x0078,
    CY_RSLT_MODULE_DRIVER_WHD = 0x0080,
    CY_RSLT_MODULE_ABSTRACTION_HAL = 0x0100,
    CY_RSLT_MODULE_ABSTRACTION_BSP = 0x0180,
    CY_RSLT_MODULE_ABSTRACTION_FS = 0x0181,
    CY_RSLT_MODULE_ABSTRACTION_RESOURCE = 0x0182,
    CY_RSLT_MODULE_ABSTRACTION_OS = 0x0183,
    CY_RSLT_MODULE_ABSTRACTION_DATA_STREAMING= 0x0184,
    CY_RSLT_MODULE_ABSTRACTION_BLOCK_STORAGE= 0x0185,
    CY_RSLT_MODULE_BOARD_LIB_RETARGET_IO = 0x1A0,
    CY_RSLT_MODULE_BOARD_LIB_RGB_LED = 0x01A1,
    CY_RSLT_MODULE_BOARD_LIB_SERIAL_FLASH = 0x01A2,
    CY_RSLT_MODULE_BOARD_LIB_WHD_INTEGRATION = 0x01A3,
    CY_RSLT_MODULE_BOARD_SHIELD_028_EPD = 0x01B8,
    CY_RSLT_MODULE_BOARD_SHIELD_028_TFT = 0x01B9,
    CY_RSLT_MODULE_BOARD_SHIELD_032 = 0x01BA,
    CY_RSLT_MODULE_BOARD_SHIELD_028_SENSE = 0x01BB,
    CY_RSLT_MODULE_BOARD_HARDWARE_BMI160 = 0x01C0,
    CY_RSLT_MODULE_BOARD_HARDWARE_E2271CS021 = 0x01C1,
    CY_RSLT_MODULE_BOARD_HARDWARE_THERMISTOR = 0x01C2,
    CY_RSLT_MODULE_BOARD_HARDWARE_SSD1306 = 0x01C3,
    CY_RSLT_MODULE_BOARD_HARDWARE_ST7789V = 0x01C4,
    CY_RSLT_MODULE_BOARD_HARDWARE_LIGHT_SENSOR = 0x01C5,
    CY_RSLT_MODULE_BOARD_HARDWARE_AK4954A = 0x01C6,
    CY_RSLT_MODULE_BOARD_HARDWARE_BMX160 = 0x01C7,
    CY_RSLT_MODULE_BOARD_HARDWARE_DPS3XX = 0x01C8,
    CY_RSLT_MODULE_BOARD_HARDWARE_WM8960 = 0x01C9,
    CY_RSLT_MODULE_BOARD_HARDWARE_XENSIV_PASCO2 = 0x01CA,
    CY_RSLT_MODULE_BOARD_HARDWARE_XENSIV_BGT60TRXX = 0x01CC,
    CY_RSLT_MODULE_BOARD_HARDWARE_LM49450 = 0x01CE,
    CY_RSLT_MODULE_BOARD_HARDWARE_TLV320DAC3100 = 0x01CF,
    CY_RSLT_MODULE_MIDDLEWARE_MNDS = 0x200,
    CY_RSLT_MODULE_MIDDLEWARE_AWS = 0x201,
    CY_RSLT_MODULE_MIDDLEWARE_JSON = 0x202,
    CY_RSLT_MODULE_MIDDLEWARE_LINKED_LIST = 0x203,
    CY_RSLT_MODULE_MIDDLEWARE_COMMAND_CONSOLE = 0x204,
    CY_RSLT_MODULE_MIDDLEWARE_HTTP_SERVER = 0x205,
    CY_RSLT_MODULE_MIDDLEWARE_ENTERPRISE_SECURITY = 0x206,
    CY_RSLT_MODULE_MIDDLEWARE_TCPIP = 0x207,
    CY_RSLT_MODULE_MIDDLEWARE_MW = 0x208,
    CY_RSLT_MODULE_MIDDLEWARE_TLS = 0x209,
    CY_RSLT_MODULE_MIDDLEWARE_SECURE_SOCKETS = 0x20a,
    CY_RSLT_MODULE_MIDDLEWARE_WCM = 0x20b,
    CY_RSLT_MODULE_MIDDLEWARE_LWIP_WHD_PORT = 0x20c,
    CY_RSLT_MODULE_MIDDLEWARE_OTA_UPDATE = 0x20d,
    CY_RSLT_MODULE_MIDDLEWARE_HTTP_CLIENT = 0x20e,
    CY_RSLT_MODULE_MIDDLEWARE_ML = 0x20f,
    CY_RSLT_MODULE_MIDDLEWARE_EM_EEPROM = 0x24f,
    CY_RSLT_MODULE_MIDDLEWARE_KVSTORE = 0x250,
    CY_RSLT_MODULE_MIDDLEWARE_LIN = 0x0251,
    CY_RSLT_MODULE_MIDDLEWARE_UBM = 0x0252,
    CY_RSLT_MODULE_MIDDLEWARE_KVSTORE_CAT5 = 0x0253
} cy_en_rslt_module_t;
typedef uint32_t cy_rslt_t;
typedef union
{
    cy_rslt_t raw;
    struct
    {
        uint16_t code : (16U);
        cy_en_rslt_type_t type : (2U);
        cy_en_rslt_module_t module : (14U);
    };
} cy_rslt_decode_t;

typedef int ptrdiff_t;
typedef unsigned int size_t;
typedef unsigned int wchar_t;
typedef struct {
  long long __max_align_ll __attribute__((__aligned__(__alignof__(long long))));
  long double __max_align_ld __attribute__((__aligned__(__alignof__(long double))));
} max_align_t;
typedef enum {
  Reset_IRQn = -15,
  NonMaskableInt_IRQn = -14,
  HardFault_IRQn = -13,
  MemoryManagement_IRQn = -12,
  BusFault_IRQn = -11,
  UsageFault_IRQn = -10,
  SVCall_IRQn = -5,
  DebugMonitor_IRQn = -4,
  PendSV_IRQn = -2,
  SysTick_IRQn = -1,
  ioss_interrupts_gpio_0_IRQn = 0,
  ioss_interrupts_gpio_1_IRQn = 1,
  ioss_interrupts_gpio_2_IRQn = 2,
  ioss_interrupts_gpio_3_IRQn = 3,
  ioss_interrupts_gpio_4_IRQn = 4,
  ioss_interrupts_gpio_5_IRQn = 5,
  ioss_interrupts_gpio_6_IRQn = 6,
  ioss_interrupts_gpio_7_IRQn = 7,
  ioss_interrupts_gpio_8_IRQn = 8,
  ioss_interrupts_gpio_9_IRQn = 9,
  ioss_interrupts_gpio_10_IRQn = 10,
  ioss_interrupts_gpio_11_IRQn = 11,
  ioss_interrupts_gpio_12_IRQn = 12,
  ioss_interrupts_gpio_13_IRQn = 13,
  ioss_interrupts_gpio_14_IRQn = 14,
  ioss_interrupt_gpio_IRQn = 15,
  ioss_interrupt_vdd_IRQn = 16,
  lpcomp_interrupt_IRQn = 17,
  scb_8_interrupt_IRQn = 18,
  srss_interrupt_mcwdt_0_IRQn = 19,
  srss_interrupt_mcwdt_1_IRQn = 20,
  srss_interrupt_backup_IRQn = 21,
  srss_interrupt_IRQn = 22,
  pass_interrupt_ctbs_IRQn = 23,
  bless_interrupt_IRQn = 24,
  cpuss_interrupts_ipc_0_IRQn = 25,
  cpuss_interrupts_ipc_1_IRQn = 26,
  cpuss_interrupts_ipc_2_IRQn = 27,
  cpuss_interrupts_ipc_3_IRQn = 28,
  cpuss_interrupts_ipc_4_IRQn = 29,
  cpuss_interrupts_ipc_5_IRQn = 30,
  cpuss_interrupts_ipc_6_IRQn = 31,
  cpuss_interrupts_ipc_7_IRQn = 32,
  cpuss_interrupts_ipc_8_IRQn = 33,
  cpuss_interrupts_ipc_9_IRQn = 34,
  cpuss_interrupts_ipc_10_IRQn = 35,
  cpuss_interrupts_ipc_11_IRQn = 36,
  cpuss_interrupts_ipc_12_IRQn = 37,
  cpuss_interrupts_ipc_13_IRQn = 38,
  cpuss_interrupts_ipc_14_IRQn = 39,
  cpuss_interrupts_ipc_15_IRQn = 40,
  scb_0_interrupt_IRQn = 41,
  scb_1_interrupt_IRQn = 42,
  scb_2_interrupt_IRQn = 43,
  scb_3_interrupt_IRQn = 44,
  scb_4_interrupt_IRQn = 45,
  scb_5_interrupt_IRQn = 46,
  scb_6_interrupt_IRQn = 47,
  scb_7_interrupt_IRQn = 48,
  csd_interrupt_IRQn = 49,
  cpuss_interrupts_dw0_0_IRQn = 50,
  cpuss_interrupts_dw0_1_IRQn = 51,
  cpuss_interrupts_dw0_2_IRQn = 52,
  cpuss_interrupts_dw0_3_IRQn = 53,
  cpuss_interrupts_dw0_4_IRQn = 54,
  cpuss_interrupts_dw0_5_IRQn = 55,
  cpuss_interrupts_dw0_6_IRQn = 56,
  cpuss_interrupts_dw0_7_IRQn = 57,
  cpuss_interrupts_dw0_8_IRQn = 58,
  cpuss_interrupts_dw0_9_IRQn = 59,
  cpuss_interrupts_dw0_10_IRQn = 60,
  cpuss_interrupts_dw0_11_IRQn = 61,
  cpuss_interrupts_dw0_12_IRQn = 62,
  cpuss_interrupts_dw0_13_IRQn = 63,
  cpuss_interrupts_dw0_14_IRQn = 64,
  cpuss_interrupts_dw0_15_IRQn = 65,
  cpuss_interrupts_dw1_0_IRQn = 66,
  cpuss_interrupts_dw1_1_IRQn = 67,
  cpuss_interrupts_dw1_2_IRQn = 68,
  cpuss_interrupts_dw1_3_IRQn = 69,
  cpuss_interrupts_dw1_4_IRQn = 70,
  cpuss_interrupts_dw1_5_IRQn = 71,
  cpuss_interrupts_dw1_6_IRQn = 72,
  cpuss_interrupts_dw1_7_IRQn = 73,
  cpuss_interrupts_dw1_8_IRQn = 74,
  cpuss_interrupts_dw1_9_IRQn = 75,
  cpuss_interrupts_dw1_10_IRQn = 76,
  cpuss_interrupts_dw1_11_IRQn = 77,
  cpuss_interrupts_dw1_12_IRQn = 78,
  cpuss_interrupts_dw1_13_IRQn = 79,
  cpuss_interrupts_dw1_14_IRQn = 80,
  cpuss_interrupts_dw1_15_IRQn = 81,
  cpuss_interrupts_fault_0_IRQn = 82,
  cpuss_interrupts_fault_1_IRQn = 83,
  cpuss_interrupt_crypto_IRQn = 84,
  cpuss_interrupt_fm_IRQn = 85,
  cpuss_interrupts_cm0_cti_0_IRQn = 86,
  cpuss_interrupts_cm0_cti_1_IRQn = 87,
  cpuss_interrupts_cm4_cti_0_IRQn = 88,
  cpuss_interrupts_cm4_cti_1_IRQn = 89,
  tcpwm_0_interrupts_0_IRQn = 90,
  tcpwm_0_interrupts_1_IRQn = 91,
  tcpwm_0_interrupts_2_IRQn = 92,
  tcpwm_0_interrupts_3_IRQn = 93,
  tcpwm_0_interrupts_4_IRQn = 94,
  tcpwm_0_interrupts_5_IRQn = 95,
  tcpwm_0_interrupts_6_IRQn = 96,
  tcpwm_0_interrupts_7_IRQn = 97,
  tcpwm_1_interrupts_0_IRQn = 98,
  tcpwm_1_interrupts_1_IRQn = 99,
  tcpwm_1_interrupts_2_IRQn = 100,
  tcpwm_1_interrupts_3_IRQn = 101,
  tcpwm_1_interrupts_4_IRQn = 102,
  tcpwm_1_interrupts_5_IRQn = 103,
  tcpwm_1_interrupts_6_IRQn = 104,
  tcpwm_1_interrupts_7_IRQn = 105,
  tcpwm_1_interrupts_8_IRQn = 106,
  tcpwm_1_interrupts_9_IRQn = 107,
  tcpwm_1_interrupts_10_IRQn = 108,
  tcpwm_1_interrupts_11_IRQn = 109,
  tcpwm_1_interrupts_12_IRQn = 110,
  tcpwm_1_interrupts_13_IRQn = 111,
  tcpwm_1_interrupts_14_IRQn = 112,
  tcpwm_1_interrupts_15_IRQn = 113,
  tcpwm_1_interrupts_16_IRQn = 114,
  tcpwm_1_interrupts_17_IRQn = 115,
  tcpwm_1_interrupts_18_IRQn = 116,
  tcpwm_1_interrupts_19_IRQn = 117,
  tcpwm_1_interrupts_20_IRQn = 118,
  tcpwm_1_interrupts_21_IRQn = 119,
  tcpwm_1_interrupts_22_IRQn = 120,
  tcpwm_1_interrupts_23_IRQn = 121,
  udb_interrupts_0_IRQn = 122,
  udb_interrupts_1_IRQn = 123,
  udb_interrupts_2_IRQn = 124,
  udb_interrupts_3_IRQn = 125,
  udb_interrupts_4_IRQn = 126,
  udb_interrupts_5_IRQn = 127,
  udb_interrupts_6_IRQn = 128,
  udb_interrupts_7_IRQn = 129,
  udb_interrupts_8_IRQn = 130,
  udb_interrupts_9_IRQn = 131,
  udb_interrupts_10_IRQn = 132,
  udb_interrupts_11_IRQn = 133,
  udb_interrupts_12_IRQn = 134,
  udb_interrupts_13_IRQn = 135,
  udb_interrupts_14_IRQn = 136,
  udb_interrupts_15_IRQn = 137,
  pass_interrupt_sar_IRQn = 138,
  audioss_interrupt_i2s_IRQn = 139,
  audioss_interrupt_pdm_IRQn = 140,
  profile_interrupt_IRQn = 141,
  smif_interrupt_IRQn = 142,
  usb_interrupt_hi_IRQn = 143,
  usb_interrupt_med_IRQn = 144,
  usb_interrupt_lo_IRQn = 145,
  pass_interrupt_dacs_IRQn = 146,
  unconnected_IRQn = 240
} IRQn_Type;
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wsign-conversion"
#pragma GCC diagnostic ignored "-Wconversion"
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpacked"
#pragma GCC diagnostic ignored "-Wattributes"
  struct __attribute__((packed)) T_UINT32 { uint32_t v; };
#pragma GCC diagnostic pop
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpacked"
#pragma GCC diagnostic ignored "-Wattributes"
  struct __attribute__((packed, aligned(1))) T_UINT16_WRITE { uint16_t v; };
#pragma GCC diagnostic pop
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpacked"
#pragma GCC diagnostic ignored "-Wattributes"
  struct __attribute__((packed, aligned(1))) T_UINT16_READ { uint16_t v; };
#pragma GCC diagnostic pop
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpacked"
#pragma GCC diagnostic ignored "-Wattributes"
  struct __attribute__((packed, aligned(1))) T_UINT32_WRITE { uint32_t v; };
#pragma GCC diagnostic pop
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpacked"
#pragma GCC diagnostic ignored "-Wattributes"
  struct __attribute__((packed, aligned(1))) T_UINT32_READ { uint32_t v; };
#pragma GCC diagnostic pop
__attribute__((always_inline)) static inline __attribute__((__noreturn__)) void __cmsis_start(void)
{
  extern void _start(void) __attribute__((__noreturn__));
  typedef struct {
    uint32_t const* src;
    uint32_t* dest;
    uint32_t wlen;
  } __copy_table_t;
  typedef struct {
    uint32_t* dest;
    uint32_t wlen;
  } __zero_table_t;
  extern const __copy_table_t __copy_table_start__;
  extern const __copy_table_t __copy_table_end__;
  extern const __zero_table_t __zero_table_start__;
  extern const __zero_table_t __zero_table_end__;
  for (__copy_table_t const* pTable = &__copy_table_start__; pTable < &__copy_table_end__; ++pTable) {
    for(uint32_t i=0u; i<pTable->wlen; ++i) {
      pTable->dest[i] = pTable->src[i];
    }
  }
  for (__zero_table_t const* pTable = &__zero_table_start__; pTable < &__zero_table_end__; ++pTable) {
    for(uint32_t i=0u; i<pTable->wlen; ++i) {
      pTable->dest[i] = 0u;
    }
  }
  _start();
}
__attribute__((always_inline)) static inline void __ISB(void)
{
  __asm volatile ("isb 0xF":::"memory");
}
__attribute__((always_inline)) static inline void __DSB(void)
{
  __asm volatile ("dsb 0xF":::"memory");
}
__attribute__((always_inline)) static inline void __DMB(void)
{
  __asm volatile ("dmb 0xF":::"memory");
}
__attribute__((always_inline)) static inline uint32_t __REV(uint32_t value)
{
  return __builtin_bswap32(value);
}
__attribute__((always_inline)) static inline uint32_t __REV16(uint32_t value)
{
  uint32_t result;
  __asm ("rev16 %0, %1" : "=r" (result) : "r" (value) );
  return result;
}
__attribute__((always_inline)) static inline int16_t __REVSH(int16_t value)
{
  return (int16_t)__builtin_bswap16(value);
}
__attribute__((always_inline)) static inline uint32_t __ROR(uint32_t op1, uint32_t op2)
{
  op2 %= 32U;
  if (op2 == 0U)
  {
    return op1;
  }
  return (op1 >> op2) | (op1 << (32U - op2));
}
__attribute__((always_inline)) static inline uint32_t __RBIT(uint32_t value)
{
  uint32_t result;
  uint32_t s = (4U * 8U) - 1U;
  result = value;
  for (value >>= 1U; value != 0U; value >>= 1U)
  {
    result <<= 1U;
    result |= value & 1U;
    s--;
  }
  result <<= s;
  return result;
}
__attribute__((always_inline)) static inline uint8_t __CLZ(uint32_t value)
{
  if (value == 0U)
  {
    return 32U;
  }
  return __builtin_clz(value);
}
__attribute__((always_inline)) static inline int32_t __SSAT(int32_t val, uint32_t sat)
{
  if ((sat >= 1U) && (sat <= 32U))
  {
    const int32_t max = (int32_t)((1U << (sat - 1U)) - 1U);
    const int32_t min = -1 - max ;
    if (val > max)
    {
      return max;
    }
    else if (val < min)
    {
      return min;
    }
  }
  return val;
}
__attribute__((always_inline)) static inline uint32_t __USAT(int32_t val, uint32_t sat)
{
  if (sat <= 31U)
  {
    const uint32_t max = ((1U << sat) - 1U);
    if (val > (int32_t)max)
    {
      return max;
    }
    else if (val < 0)
    {
      return 0U;
    }
  }
  return (uint32_t)val;
}
__attribute__((always_inline)) static inline void __enable_irq(void)
{
  __asm volatile ("cpsie i" : : : "memory");
}
__attribute__((always_inline)) static inline void __disable_irq(void)
{
  __asm volatile ("cpsid i" : : : "memory");
}
__attribute__((always_inline)) static inline uint32_t __get_CONTROL(void)
{
  uint32_t result;
  __asm volatile ("MRS %0, control" : "=r" (result) );
  return(result);
}
__attribute__((always_inline)) static inline void __set_CONTROL(uint32_t control)
{
  __asm volatile ("MSR control, %0" : : "r" (control) : "memory");
  __ISB();
}
__attribute__((always_inline)) static inline uint32_t __get_IPSR(void)
{
  uint32_t result;
  __asm volatile ("MRS %0, ipsr" : "=r" (result) );
  return(result);
}
__attribute__((always_inline)) static inline uint32_t __get_APSR(void)
{
  uint32_t result;
  __asm volatile ("MRS %0, apsr" : "=r" (result) );
  return(result);
}
__attribute__((always_inline)) static inline uint32_t __get_xPSR(void)
{
  uint32_t result;
  __asm volatile ("MRS %0, xpsr" : "=r" (result) );
  return(result);
}
__attribute__((always_inline)) static inline uint32_t __get_PSP(void)
{
  uint32_t result;
  __asm volatile ("MRS %0, psp" : "=r" (result) );
  return(result);
}
__attribute__((always_inline)) static inline void __set_PSP(uint32_t topOfProcStack)
{
  __asm volatile ("MSR psp, %0" : : "r" (topOfProcStack) : );
}
__attribute__((always_inline)) static inline uint32_t __get_MSP(void)
{
  uint32_t result;
  __asm volatile ("MRS %0, msp" : "=r" (result) );
  return(result);
}
__attribute__((always_inline)) static inline void __set_MSP(uint32_t topOfMainStack)
{
  __asm volatile ("MSR msp, %0" : : "r" (topOfMainStack) : );
}
__attribute__((always_inline)) static inline uint32_t __get_PRIMASK(void)
{
  uint32_t result;
  __asm volatile ("MRS %0, primask" : "=r" (result) );
  return(result);
}
__attribute__((always_inline)) static inline void __set_PRIMASK(uint32_t priMask)
{
  __asm volatile ("MSR primask, %0" : : "r" (priMask) : "memory");
}
__attribute__((always_inline)) static inline uint32_t __get_FPSCR(void)
{
  return(0U);
}
__attribute__((always_inline)) static inline void __set_FPSCR(uint32_t fpscr)
{
  (void)fpscr;
}
#pragma GCC diagnostic pop
typedef union
{
  struct
  {
    uint32_t _reserved0:16;
    uint32_t GE:4;
    uint32_t _reserved1:7;
    uint32_t Q:1;
    uint32_t V:1;
    uint32_t C:1;
    uint32_t Z:1;
    uint32_t N:1;
  } b;
  uint32_t w;
} APSR_Type;
typedef union
{
  struct
  {
    uint32_t ISR:9;
    uint32_t _reserved0:23;
  } b;
  uint32_t w;
} IPSR_Type;
typedef union
{
  struct
  {
    uint32_t ISR:9;
    uint32_t _reserved0:1;
    uint32_t ICI_IT_1:6;
    uint32_t GE:4;
    uint32_t _reserved1:4;
    uint32_t T:1;
    uint32_t ICI_IT_2:2;
    uint32_t Q:1;
    uint32_t V:1;
    uint32_t C:1;
    uint32_t Z:1;
    uint32_t N:1;
  } b;
  uint32_t w;
} xPSR_Type;
typedef union
{
  struct
  {
    uint32_t nPRIV:1;
    uint32_t SPSEL:1;
    uint32_t FPCA:1;
    uint32_t _reserved0:29;
  } b;
  uint32_t w;
} CONTROL_Type;
typedef struct
{
  volatile uint32_t ISER[8U];
        uint32_t RESERVED0[24U];
  volatile uint32_t ICER[8U];
        uint32_t RESERVED1[24U];
  volatile uint32_t ISPR[8U];
        uint32_t RESERVED2[24U];
  volatile uint32_t ICPR[8U];
        uint32_t RESERVED3[24U];
  volatile uint32_t IABR[8U];
        uint32_t RESERVED4[56U];
  volatile uint8_t IP[240U];
        uint32_t RESERVED5[644U];
  volatile uint32_t STIR;
} NVIC_Type;
typedef struct
{
  volatile const uint32_t CPUID;
  volatile uint32_t ICSR;
  volatile uint32_t VTOR;
  volatile uint32_t AIRCR;
  volatile uint32_t SCR;
  volatile uint32_t CCR;
  volatile uint8_t SHP[12U];
  volatile uint32_t SHCSR;
  volatile uint32_t CFSR;
  volatile uint32_t HFSR;
  volatile uint32_t DFSR;
  volatile uint32_t MMFAR;
  volatile uint32_t BFAR;
  volatile uint32_t AFSR;
  volatile const uint32_t PFR[2U];
  volatile const uint32_t DFR;
  volatile const uint32_t ADR;
  volatile const uint32_t MMFR[4U];
  volatile const uint32_t ISAR[5U];
        uint32_t RESERVED0[5U];
  volatile uint32_t CPACR;
} SCB_Type;
typedef struct
{
        uint32_t RESERVED0[1U];
  volatile const uint32_t ICTR;
  volatile uint32_t ACTLR;
} SCnSCB_Type;
typedef struct
{
  volatile uint32_t CTRL;
  volatile uint32_t LOAD;
  volatile uint32_t VAL;
  volatile const uint32_t CALIB;
} SysTick_Type;
typedef struct
{
  volatile union
  {
    volatile uint8_t u8;
    volatile uint16_t u16;
    volatile uint32_t u32;
  } PORT [32U];
        uint32_t RESERVED0[864U];
  volatile uint32_t TER;
        uint32_t RESERVED1[15U];
  volatile uint32_t TPR;
        uint32_t RESERVED2[15U];
  volatile uint32_t TCR;
        uint32_t RESERVED3[32U];
        uint32_t RESERVED4[43U];
  volatile uint32_t LAR;
  volatile const uint32_t LSR;
        uint32_t RESERVED5[6U];
  volatile const uint32_t PID4;
  volatile const uint32_t PID5;
  volatile const uint32_t PID6;
  volatile const uint32_t PID7;
  volatile const uint32_t PID0;
  volatile const uint32_t PID1;
  volatile const uint32_t PID2;
  volatile const uint32_t PID3;
  volatile const uint32_t CID0;
  volatile const uint32_t CID1;
  volatile const uint32_t CID2;
  volatile const uint32_t CID3;
} ITM_Type;
typedef struct
{
  volatile uint32_t CTRL;
  volatile uint32_t CYCCNT;
  volatile uint32_t CPICNT;
  volatile uint32_t EXCCNT;
  volatile uint32_t SLEEPCNT;
  volatile uint32_t LSUCNT;
  volatile uint32_t FOLDCNT;
  volatile const uint32_t PCSR;
  volatile uint32_t COMP0;
  volatile uint32_t MASK0;
  volatile uint32_t FUNCTION0;
        uint32_t RESERVED0[1U];
  volatile uint32_t COMP1;
  volatile uint32_t MASK1;
  volatile uint32_t FUNCTION1;
        uint32_t RESERVED1[1U];
  volatile uint32_t COMP2;
  volatile uint32_t MASK2;
  volatile uint32_t FUNCTION2;
        uint32_t RESERVED2[1U];
  volatile uint32_t COMP3;
  volatile uint32_t MASK3;
  volatile uint32_t FUNCTION3;
} DWT_Type;
typedef struct
{
  volatile const uint32_t SSPSR;
  volatile uint32_t CSPSR;
        uint32_t RESERVED0[2U];
  volatile uint32_t ACPR;
        uint32_t RESERVED1[55U];
  volatile uint32_t SPPR;
        uint32_t RESERVED2[131U];
  volatile const uint32_t FFSR;
  volatile uint32_t FFCR;
  volatile const uint32_t FSCR;
        uint32_t RESERVED3[759U];
  volatile const uint32_t TRIGGER;
  volatile const uint32_t FIFO0;
  volatile const uint32_t ITATBCTR2;
        uint32_t RESERVED4[1U];
  volatile const uint32_t ITATBCTR0;
  volatile const uint32_t FIFO1;
  volatile uint32_t ITCTRL;
        uint32_t RESERVED5[39U];
  volatile uint32_t CLAIMSET;
  volatile uint32_t CLAIMCLR;
        uint32_t RESERVED7[8U];
  volatile const uint32_t DEVID;
  volatile const uint32_t DEVTYPE;
} TPI_Type;
typedef struct
{
  volatile const uint32_t TYPE;
  volatile uint32_t CTRL;
  volatile uint32_t RNR;
  volatile uint32_t RBAR;
  volatile uint32_t RASR;
  volatile uint32_t RBAR_A1;
  volatile uint32_t RASR_A1;
  volatile uint32_t RBAR_A2;
  volatile uint32_t RASR_A2;
  volatile uint32_t RBAR_A3;
  volatile uint32_t RASR_A3;
} MPU_Type;
typedef struct
{
        uint32_t RESERVED0[1U];
  volatile uint32_t FPCCR;
  volatile uint32_t FPCAR;
  volatile uint32_t FPDSCR;
  volatile const uint32_t MVFR0;
  volatile const uint32_t MVFR1;
  volatile const uint32_t MVFR2;
} FPU_Type;
typedef struct
{
  volatile uint32_t DHCSR;
  volatile uint32_t DCRSR;
  volatile uint32_t DCRDR;
  volatile uint32_t DEMCR;
} CoreDebug_Type;
static inline void __NVIC_SetPriorityGrouping(uint32_t PriorityGroup)
{
  uint32_t reg_value;
  uint32_t PriorityGroupTmp = (PriorityGroup & (uint32_t)0x07UL);
  reg_value = ((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->AIRCR;
  reg_value &= ~((uint32_t)((0xFFFFUL << 16U) | (7UL << 8U)));
  reg_value = (reg_value |
                ((uint32_t)0x5FAUL << 16U) |
                (PriorityGroupTmp << 8U) );
  ((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->AIRCR = reg_value;
}
static inline uint32_t __NVIC_GetPriorityGrouping(void)
{
  return ((uint32_t)((((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->AIRCR & (7UL << 8U)) >> 8U));
}
static inline void __NVIC_EnableIRQ(IRQn_Type IRQn)
{
  if ((int32_t)(IRQn) >= 0)
  {
    __asm volatile("":::"memory");
    ((NVIC_Type *) ((0xE000E000UL) + 0x0100UL) )->ISER[(((uint32_t)IRQn) >> 5UL)] = (uint32_t)(1UL << (((uint32_t)IRQn) & 0x1FUL));
    __asm volatile("":::"memory");
  }
}
static inline uint32_t __NVIC_GetEnableIRQ(IRQn_Type IRQn)
{
  if ((int32_t)(IRQn) >= 0)
  {
    return((uint32_t)(((((NVIC_Type *) ((0xE000E000UL) + 0x0100UL) )->ISER[(((uint32_t)IRQn) >> 5UL)] & (1UL << (((uint32_t)IRQn) & 0x1FUL))) != 0UL) ? 1UL : 0UL));
  }
  else
  {
    return(0U);
  }
}
static inline void __NVIC_DisableIRQ(IRQn_Type IRQn)
{
  if ((int32_t)(IRQn) >= 0)
  {
    ((NVIC_Type *) ((0xE000E000UL) + 0x0100UL) )->ICER[(((uint32_t)IRQn) >> 5UL)] = (uint32_t)(1UL << (((uint32_t)IRQn) & 0x1FUL));
    __DSB();
    __ISB();
  }
}
static inline uint32_t __NVIC_GetPendingIRQ(IRQn_Type IRQn)
{
  if ((int32_t)(IRQn) >= 0)
  {
    return((uint32_t)(((((NVIC_Type *) ((0xE000E000UL) + 0x0100UL) )->ISPR[(((uint32_t)IRQn) >> 5UL)] & (1UL << (((uint32_t)IRQn) & 0x1FUL))) != 0UL) ? 1UL : 0UL));
  }
  else
  {
    return(0U);
  }
}
static inline void __NVIC_SetPendingIRQ(IRQn_Type IRQn)
{
  if ((int32_t)(IRQn) >= 0)
  {
    ((NVIC_Type *) ((0xE000E000UL) + 0x0100UL) )->ISPR[(((uint32_t)IRQn) >> 5UL)] = (uint32_t)(1UL << (((uint32_t)IRQn) & 0x1FUL));
  }
}
static inline void __NVIC_ClearPendingIRQ(IRQn_Type IRQn)
{
  if ((int32_t)(IRQn) >= 0)
  {
    ((NVIC_Type *) ((0xE000E000UL) + 0x0100UL) )->ICPR[(((uint32_t)IRQn) >> 5UL)] = (uint32_t)(1UL << (((uint32_t)IRQn) & 0x1FUL));
  }
}
static inline uint32_t __NVIC_GetActive(IRQn_Type IRQn)
{
  if ((int32_t)(IRQn) >= 0)
  {
    return((uint32_t)(((((NVIC_Type *) ((0xE000E000UL) + 0x0100UL) )->IABR[(((uint32_t)IRQn) >> 5UL)] & (1UL << (((uint32_t)IRQn) & 0x1FUL))) != 0UL) ? 1UL : 0UL));
  }
  else
  {
    return(0U);
  }
}
static inline void __NVIC_SetPriority(IRQn_Type IRQn, uint32_t priority)
{
  if ((int32_t)(IRQn) >= 0)
  {
    ((NVIC_Type *) ((0xE000E000UL) + 0x0100UL) )->IP[((uint32_t)IRQn)] = (uint8_t)((priority << (8U - 3)) & (uint32_t)0xFFUL);
  }
  else
  {
    ((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->SHP[(((uint32_t)IRQn) & 0xFUL)-4UL] = (uint8_t)((priority << (8U - 3)) & (uint32_t)0xFFUL);
  }
}
static inline uint32_t __NVIC_GetPriority(IRQn_Type IRQn)
{
  if ((int32_t)(IRQn) >= 0)
  {
    return(((uint32_t)((NVIC_Type *) ((0xE000E000UL) + 0x0100UL) )->IP[((uint32_t)IRQn)] >> (8U - 3)));
  }
  else
  {
    return(((uint32_t)((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->SHP[(((uint32_t)IRQn) & 0xFUL)-4UL] >> (8U - 3)));
  }
}
static inline uint32_t NVIC_EncodePriority (uint32_t PriorityGroup, uint32_t PreemptPriority, uint32_t SubPriority)
{
  uint32_t PriorityGroupTmp = (PriorityGroup & (uint32_t)0x07UL);
  uint32_t PreemptPriorityBits;
  uint32_t SubPriorityBits;
  PreemptPriorityBits = ((7UL - PriorityGroupTmp) > (uint32_t)(3)) ? (uint32_t)(3) : (uint32_t)(7UL - PriorityGroupTmp);
  SubPriorityBits = ((PriorityGroupTmp + (uint32_t)(3)) < (uint32_t)7UL) ? (uint32_t)0UL : (uint32_t)((PriorityGroupTmp - 7UL) + (uint32_t)(3));
  return (
           ((PreemptPriority & (uint32_t)((1UL << (PreemptPriorityBits)) - 1UL)) << SubPriorityBits) |
           ((SubPriority & (uint32_t)((1UL << (SubPriorityBits )) - 1UL)))
         );
}
static inline void NVIC_DecodePriority (uint32_t Priority, uint32_t PriorityGroup, uint32_t* const pPreemptPriority, uint32_t* const pSubPriority)
{
  uint32_t PriorityGroupTmp = (PriorityGroup & (uint32_t)0x07UL);
  uint32_t PreemptPriorityBits;
  uint32_t SubPriorityBits;
  PreemptPriorityBits = ((7UL - PriorityGroupTmp) > (uint32_t)(3)) ? (uint32_t)(3) : (uint32_t)(7UL - PriorityGroupTmp);
  SubPriorityBits = ((PriorityGroupTmp + (uint32_t)(3)) < (uint32_t)7UL) ? (uint32_t)0UL : (uint32_t)((PriorityGroupTmp - 7UL) + (uint32_t)(3));
  *pPreemptPriority = (Priority >> SubPriorityBits) & (uint32_t)((1UL << (PreemptPriorityBits)) - 1UL);
  *pSubPriority = (Priority ) & (uint32_t)((1UL << (SubPriorityBits )) - 1UL);
}
static inline void __NVIC_SetVector(IRQn_Type IRQn, uint32_t vector)
{
  uint32_t *vectors = (uint32_t *)((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->VTOR;
  vectors[(int32_t)IRQn + 16] = vector;
}
static inline uint32_t __NVIC_GetVector(IRQn_Type IRQn)
{
  uint32_t *vectors = (uint32_t *)((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->VTOR;
  return vectors[(int32_t)IRQn + 16];
}
__attribute__((__noreturn__)) static inline void __NVIC_SystemReset(void)
{
  __DSB();
  ((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->AIRCR = (uint32_t)((0x5FAUL << 16U) |
                           (((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->AIRCR & (7UL << 8U)) |
                            (1UL << 2U) );
  __DSB();
  for(;;)
  {
    __asm volatile ("nop");
  }
}
typedef struct {
  uint32_t RBAR;
  uint32_t RASR;
} ARM_MPU_Region_t;
static inline void ARM_MPU_Enable(uint32_t MPU_Control)
{
  __DMB();
  ((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->CTRL = MPU_Control | (1UL );
  ((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->SHCSR |= (1UL << 16U);
  __DSB();
  __ISB();
}
static inline void ARM_MPU_Disable(void)
{
  __DMB();
  ((SCB_Type *) ((0xE000E000UL) + 0x0D00UL) )->SHCSR &= ~(1UL << 16U);
  ((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->CTRL &= ~(1UL );
  __DSB();
  __ISB();
}
static inline void ARM_MPU_ClrRegion(uint32_t rnr)
{
  ((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->RNR = rnr;
  ((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->RASR = 0U;
}
static inline void ARM_MPU_SetRegion(uint32_t rbar, uint32_t rasr)
{
  ((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->RBAR = rbar;
  ((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->RASR = rasr;
}
static inline void ARM_MPU_SetRegionEx(uint32_t rnr, uint32_t rbar, uint32_t rasr)
{
  ((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->RNR = rnr;
  ((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->RBAR = rbar;
  ((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->RASR = rasr;
}
static inline void ARM_MPU_OrderedMemcpy(volatile uint32_t* dst, const uint32_t* __restrict src, uint32_t len)
{
  uint32_t i;
  for (i = 0U; i < len; ++i)
  {
    dst[i] = src[i];
  }
}
static inline void ARM_MPU_Load(ARM_MPU_Region_t const* table, uint32_t cnt)
{
  const uint32_t rowWordSize = sizeof(ARM_MPU_Region_t)/4U;
  while (cnt > 4U) {
    ARM_MPU_OrderedMemcpy(&(((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->RBAR), &(table->RBAR), 4U*rowWordSize);
    table += 4U;
    cnt -= 4U;
  }
  ARM_MPU_OrderedMemcpy(&(((MPU_Type *) ((0xE000E000UL) + 0x0D90UL) )->RBAR), &(table->RBAR), cnt*rowWordSize);
}
static inline uint32_t SCB_GetFPUType(void)
{
  uint32_t mvfr0;
  mvfr0 = ((FPU_Type *) ((0xE000E000UL) + 0x0F30UL) )->MVFR0;
  if ((mvfr0 & ((0xFUL << 4U) | (0xFUL << 8U))) == 0x020U)
  {
    return 1U;
  }
  else
  {
    return 0U;
  }
}
static inline uint32_t SysTick_Config(uint32_t ticks)
{
  if ((ticks - 1UL) > (0xFFFFFFUL ))
  {
    return (1UL);
  }
  ((SysTick_Type *) ((0xE000E000UL) + 0x0010UL) )->LOAD = (uint32_t)(ticks - 1UL);
  __NVIC_SetPriority (SysTick_IRQn, (1UL << 3) - 1UL);
  ((SysTick_Type *) ((0xE000E000UL) + 0x0010UL) )->VAL = 0UL;
  ((SysTick_Type *) ((0xE000E000UL) + 0x0010UL) )->CTRL = (1UL << 2U) |
                   (1UL << 1U) |
                   (1UL );
  return (0UL);
}
extern volatile int32_t ITM_RxBuffer;
static inline uint32_t ITM_SendChar (uint32_t ch)
{
  if (((((ITM_Type *) (0xE0000000UL) )->TCR & (1UL )) != 0UL) &&
      ((((ITM_Type *) (0xE0000000UL) )->TER & 1UL ) != 0UL) )
  {
    while (((ITM_Type *) (0xE0000000UL) )->PORT[0U].u32 == 0UL)
    {
      __asm volatile ("nop");
    }
    ((ITM_Type *) (0xE0000000UL) )->PORT[0U].u8 = (uint8_t)ch;
  }
  return (ch);
}
static inline int32_t ITM_ReceiveChar (void)
{
  int32_t ch = -1;
  if (ITM_RxBuffer != ((int32_t)0x5AA55AA5U))
  {
    ch = ITM_RxBuffer;
    ITM_RxBuffer = ((int32_t)0x5AA55AA5U);
  }
  return (ch);
}
static inline int32_t ITM_CheckChar (void)
{
  if (ITM_RxBuffer == ((int32_t)0x5AA55AA5U))
  {
    return (0);
  }
  else
  {
    return (1);
  }
}
    extern void SystemInit(void);
extern void SystemCoreClockUpdate(void);
extern uint32_t Cy_SysGetCM4Status(void);
extern void Cy_SysEnableCM4(uint32_t vectorTableOffset);
extern void Cy_SysDisableCM4(void);
extern void Cy_SysRetainCM4(void);
extern void Cy_SysResetCM4(void);
extern void Default_Handler (void);
void Cy_SysIpcPipeIsrCm0(void);
void Cy_SysIpcPipeIsrCm4(void);
extern void Cy_SystemInit(void);
extern void Cy_SystemInitFpuEnable(void);
extern uint32_t cy_delayFreqKhz;
extern uint8_t cy_delayFreqMhz;
extern uint32_t cy_BleEcoClockFreqHz;
extern uint32_t cy_Hfclk0FreqHz;
extern uint32_t cy_PeriClkFreqHz;
extern uint32_t SystemCoreClock;
extern uint32_t cy_AhbFreqHz;
typedef enum
{
    PCLK_SCB0_CLOCK = 0x0000u,
    PCLK_SCB1_CLOCK = 0x0001u,
    PCLK_SCB2_CLOCK = 0x0002u,
    PCLK_SCB3_CLOCK = 0x0003u,
    PCLK_SCB4_CLOCK = 0x0004u,
    PCLK_SCB5_CLOCK = 0x0005u,
    PCLK_SCB6_CLOCK = 0x0006u,
    PCLK_SCB7_CLOCK = 0x0007u,
    PCLK_SCB8_CLOCK = 0x0008u,
    PCLK_UDB_CLOCKS0 = 0x0009u,
    PCLK_UDB_CLOCKS1 = 0x000Au,
    PCLK_UDB_CLOCKS2 = 0x000Bu,
    PCLK_UDB_CLOCKS3 = 0x000Cu,
    PCLK_UDB_CLOCKS4 = 0x000Du,
    PCLK_UDB_CLOCKS5 = 0x000Eu,
    PCLK_UDB_CLOCKS6 = 0x000Fu,
    PCLK_UDB_CLOCKS7 = 0x0010u,
    PCLK_SMARTIO8_CLOCK = 0x0011u,
    PCLK_SMARTIO9_CLOCK = 0x0012u,
    PCLK_TCPWM0_CLOCKS0 = 0x0013u,
    PCLK_TCPWM0_CLOCKS1 = 0x0014u,
    PCLK_TCPWM0_CLOCKS2 = 0x0015u,
    PCLK_TCPWM0_CLOCKS3 = 0x0016u,
    PCLK_TCPWM0_CLOCKS4 = 0x0017u,
    PCLK_TCPWM0_CLOCKS5 = 0x0018u,
    PCLK_TCPWM0_CLOCKS6 = 0x0019u,
    PCLK_TCPWM0_CLOCKS7 = 0x001Au,
    PCLK_TCPWM1_CLOCKS0 = 0x001Bu,
    PCLK_TCPWM1_CLOCKS1 = 0x001Cu,
    PCLK_TCPWM1_CLOCKS2 = 0x001Du,
    PCLK_TCPWM1_CLOCKS3 = 0x001Eu,
    PCLK_TCPWM1_CLOCKS4 = 0x001Fu,
    PCLK_TCPWM1_CLOCKS5 = 0x0020u,
    PCLK_TCPWM1_CLOCKS6 = 0x0021u,
    PCLK_TCPWM1_CLOCKS7 = 0x0022u,
    PCLK_TCPWM1_CLOCKS8 = 0x0023u,
    PCLK_TCPWM1_CLOCKS9 = 0x0024u,
    PCLK_TCPWM1_CLOCKS10 = 0x0025u,
    PCLK_TCPWM1_CLOCKS11 = 0x0026u,
    PCLK_TCPWM1_CLOCKS12 = 0x0027u,
    PCLK_TCPWM1_CLOCKS13 = 0x0028u,
    PCLK_TCPWM1_CLOCKS14 = 0x0029u,
    PCLK_TCPWM1_CLOCKS15 = 0x002Au,
    PCLK_TCPWM1_CLOCKS16 = 0x002Bu,
    PCLK_TCPWM1_CLOCKS17 = 0x002Cu,
    PCLK_TCPWM1_CLOCKS18 = 0x002Du,
    PCLK_TCPWM1_CLOCKS19 = 0x002Eu,
    PCLK_TCPWM1_CLOCKS20 = 0x002Fu,
    PCLK_TCPWM1_CLOCKS21 = 0x0030u,
    PCLK_TCPWM1_CLOCKS22 = 0x0031u,
    PCLK_TCPWM1_CLOCKS23 = 0x0032u,
    PCLK_CSD_CLOCK = 0x0033u,
    PCLK_LCD_CLOCK = 0x0034u,
    PCLK_PROFILE_CLOCK_PROFILE = 0x0035u,
    PCLK_CPUSS_CLOCK_TRACE_IN = 0x0036u,
    PCLK_PASS_CLOCK_CTDAC = 0x0037u,
    PCLK_PASS_CLOCK_PUMP_PERI = 0x0038u,
    PCLK_PASS_CLOCK_SAR = 0x0039u,
    PCLK_USB_CLOCK_DEV_BRS = 0x003Au
} en_clk_dst_t;
typedef enum
{
    TRIG0_IN_CPUSS_ZERO = 0x00000000u,
    TRIG0_IN_TR_GROUP10_OUTPUT0 = 0x00000001u,
    TRIG0_IN_TR_GROUP10_OUTPUT1 = 0x00000002u,
    TRIG0_IN_TR_GROUP10_OUTPUT2 = 0x00000003u,
    TRIG0_IN_TR_GROUP10_OUTPUT3 = 0x00000004u,
    TRIG0_IN_TR_GROUP10_OUTPUT4 = 0x00000005u,
    TRIG0_IN_TR_GROUP10_OUTPUT5 = 0x00000006u,
    TRIG0_IN_TR_GROUP10_OUTPUT6 = 0x00000007u,
    TRIG0_IN_TR_GROUP10_OUTPUT7 = 0x00000008u,
    TRIG0_IN_TR_GROUP11_OUTPUT0 = 0x00000009u,
    TRIG0_IN_TR_GROUP11_OUTPUT1 = 0x0000000Au,
    TRIG0_IN_TR_GROUP11_OUTPUT2 = 0x0000000Bu,
    TRIG0_IN_TR_GROUP11_OUTPUT3 = 0x0000000Cu,
    TRIG0_IN_TR_GROUP11_OUTPUT4 = 0x0000000Du,
    TRIG0_IN_TR_GROUP11_OUTPUT5 = 0x0000000Eu,
    TRIG0_IN_TR_GROUP11_OUTPUT6 = 0x0000000Fu,
    TRIG0_IN_TR_GROUP11_OUTPUT7 = 0x00000010u,
    TRIG0_IN_TR_GROUP11_OUTPUT8 = 0x00000011u,
    TRIG0_IN_TR_GROUP11_OUTPUT9 = 0x00000012u,
    TRIG0_IN_TR_GROUP11_OUTPUT10 = 0x00000013u,
    TRIG0_IN_TR_GROUP11_OUTPUT11 = 0x00000014u,
    TRIG0_IN_TR_GROUP11_OUTPUT12 = 0x00000015u,
    TRIG0_IN_TR_GROUP11_OUTPUT13 = 0x00000016u,
    TRIG0_IN_TR_GROUP11_OUTPUT14 = 0x00000017u,
    TRIG0_IN_TR_GROUP11_OUTPUT15 = 0x00000018u,
    TRIG0_IN_TR_GROUP12_OUTPUT8 = 0x00000019u,
    TRIG0_IN_TR_GROUP12_OUTPUT9 = 0x0000001Au,
    TRIG0_IN_TR_GROUP13_OUTPUT0 = 0x0000001Bu,
    TRIG0_IN_TR_GROUP13_OUTPUT1 = 0x0000001Cu,
    TRIG0_IN_TR_GROUP13_OUTPUT2 = 0x0000001Du,
    TRIG0_IN_TR_GROUP13_OUTPUT3 = 0x0000001Eu,
    TRIG0_IN_TR_GROUP13_OUTPUT4 = 0x0000001Fu,
    TRIG0_IN_TR_GROUP13_OUTPUT5 = 0x00000020u,
    TRIG0_IN_TR_GROUP13_OUTPUT6 = 0x00000021u,
    TRIG0_IN_TR_GROUP13_OUTPUT7 = 0x00000022u,
    TRIG0_IN_TR_GROUP13_OUTPUT8 = 0x00000023u,
    TRIG0_IN_TR_GROUP13_OUTPUT9 = 0x00000024u,
    TRIG0_IN_TR_GROUP13_OUTPUT10 = 0x00000025u,
    TRIG0_IN_TR_GROUP13_OUTPUT11 = 0x00000026u,
    TRIG0_IN_TR_GROUP13_OUTPUT12 = 0x00000027u,
    TRIG0_IN_TR_GROUP13_OUTPUT13 = 0x00000028u,
    TRIG0_IN_TR_GROUP13_OUTPUT14 = 0x00000029u,
    TRIG0_IN_TR_GROUP13_OUTPUT15 = 0x0000002Au,
    TRIG0_IN_TR_GROUP14_OUTPUT0 = 0x0000002Bu,
    TRIG0_IN_TR_GROUP14_OUTPUT1 = 0x0000002Cu,
    TRIG0_IN_TR_GROUP14_OUTPUT2 = 0x0000002Du,
    TRIG0_IN_TR_GROUP14_OUTPUT3 = 0x0000002Eu,
    TRIG0_IN_TR_GROUP14_OUTPUT4 = 0x0000002Fu,
    TRIG0_IN_TR_GROUP14_OUTPUT5 = 0x00000030u,
    TRIG0_IN_TR_GROUP14_OUTPUT6 = 0x00000031u,
    TRIG0_IN_TR_GROUP14_OUTPUT7 = 0x00000032u
} en_trig_input_grp0_t;
typedef enum
{
    TRIG1_IN_CPUSS_ZERO = 0x00000100u,
    TRIG1_IN_TR_GROUP10_OUTPUT0 = 0x00000101u,
    TRIG1_IN_TR_GROUP10_OUTPUT1 = 0x00000102u,
    TRIG1_IN_TR_GROUP10_OUTPUT2 = 0x00000103u,
    TRIG1_IN_TR_GROUP10_OUTPUT3 = 0x00000104u,
    TRIG1_IN_TR_GROUP10_OUTPUT4 = 0x00000105u,
    TRIG1_IN_TR_GROUP10_OUTPUT5 = 0x00000106u,
    TRIG1_IN_TR_GROUP10_OUTPUT6 = 0x00000107u,
    TRIG1_IN_TR_GROUP10_OUTPUT7 = 0x00000108u,
    TRIG1_IN_TR_GROUP11_OUTPUT0 = 0x00000109u,
    TRIG1_IN_TR_GROUP11_OUTPUT1 = 0x0000010Au,
    TRIG1_IN_TR_GROUP11_OUTPUT2 = 0x0000010Bu,
    TRIG1_IN_TR_GROUP11_OUTPUT3 = 0x0000010Cu,
    TRIG1_IN_TR_GROUP11_OUTPUT4 = 0x0000010Du,
    TRIG1_IN_TR_GROUP11_OUTPUT5 = 0x0000010Eu,
    TRIG1_IN_TR_GROUP11_OUTPUT6 = 0x0000010Fu,
    TRIG1_IN_TR_GROUP11_OUTPUT7 = 0x00000110u,
    TRIG1_IN_TR_GROUP11_OUTPUT8 = 0x00000111u,
    TRIG1_IN_TR_GROUP11_OUTPUT9 = 0x00000112u,
    TRIG1_IN_TR_GROUP11_OUTPUT10 = 0x00000113u,
    TRIG1_IN_TR_GROUP11_OUTPUT11 = 0x00000114u,
    TRIG1_IN_TR_GROUP11_OUTPUT12 = 0x00000115u,
    TRIG1_IN_TR_GROUP11_OUTPUT13 = 0x00000116u,
    TRIG1_IN_TR_GROUP11_OUTPUT14 = 0x00000117u,
    TRIG1_IN_TR_GROUP11_OUTPUT15 = 0x00000118u,
    TRIG1_IN_TR_GROUP12_OUTPUT8 = 0x00000119u,
    TRIG1_IN_TR_GROUP12_OUTPUT9 = 0x0000011Au,
    TRIG1_IN_TR_GROUP13_OUTPUT0 = 0x0000011Bu,
    TRIG1_IN_TR_GROUP13_OUTPUT1 = 0x0000011Cu,
    TRIG1_IN_TR_GROUP13_OUTPUT2 = 0x0000011Du,
    TRIG1_IN_TR_GROUP13_OUTPUT3 = 0x0000011Eu,
    TRIG1_IN_TR_GROUP13_OUTPUT4 = 0x0000011Fu,
    TRIG1_IN_TR_GROUP13_OUTPUT5 = 0x00000120u,
    TRIG1_IN_TR_GROUP13_OUTPUT6 = 0x00000121u,
    TRIG1_IN_TR_GROUP13_OUTPUT7 = 0x00000122u,
    TRIG1_IN_TR_GROUP13_OUTPUT8 = 0x00000123u,
    TRIG1_IN_TR_GROUP13_OUTPUT9 = 0x00000124u,
    TRIG1_IN_TR_GROUP13_OUTPUT10 = 0x00000125u,
    TRIG1_IN_TR_GROUP13_OUTPUT11 = 0x00000126u,
    TRIG1_IN_TR_GROUP13_OUTPUT12 = 0x00000127u,
    TRIG1_IN_TR_GROUP13_OUTPUT13 = 0x00000128u,
    TRIG1_IN_TR_GROUP13_OUTPUT14 = 0x00000129u,
    TRIG1_IN_TR_GROUP13_OUTPUT15 = 0x0000012Au,
    TRIG1_IN_TR_GROUP14_OUTPUT0 = 0x0000012Bu,
    TRIG1_IN_TR_GROUP14_OUTPUT1 = 0x0000012Cu,
    TRIG1_IN_TR_GROUP14_OUTPUT2 = 0x0000012Du,
    TRIG1_IN_TR_GROUP14_OUTPUT3 = 0x0000012Eu,
    TRIG1_IN_TR_GROUP14_OUTPUT4 = 0x0000012Fu,
    TRIG1_IN_TR_GROUP14_OUTPUT5 = 0x00000130u,
    TRIG1_IN_TR_GROUP14_OUTPUT6 = 0x00000131u,
    TRIG1_IN_TR_GROUP14_OUTPUT7 = 0x00000132u
} en_trig_input_grp1_t;
typedef enum
{
    TRIG2_IN_CPUSS_ZERO = 0x00000200u,
    TRIG2_IN_TR_GROUP10_OUTPUT0 = 0x00000201u,
    TRIG2_IN_TR_GROUP10_OUTPUT1 = 0x00000202u,
    TRIG2_IN_TR_GROUP10_OUTPUT2 = 0x00000203u,
    TRIG2_IN_TR_GROUP10_OUTPUT3 = 0x00000204u,
    TRIG2_IN_TR_GROUP10_OUTPUT4 = 0x00000205u,
    TRIG2_IN_TR_GROUP10_OUTPUT5 = 0x00000206u,
    TRIG2_IN_TR_GROUP10_OUTPUT6 = 0x00000207u,
    TRIG2_IN_TR_GROUP10_OUTPUT7 = 0x00000208u,
    TRIG2_IN_TR_GROUP11_OUTPUT0 = 0x00000209u,
    TRIG2_IN_TR_GROUP11_OUTPUT1 = 0x0000020Au,
    TRIG2_IN_TR_GROUP11_OUTPUT2 = 0x0000020Bu,
    TRIG2_IN_TR_GROUP11_OUTPUT3 = 0x0000020Cu,
    TRIG2_IN_TR_GROUP11_OUTPUT4 = 0x0000020Du,
    TRIG2_IN_TR_GROUP11_OUTPUT5 = 0x0000020Eu,
    TRIG2_IN_TR_GROUP11_OUTPUT6 = 0x0000020Fu,
    TRIG2_IN_TR_GROUP11_OUTPUT7 = 0x00000210u,
    TRIG2_IN_TR_GROUP11_OUTPUT8 = 0x00000211u,
    TRIG2_IN_TR_GROUP11_OUTPUT9 = 0x00000212u,
    TRIG2_IN_TR_GROUP11_OUTPUT10 = 0x00000213u,
    TRIG2_IN_TR_GROUP11_OUTPUT11 = 0x00000214u,
    TRIG2_IN_TR_GROUP11_OUTPUT12 = 0x00000215u,
    TRIG2_IN_TR_GROUP11_OUTPUT13 = 0x00000216u,
    TRIG2_IN_TR_GROUP11_OUTPUT14 = 0x00000217u,
    TRIG2_IN_TR_GROUP11_OUTPUT15 = 0x00000218u,
    TRIG2_IN_TR_GROUP12_OUTPUT0 = 0x00000219u,
    TRIG2_IN_TR_GROUP12_OUTPUT1 = 0x0000021Au,
    TRIG2_IN_TR_GROUP12_OUTPUT2 = 0x0000021Bu,
    TRIG2_IN_TR_GROUP12_OUTPUT3 = 0x0000021Cu,
    TRIG2_IN_TR_GROUP12_OUTPUT4 = 0x0000021Du,
    TRIG2_IN_TR_GROUP12_OUTPUT5 = 0x0000021Eu,
    TRIG2_IN_TR_GROUP12_OUTPUT6 = 0x0000021Fu,
    TRIG2_IN_TR_GROUP12_OUTPUT7 = 0x00000220u,
    TRIG2_IN_TR_GROUP13_OUTPUT16 = 0x00000221u,
    TRIG2_IN_TR_GROUP13_OUTPUT17 = 0x00000222u,
    TRIG2_IN_TR_GROUP14_OUTPUT8 = 0x00000223u,
    TRIG2_IN_TR_GROUP14_OUTPUT9 = 0x00000224u,
    TRIG2_IN_TR_GROUP14_OUTPUT10 = 0x00000225u,
    TRIG2_IN_TR_GROUP14_OUTPUT11 = 0x00000226u,
    TRIG2_IN_TR_GROUP14_OUTPUT12 = 0x00000227u,
    TRIG2_IN_TR_GROUP14_OUTPUT13 = 0x00000228u,
    TRIG2_IN_TR_GROUP14_OUTPUT14 = 0x00000229u,
    TRIG2_IN_TR_GROUP14_OUTPUT15 = 0x0000022Au
} en_trig_input_grp2_t;
typedef enum
{
    TRIG3_IN_CPUSS_ZERO = 0x00000300u,
    TRIG3_IN_TR_GROUP10_OUTPUT0 = 0x00000301u,
    TRIG3_IN_TR_GROUP10_OUTPUT1 = 0x00000302u,
    TRIG3_IN_TR_GROUP10_OUTPUT2 = 0x00000303u,
    TRIG3_IN_TR_GROUP10_OUTPUT3 = 0x00000304u,
    TRIG3_IN_TR_GROUP10_OUTPUT4 = 0x00000305u,
    TRIG3_IN_TR_GROUP10_OUTPUT5 = 0x00000306u,
    TRIG3_IN_TR_GROUP10_OUTPUT6 = 0x00000307u,
    TRIG3_IN_TR_GROUP10_OUTPUT7 = 0x00000308u,
    TRIG3_IN_TR_GROUP11_OUTPUT0 = 0x00000309u,
    TRIG3_IN_TR_GROUP11_OUTPUT1 = 0x0000030Au,
    TRIG3_IN_TR_GROUP11_OUTPUT2 = 0x0000030Bu,
    TRIG3_IN_TR_GROUP11_OUTPUT3 = 0x0000030Cu,
    TRIG3_IN_TR_GROUP11_OUTPUT4 = 0x0000030Du,
    TRIG3_IN_TR_GROUP11_OUTPUT5 = 0x0000030Eu,
    TRIG3_IN_TR_GROUP11_OUTPUT6 = 0x0000030Fu,
    TRIG3_IN_TR_GROUP11_OUTPUT7 = 0x00000310u,
    TRIG3_IN_TR_GROUP11_OUTPUT8 = 0x00000311u,
    TRIG3_IN_TR_GROUP11_OUTPUT9 = 0x00000312u,
    TRIG3_IN_TR_GROUP11_OUTPUT10 = 0x00000313u,
    TRIG3_IN_TR_GROUP11_OUTPUT11 = 0x00000314u,
    TRIG3_IN_TR_GROUP11_OUTPUT12 = 0x00000315u,
    TRIG3_IN_TR_GROUP11_OUTPUT13 = 0x00000316u,
    TRIG3_IN_TR_GROUP11_OUTPUT14 = 0x00000317u,
    TRIG3_IN_TR_GROUP11_OUTPUT15 = 0x00000318u,
    TRIG3_IN_TR_GROUP12_OUTPUT0 = 0x00000319u,
    TRIG3_IN_TR_GROUP12_OUTPUT1 = 0x0000031Au,
    TRIG3_IN_TR_GROUP12_OUTPUT2 = 0x0000031Bu,
    TRIG3_IN_TR_GROUP12_OUTPUT3 = 0x0000031Cu,
    TRIG3_IN_TR_GROUP12_OUTPUT4 = 0x0000031Du,
    TRIG3_IN_TR_GROUP12_OUTPUT5 = 0x0000031Eu,
    TRIG3_IN_TR_GROUP12_OUTPUT6 = 0x0000031Fu,
    TRIG3_IN_TR_GROUP12_OUTPUT7 = 0x00000320u,
    TRIG3_IN_TR_GROUP13_OUTPUT16 = 0x00000321u,
    TRIG3_IN_TR_GROUP13_OUTPUT17 = 0x00000322u,
    TRIG3_IN_TR_GROUP14_OUTPUT8 = 0x00000323u,
    TRIG3_IN_TR_GROUP14_OUTPUT9 = 0x00000324u,
    TRIG3_IN_TR_GROUP14_OUTPUT10 = 0x00000325u,
    TRIG3_IN_TR_GROUP14_OUTPUT11 = 0x00000326u,
    TRIG3_IN_TR_GROUP14_OUTPUT12 = 0x00000327u,
    TRIG3_IN_TR_GROUP14_OUTPUT13 = 0x00000328u,
    TRIG3_IN_TR_GROUP14_OUTPUT14 = 0x00000329u,
    TRIG3_IN_TR_GROUP14_OUTPUT15 = 0x0000032Au
} en_trig_input_grp3_t;
typedef enum
{
    TRIG4_IN_CPUSS_ZERO = 0x00000400u,
    TRIG4_IN_TR_GROUP10_OUTPUT0 = 0x00000401u,
    TRIG4_IN_TR_GROUP10_OUTPUT1 = 0x00000402u,
    TRIG4_IN_TR_GROUP10_OUTPUT2 = 0x00000403u,
    TRIG4_IN_TR_GROUP10_OUTPUT3 = 0x00000404u,
    TRIG4_IN_TR_GROUP10_OUTPUT4 = 0x00000405u,
    TRIG4_IN_TR_GROUP10_OUTPUT5 = 0x00000406u,
    TRIG4_IN_TR_GROUP10_OUTPUT6 = 0x00000407u,
    TRIG4_IN_TR_GROUP10_OUTPUT7 = 0x00000408u,
    TRIG4_IN_TR_GROUP11_OUTPUT0 = 0x00000409u,
    TRIG4_IN_TR_GROUP11_OUTPUT1 = 0x0000040Au,
    TRIG4_IN_TR_GROUP11_OUTPUT2 = 0x0000040Bu,
    TRIG4_IN_TR_GROUP11_OUTPUT3 = 0x0000040Cu,
    TRIG4_IN_TR_GROUP11_OUTPUT4 = 0x0000040Du,
    TRIG4_IN_TR_GROUP11_OUTPUT5 = 0x0000040Eu,
    TRIG4_IN_TR_GROUP11_OUTPUT6 = 0x0000040Fu,
    TRIG4_IN_TR_GROUP11_OUTPUT7 = 0x00000410u,
    TRIG4_IN_TR_GROUP11_OUTPUT8 = 0x00000411u,
    TRIG4_IN_TR_GROUP11_OUTPUT9 = 0x00000412u,
    TRIG4_IN_TR_GROUP11_OUTPUT10 = 0x00000413u,
    TRIG4_IN_TR_GROUP11_OUTPUT11 = 0x00000414u,
    TRIG4_IN_TR_GROUP11_OUTPUT12 = 0x00000415u,
    TRIG4_IN_TR_GROUP11_OUTPUT13 = 0x00000416u,
    TRIG4_IN_TR_GROUP11_OUTPUT14 = 0x00000417u,
    TRIG4_IN_TR_GROUP11_OUTPUT15 = 0x00000418u,
    TRIG4_IN_TR_GROUP12_OUTPUT0 = 0x00000419u,
    TRIG4_IN_TR_GROUP12_OUTPUT1 = 0x0000041Au,
    TRIG4_IN_TR_GROUP12_OUTPUT2 = 0x0000041Bu,
    TRIG4_IN_TR_GROUP12_OUTPUT3 = 0x0000041Cu,
    TRIG4_IN_TR_GROUP12_OUTPUT4 = 0x0000041Du,
    TRIG4_IN_TR_GROUP12_OUTPUT5 = 0x0000041Eu,
    TRIG4_IN_TR_GROUP12_OUTPUT6 = 0x0000041Fu,
    TRIG4_IN_TR_GROUP12_OUTPUT7 = 0x00000420u,
    TRIG4_IN_TR_GROUP13_OUTPUT16 = 0x00000421u,
    TRIG4_IN_TR_GROUP13_OUTPUT17 = 0x00000422u,
    TRIG4_IN_TR_GROUP14_OUTPUT8 = 0x00000423u,
    TRIG4_IN_TR_GROUP14_OUTPUT9 = 0x00000424u,
    TRIG4_IN_TR_GROUP14_OUTPUT10 = 0x00000425u,
    TRIG4_IN_TR_GROUP14_OUTPUT11 = 0x00000426u,
    TRIG4_IN_TR_GROUP14_OUTPUT12 = 0x00000427u,
    TRIG4_IN_TR_GROUP14_OUTPUT13 = 0x00000428u,
    TRIG4_IN_TR_GROUP14_OUTPUT14 = 0x00000429u,
    TRIG4_IN_TR_GROUP14_OUTPUT15 = 0x0000042Au
} en_trig_input_grp4_t;
typedef enum
{
    TRIG5_IN_CPUSS_ZERO = 0x00000500u,
    TRIG5_IN_TR_GROUP10_OUTPUT0 = 0x00000501u,
    TRIG5_IN_TR_GROUP10_OUTPUT1 = 0x00000502u,
    TRIG5_IN_TR_GROUP10_OUTPUT2 = 0x00000503u,
    TRIG5_IN_TR_GROUP10_OUTPUT3 = 0x00000504u,
    TRIG5_IN_TR_GROUP10_OUTPUT4 = 0x00000505u,
    TRIG5_IN_TR_GROUP10_OUTPUT5 = 0x00000506u,
    TRIG5_IN_TR_GROUP10_OUTPUT6 = 0x00000507u,
    TRIG5_IN_TR_GROUP10_OUTPUT7 = 0x00000508u,
    TRIG5_IN_TR_GROUP11_OUTPUT0 = 0x00000509u,
    TRIG5_IN_TR_GROUP11_OUTPUT1 = 0x0000050Au,
    TRIG5_IN_TR_GROUP11_OUTPUT2 = 0x0000050Bu,
    TRIG5_IN_TR_GROUP11_OUTPUT3 = 0x0000050Cu,
    TRIG5_IN_TR_GROUP11_OUTPUT4 = 0x0000050Du,
    TRIG5_IN_TR_GROUP11_OUTPUT5 = 0x0000050Eu,
    TRIG5_IN_TR_GROUP11_OUTPUT6 = 0x0000050Fu,
    TRIG5_IN_TR_GROUP11_OUTPUT7 = 0x00000510u,
    TRIG5_IN_TR_GROUP11_OUTPUT8 = 0x00000511u,
    TRIG5_IN_TR_GROUP11_OUTPUT9 = 0x00000512u,
    TRIG5_IN_TR_GROUP11_OUTPUT10 = 0x00000513u,
    TRIG5_IN_TR_GROUP11_OUTPUT11 = 0x00000514u,
    TRIG5_IN_TR_GROUP11_OUTPUT12 = 0x00000515u,
    TRIG5_IN_TR_GROUP11_OUTPUT13 = 0x00000516u,
    TRIG5_IN_TR_GROUP11_OUTPUT14 = 0x00000517u,
    TRIG5_IN_TR_GROUP11_OUTPUT15 = 0x00000518u,
    TRIG5_IN_TR_GROUP12_OUTPUT0 = 0x00000519u,
    TRIG5_IN_TR_GROUP12_OUTPUT1 = 0x0000051Au,
    TRIG5_IN_TR_GROUP12_OUTPUT2 = 0x0000051Bu,
    TRIG5_IN_TR_GROUP12_OUTPUT3 = 0x0000051Cu,
    TRIG5_IN_TR_GROUP12_OUTPUT4 = 0x0000051Du,
    TRIG5_IN_TR_GROUP12_OUTPUT5 = 0x0000051Eu,
    TRIG5_IN_TR_GROUP12_OUTPUT6 = 0x0000051Fu,
    TRIG5_IN_TR_GROUP12_OUTPUT7 = 0x00000520u,
    TRIG5_IN_TR_GROUP13_OUTPUT16 = 0x00000521u,
    TRIG5_IN_TR_GROUP13_OUTPUT17 = 0x00000522u,
    TRIG5_IN_TR_GROUP14_OUTPUT8 = 0x00000523u,
    TRIG5_IN_TR_GROUP14_OUTPUT9 = 0x00000524u,
    TRIG5_IN_TR_GROUP14_OUTPUT10 = 0x00000525u,
    TRIG5_IN_TR_GROUP14_OUTPUT11 = 0x00000526u,
    TRIG5_IN_TR_GROUP14_OUTPUT12 = 0x00000527u,
    TRIG5_IN_TR_GROUP14_OUTPUT13 = 0x00000528u,
    TRIG5_IN_TR_GROUP14_OUTPUT14 = 0x00000529u,
    TRIG5_IN_TR_GROUP14_OUTPUT15 = 0x0000052Au
} en_trig_input_grp5_t;
typedef enum
{
    TRIG6_IN_CPUSS_ZERO = 0x00000600u,
    TRIG6_IN_TR_GROUP10_OUTPUT0 = 0x00000601u,
    TRIG6_IN_TR_GROUP10_OUTPUT1 = 0x00000602u,
    TRIG6_IN_TR_GROUP10_OUTPUT2 = 0x00000603u,
    TRIG6_IN_TR_GROUP10_OUTPUT3 = 0x00000604u,
    TRIG6_IN_TR_GROUP10_OUTPUT4 = 0x00000605u,
    TRIG6_IN_TR_GROUP10_OUTPUT5 = 0x00000606u,
    TRIG6_IN_TR_GROUP10_OUTPUT6 = 0x00000607u,
    TRIG6_IN_TR_GROUP10_OUTPUT7 = 0x00000608u,
    TRIG6_IN_TR_GROUP11_OUTPUT0 = 0x00000609u,
    TRIG6_IN_TR_GROUP11_OUTPUT1 = 0x0000060Au,
    TRIG6_IN_TR_GROUP11_OUTPUT2 = 0x0000060Bu,
    TRIG6_IN_TR_GROUP11_OUTPUT3 = 0x0000060Cu,
    TRIG6_IN_TR_GROUP11_OUTPUT4 = 0x0000060Du,
    TRIG6_IN_TR_GROUP11_OUTPUT5 = 0x0000060Eu,
    TRIG6_IN_TR_GROUP11_OUTPUT6 = 0x0000060Fu,
    TRIG6_IN_TR_GROUP11_OUTPUT7 = 0x00000610u,
    TRIG6_IN_TR_GROUP11_OUTPUT8 = 0x00000611u,
    TRIG6_IN_TR_GROUP11_OUTPUT9 = 0x00000612u,
    TRIG6_IN_TR_GROUP11_OUTPUT10 = 0x00000613u,
    TRIG6_IN_TR_GROUP11_OUTPUT11 = 0x00000614u,
    TRIG6_IN_TR_GROUP11_OUTPUT12 = 0x00000615u,
    TRIG6_IN_TR_GROUP11_OUTPUT13 = 0x00000616u,
    TRIG6_IN_TR_GROUP11_OUTPUT14 = 0x00000617u,
    TRIG6_IN_TR_GROUP11_OUTPUT15 = 0x00000618u,
    TRIG6_IN_TR_GROUP12_OUTPUT0 = 0x00000619u,
    TRIG6_IN_TR_GROUP12_OUTPUT1 = 0x0000061Au,
    TRIG6_IN_TR_GROUP12_OUTPUT2 = 0x0000061Bu,
    TRIG6_IN_TR_GROUP12_OUTPUT3 = 0x0000061Cu,
    TRIG6_IN_TR_GROUP12_OUTPUT4 = 0x0000061Du,
    TRIG6_IN_TR_GROUP12_OUTPUT5 = 0x0000061Eu,
    TRIG6_IN_TR_GROUP12_OUTPUT6 = 0x0000061Fu,
    TRIG6_IN_TR_GROUP12_OUTPUT7 = 0x00000620u,
    TRIG6_IN_TR_GROUP13_OUTPUT16 = 0x00000621u,
    TRIG6_IN_TR_GROUP13_OUTPUT17 = 0x00000622u,
    TRIG6_IN_TR_GROUP14_OUTPUT8 = 0x00000623u,
    TRIG6_IN_TR_GROUP14_OUTPUT9 = 0x00000624u,
    TRIG6_IN_TR_GROUP14_OUTPUT10 = 0x00000625u,
    TRIG6_IN_TR_GROUP14_OUTPUT11 = 0x00000626u,
    TRIG6_IN_TR_GROUP14_OUTPUT12 = 0x00000627u,
    TRIG6_IN_TR_GROUP14_OUTPUT13 = 0x00000628u,
    TRIG6_IN_TR_GROUP14_OUTPUT14 = 0x00000629u,
    TRIG6_IN_TR_GROUP14_OUTPUT15 = 0x0000062Au
} en_trig_input_grp6_t;
typedef enum
{
    TRIG7_IN_CPUSS_ZERO = 0x00000700u,
    TRIG7_IN_TR_GROUP10_OUTPUT0 = 0x00000701u,
    TRIG7_IN_TR_GROUP10_OUTPUT1 = 0x00000702u,
    TRIG7_IN_TR_GROUP10_OUTPUT2 = 0x00000703u,
    TRIG7_IN_TR_GROUP10_OUTPUT3 = 0x00000704u,
    TRIG7_IN_TR_GROUP10_OUTPUT4 = 0x00000705u,
    TRIG7_IN_TR_GROUP10_OUTPUT5 = 0x00000706u,
    TRIG7_IN_TR_GROUP10_OUTPUT6 = 0x00000707u,
    TRIG7_IN_TR_GROUP10_OUTPUT7 = 0x00000708u,
    TRIG7_IN_TR_GROUP11_OUTPUT0 = 0x00000709u,
    TRIG7_IN_TR_GROUP11_OUTPUT1 = 0x0000070Au,
    TRIG7_IN_TR_GROUP11_OUTPUT2 = 0x0000070Bu,
    TRIG7_IN_TR_GROUP11_OUTPUT3 = 0x0000070Cu,
    TRIG7_IN_TR_GROUP11_OUTPUT4 = 0x0000070Du,
    TRIG7_IN_TR_GROUP11_OUTPUT5 = 0x0000070Eu,
    TRIG7_IN_TR_GROUP11_OUTPUT6 = 0x0000070Fu,
    TRIG7_IN_TR_GROUP11_OUTPUT7 = 0x00000710u,
    TRIG7_IN_TR_GROUP11_OUTPUT8 = 0x00000711u,
    TRIG7_IN_TR_GROUP11_OUTPUT9 = 0x00000712u,
    TRIG7_IN_TR_GROUP11_OUTPUT10 = 0x00000713u,
    TRIG7_IN_TR_GROUP11_OUTPUT11 = 0x00000714u,
    TRIG7_IN_TR_GROUP11_OUTPUT12 = 0x00000715u,
    TRIG7_IN_TR_GROUP11_OUTPUT13 = 0x00000716u,
    TRIG7_IN_TR_GROUP11_OUTPUT14 = 0x00000717u,
    TRIG7_IN_TR_GROUP11_OUTPUT15 = 0x00000718u,
    TRIG7_IN_TR_GROUP12_OUTPUT0 = 0x00000719u,
    TRIG7_IN_TR_GROUP12_OUTPUT1 = 0x0000071Au,
    TRIG7_IN_TR_GROUP12_OUTPUT2 = 0x0000071Bu,
    TRIG7_IN_TR_GROUP12_OUTPUT3 = 0x0000071Cu,
    TRIG7_IN_TR_GROUP12_OUTPUT4 = 0x0000071Du,
    TRIG7_IN_TR_GROUP12_OUTPUT5 = 0x0000071Eu,
    TRIG7_IN_TR_GROUP12_OUTPUT6 = 0x0000071Fu,
    TRIG7_IN_TR_GROUP12_OUTPUT7 = 0x00000720u,
    TRIG7_IN_TR_GROUP13_OUTPUT16 = 0x00000721u,
    TRIG7_IN_TR_GROUP13_OUTPUT17 = 0x00000722u,
    TRIG7_IN_TR_GROUP14_OUTPUT8 = 0x00000723u,
    TRIG7_IN_TR_GROUP14_OUTPUT9 = 0x00000724u,
    TRIG7_IN_TR_GROUP14_OUTPUT10 = 0x00000725u,
    TRIG7_IN_TR_GROUP14_OUTPUT11 = 0x00000726u,
    TRIG7_IN_TR_GROUP14_OUTPUT12 = 0x00000727u,
    TRIG7_IN_TR_GROUP14_OUTPUT13 = 0x00000728u,
    TRIG7_IN_TR_GROUP14_OUTPUT14 = 0x00000729u,
    TRIG7_IN_TR_GROUP14_OUTPUT15 = 0x0000072Au
} en_trig_input_grp7_t;
typedef enum
{
    TRIG8_IN_CPUSS_ZERO = 0x00000800u,
    TRIG8_IN_TR_GROUP10_OUTPUT0 = 0x00000801u,
    TRIG8_IN_TR_GROUP10_OUTPUT1 = 0x00000802u,
    TRIG8_IN_TR_GROUP10_OUTPUT2 = 0x00000803u,
    TRIG8_IN_TR_GROUP10_OUTPUT3 = 0x00000804u,
    TRIG8_IN_TR_GROUP10_OUTPUT4 = 0x00000805u,
    TRIG8_IN_TR_GROUP10_OUTPUT5 = 0x00000806u,
    TRIG8_IN_TR_GROUP10_OUTPUT6 = 0x00000807u,
    TRIG8_IN_TR_GROUP10_OUTPUT7 = 0x00000808u,
    TRIG8_IN_TR_GROUP11_OUTPUT0 = 0x00000809u,
    TRIG8_IN_TR_GROUP11_OUTPUT1 = 0x0000080Au,
    TRIG8_IN_TR_GROUP11_OUTPUT2 = 0x0000080Bu,
    TRIG8_IN_TR_GROUP11_OUTPUT3 = 0x0000080Cu,
    TRIG8_IN_TR_GROUP11_OUTPUT4 = 0x0000080Du,
    TRIG8_IN_TR_GROUP11_OUTPUT5 = 0x0000080Eu,
    TRIG8_IN_TR_GROUP11_OUTPUT6 = 0x0000080Fu,
    TRIG8_IN_TR_GROUP11_OUTPUT7 = 0x00000810u,
    TRIG8_IN_TR_GROUP11_OUTPUT8 = 0x00000811u,
    TRIG8_IN_TR_GROUP11_OUTPUT9 = 0x00000812u,
    TRIG8_IN_TR_GROUP11_OUTPUT10 = 0x00000813u,
    TRIG8_IN_TR_GROUP11_OUTPUT11 = 0x00000814u,
    TRIG8_IN_TR_GROUP11_OUTPUT12 = 0x00000815u,
    TRIG8_IN_TR_GROUP11_OUTPUT13 = 0x00000816u,
    TRIG8_IN_TR_GROUP11_OUTPUT14 = 0x00000817u,
    TRIG8_IN_TR_GROUP11_OUTPUT15 = 0x00000818u,
    TRIG8_IN_TR_GROUP12_OUTPUT0 = 0x00000819u,
    TRIG8_IN_TR_GROUP12_OUTPUT1 = 0x0000081Au,
    TRIG8_IN_TR_GROUP12_OUTPUT2 = 0x0000081Bu,
    TRIG8_IN_TR_GROUP12_OUTPUT3 = 0x0000081Cu,
    TRIG8_IN_TR_GROUP12_OUTPUT4 = 0x0000081Du,
    TRIG8_IN_TR_GROUP12_OUTPUT5 = 0x0000081Eu,
    TRIG8_IN_TR_GROUP12_OUTPUT6 = 0x0000081Fu,
    TRIG8_IN_TR_GROUP12_OUTPUT7 = 0x00000820u,
    TRIG8_IN_TR_GROUP13_OUTPUT16 = 0x00000821u,
    TRIG8_IN_TR_GROUP13_OUTPUT17 = 0x00000822u,
    TRIG8_IN_TR_GROUP14_OUTPUT8 = 0x00000823u,
    TRIG8_IN_TR_GROUP14_OUTPUT9 = 0x00000824u,
    TRIG8_IN_TR_GROUP14_OUTPUT10 = 0x00000825u,
    TRIG8_IN_TR_GROUP14_OUTPUT11 = 0x00000826u,
    TRIG8_IN_TR_GROUP14_OUTPUT12 = 0x00000827u,
    TRIG8_IN_TR_GROUP14_OUTPUT13 = 0x00000828u,
    TRIG8_IN_TR_GROUP14_OUTPUT14 = 0x00000829u,
    TRIG8_IN_TR_GROUP14_OUTPUT15 = 0x0000082Au
} en_trig_input_grp8_t;
typedef enum
{
    TRIG9_IN_CPUSS_ZERO = 0x00000900u,
    TRIG9_IN_CPUSS_DW0_TR_OUT0 = 0x00000901u,
    TRIG9_IN_CPUSS_DW0_TR_OUT1 = 0x00000902u,
    TRIG9_IN_CPUSS_DW0_TR_OUT2 = 0x00000903u,
    TRIG9_IN_CPUSS_DW0_TR_OUT3 = 0x00000904u,
    TRIG9_IN_CPUSS_DW0_TR_OUT4 = 0x00000905u,
    TRIG9_IN_CPUSS_DW0_TR_OUT5 = 0x00000906u,
    TRIG9_IN_CPUSS_DW0_TR_OUT6 = 0x00000907u,
    TRIG9_IN_CPUSS_DW0_TR_OUT7 = 0x00000908u,
    TRIG9_IN_CPUSS_DW0_TR_OUT8 = 0x00000909u,
    TRIG9_IN_CPUSS_DW0_TR_OUT9 = 0x0000090Au,
    TRIG9_IN_CPUSS_DW0_TR_OUT10 = 0x0000090Bu,
    TRIG9_IN_CPUSS_DW0_TR_OUT11 = 0x0000090Cu,
    TRIG9_IN_CPUSS_DW0_TR_OUT12 = 0x0000090Du,
    TRIG9_IN_CPUSS_DW0_TR_OUT13 = 0x0000090Eu,
    TRIG9_IN_CPUSS_DW0_TR_OUT14 = 0x0000090Fu,
    TRIG9_IN_CPUSS_DW0_TR_OUT15 = 0x00000910u,
    TRIG9_IN_CPUSS_DW1_TR_OUT0 = 0x00000911u,
    TRIG9_IN_CPUSS_DW1_TR_OUT1 = 0x00000912u,
    TRIG9_IN_CPUSS_DW1_TR_OUT2 = 0x00000913u,
    TRIG9_IN_CPUSS_DW1_TR_OUT3 = 0x00000914u,
    TRIG9_IN_CPUSS_DW1_TR_OUT4 = 0x00000915u,
    TRIG9_IN_CPUSS_DW1_TR_OUT5 = 0x00000916u,
    TRIG9_IN_CPUSS_DW1_TR_OUT6 = 0x00000917u,
    TRIG9_IN_CPUSS_DW1_TR_OUT7 = 0x00000918u,
    TRIG9_IN_CPUSS_DW1_TR_OUT8 = 0x00000919u,
    TRIG9_IN_CPUSS_DW1_TR_OUT9 = 0x0000091Au,
    TRIG9_IN_CPUSS_DW1_TR_OUT10 = 0x0000091Bu,
    TRIG9_IN_CPUSS_DW1_TR_OUT11 = 0x0000091Cu,
    TRIG9_IN_CPUSS_DW1_TR_OUT12 = 0x0000091Du,
    TRIG9_IN_CPUSS_DW1_TR_OUT13 = 0x0000091Eu,
    TRIG9_IN_CPUSS_DW1_TR_OUT14 = 0x0000091Fu,
    TRIG9_IN_CPUSS_DW1_TR_OUT15 = 0x00000920u
} en_trig_input_grp9_t;
typedef enum
{
    TRIG10_IN_CPUSS_ZERO = 0x00000A00u,
    TRIG10_IN_CPUSS_DW0_TR_OUT0 = 0x00000A01u,
    TRIG10_IN_CPUSS_DW0_TR_OUT1 = 0x00000A02u,
    TRIG10_IN_CPUSS_DW0_TR_OUT2 = 0x00000A03u,
    TRIG10_IN_CPUSS_DW0_TR_OUT3 = 0x00000A04u,
    TRIG10_IN_CPUSS_DW0_TR_OUT4 = 0x00000A05u,
    TRIG10_IN_CPUSS_DW0_TR_OUT5 = 0x00000A06u,
    TRIG10_IN_CPUSS_DW0_TR_OUT6 = 0x00000A07u,
    TRIG10_IN_CPUSS_DW0_TR_OUT7 = 0x00000A08u,
    TRIG10_IN_CPUSS_DW0_TR_OUT8 = 0x00000A09u,
    TRIG10_IN_CPUSS_DW0_TR_OUT9 = 0x00000A0Au,
    TRIG10_IN_CPUSS_DW0_TR_OUT10 = 0x00000A0Bu,
    TRIG10_IN_CPUSS_DW0_TR_OUT11 = 0x00000A0Cu,
    TRIG10_IN_CPUSS_DW0_TR_OUT12 = 0x00000A0Du,
    TRIG10_IN_CPUSS_DW0_TR_OUT13 = 0x00000A0Eu,
    TRIG10_IN_CPUSS_DW0_TR_OUT14 = 0x00000A0Fu,
    TRIG10_IN_CPUSS_DW0_TR_OUT15 = 0x00000A10u,
    TRIG10_IN_CPUSS_DW1_TR_OUT0 = 0x00000A11u,
    TRIG10_IN_CPUSS_DW1_TR_OUT1 = 0x00000A12u,
    TRIG10_IN_CPUSS_DW1_TR_OUT2 = 0x00000A13u,
    TRIG10_IN_CPUSS_DW1_TR_OUT3 = 0x00000A14u,
    TRIG10_IN_CPUSS_DW1_TR_OUT4 = 0x00000A15u,
    TRIG10_IN_CPUSS_DW1_TR_OUT5 = 0x00000A16u,
    TRIG10_IN_CPUSS_DW1_TR_OUT6 = 0x00000A17u,
    TRIG10_IN_CPUSS_DW1_TR_OUT7 = 0x00000A18u,
    TRIG10_IN_CPUSS_DW1_TR_OUT8 = 0x00000A19u,
    TRIG10_IN_CPUSS_DW1_TR_OUT9 = 0x00000A1Au,
    TRIG10_IN_CPUSS_DW1_TR_OUT10 = 0x00000A1Bu,
    TRIG10_IN_CPUSS_DW1_TR_OUT11 = 0x00000A1Cu,
    TRIG10_IN_CPUSS_DW1_TR_OUT12 = 0x00000A1Du,
    TRIG10_IN_CPUSS_DW1_TR_OUT13 = 0x00000A1Eu,
    TRIG10_IN_CPUSS_DW1_TR_OUT14 = 0x00000A1Fu,
    TRIG10_IN_CPUSS_DW1_TR_OUT15 = 0x00000A20u
} en_trig_input_grp10_t;
typedef enum
{
    TRIG11_IN_CPUSS_ZERO = 0x00000B00u,
    TRIG11_IN_TCPWM0_TR_OVERFLOW0 = 0x00000B01u,
    TRIG11_IN_TCPWM0_TR_OVERFLOW1 = 0x00000B02u,
    TRIG11_IN_TCPWM0_TR_OVERFLOW2 = 0x00000B03u,
    TRIG11_IN_TCPWM0_TR_OVERFLOW3 = 0x00000B04u,
    TRIG11_IN_TCPWM0_TR_OVERFLOW4 = 0x00000B05u,
    TRIG11_IN_TCPWM0_TR_OVERFLOW5 = 0x00000B06u,
    TRIG11_IN_TCPWM0_TR_OVERFLOW6 = 0x00000B07u,
    TRIG11_IN_TCPWM0_TR_OVERFLOW7 = 0x00000B08u,
    TRIG11_IN_TCPWM0_TR_COMPARE_MATCH0 = 0x00000B09u,
    TRIG11_IN_TCPWM0_TR_COMPARE_MATCH1 = 0x00000B0Au,
    TRIG11_IN_TCPWM0_TR_COMPARE_MATCH2 = 0x00000B0Bu,
    TRIG11_IN_TCPWM0_TR_COMPARE_MATCH3 = 0x00000B0Cu,
    TRIG11_IN_TCPWM0_TR_COMPARE_MATCH4 = 0x00000B0Du,
    TRIG11_IN_TCPWM0_TR_COMPARE_MATCH5 = 0x00000B0Eu,
    TRIG11_IN_TCPWM0_TR_COMPARE_MATCH6 = 0x00000B0Fu,
    TRIG11_IN_TCPWM0_TR_COMPARE_MATCH7 = 0x00000B10u,
    TRIG11_IN_TCPWM0_TR_UNDERFLOW0 = 0x00000B11u,
    TRIG11_IN_TCPWM0_TR_UNDERFLOW1 = 0x00000B12u,
    TRIG11_IN_TCPWM0_TR_UNDERFLOW2 = 0x00000B13u,
    TRIG11_IN_TCPWM0_TR_UNDERFLOW3 = 0x00000B14u,
    TRIG11_IN_TCPWM0_TR_UNDERFLOW4 = 0x00000B15u,
    TRIG11_IN_TCPWM0_TR_UNDERFLOW5 = 0x00000B16u,
    TRIG11_IN_TCPWM0_TR_UNDERFLOW6 = 0x00000B17u,
    TRIG11_IN_TCPWM0_TR_UNDERFLOW7 = 0x00000B18u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW0 = 0x00000B19u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW1 = 0x00000B1Au,
    TRIG11_IN_TCPWM1_TR_OVERFLOW2 = 0x00000B1Bu,
    TRIG11_IN_TCPWM1_TR_OVERFLOW3 = 0x00000B1Cu,
    TRIG11_IN_TCPWM1_TR_OVERFLOW4 = 0x00000B1Du,
    TRIG11_IN_TCPWM1_TR_OVERFLOW5 = 0x00000B1Eu,
    TRIG11_IN_TCPWM1_TR_OVERFLOW6 = 0x00000B1Fu,
    TRIG11_IN_TCPWM1_TR_OVERFLOW7 = 0x00000B20u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW8 = 0x00000B21u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW9 = 0x00000B22u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW10 = 0x00000B23u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW11 = 0x00000B24u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW12 = 0x00000B25u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW13 = 0x00000B26u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW14 = 0x00000B27u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW15 = 0x00000B28u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW16 = 0x00000B29u,
    TRIG11_IN_TCPWM1_TR_OVERFLOW17 = 0x00000B2Au,
    TRIG11_IN_TCPWM1_TR_OVERFLOW18 = 0x00000B2Bu,
    TRIG11_IN_TCPWM1_TR_OVERFLOW19 = 0x00000B2Cu,
    TRIG11_IN_TCPWM1_TR_OVERFLOW20 = 0x00000B2Du,
    TRIG11_IN_TCPWM1_TR_OVERFLOW21 = 0x00000B2Eu,
    TRIG11_IN_TCPWM1_TR_OVERFLOW22 = 0x00000B2Fu,
    TRIG11_IN_TCPWM1_TR_OVERFLOW23 = 0x00000B30u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH0 = 0x00000B31u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH1 = 0x00000B32u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH2 = 0x00000B33u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH3 = 0x00000B34u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH4 = 0x00000B35u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH5 = 0x00000B36u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH6 = 0x00000B37u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH7 = 0x00000B38u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH8 = 0x00000B39u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH9 = 0x00000B3Au,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH10 = 0x00000B3Bu,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH11 = 0x00000B3Cu,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH12 = 0x00000B3Du,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH13 = 0x00000B3Eu,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH14 = 0x00000B3Fu,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH15 = 0x00000B40u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH16 = 0x00000B41u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH17 = 0x00000B42u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH18 = 0x00000B43u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH19 = 0x00000B44u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH20 = 0x00000B45u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH21 = 0x00000B46u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH22 = 0x00000B47u,
    TRIG11_IN_TCPWM1_TR_COMPARE_MATCH23 = 0x00000B48u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW0 = 0x00000B49u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW1 = 0x00000B4Au,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW2 = 0x00000B4Bu,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW3 = 0x00000B4Cu,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW4 = 0x00000B4Du,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW5 = 0x00000B4Eu,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW6 = 0x00000B4Fu,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW7 = 0x00000B50u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW8 = 0x00000B51u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW9 = 0x00000B52u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW10 = 0x00000B53u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW11 = 0x00000B54u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW12 = 0x00000B55u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW13 = 0x00000B56u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW14 = 0x00000B57u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW15 = 0x00000B58u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW16 = 0x00000B59u,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW17 = 0x00000B5Au,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW18 = 0x00000B5Bu,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW19 = 0x00000B5Cu,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW20 = 0x00000B5Du,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW21 = 0x00000B5Eu,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW22 = 0x00000B5Fu,
    TRIG11_IN_TCPWM1_TR_UNDERFLOW23 = 0x00000B60u
} en_trig_input_grp11_t;
typedef enum
{
    TRIG12_IN_CPUSS_ZERO = 0x00000C00u,
    TRIG12_IN_PERI_TR_IO_INPUT0 = 0x00000C01u,
    TRIG12_IN_PERI_TR_IO_INPUT1 = 0x00000C02u,
    TRIG12_IN_PERI_TR_IO_INPUT2 = 0x00000C03u,
    TRIG12_IN_PERI_TR_IO_INPUT3 = 0x00000C04u,
    TRIG12_IN_PERI_TR_IO_INPUT4 = 0x00000C05u,
    TRIG12_IN_PERI_TR_IO_INPUT5 = 0x00000C06u,
    TRIG12_IN_PERI_TR_IO_INPUT6 = 0x00000C07u,
    TRIG12_IN_PERI_TR_IO_INPUT7 = 0x00000C08u,
    TRIG12_IN_PERI_TR_IO_INPUT8 = 0x00000C09u,
    TRIG12_IN_PERI_TR_IO_INPUT9 = 0x00000C0Au,
    TRIG12_IN_PERI_TR_IO_INPUT10 = 0x00000C0Bu,
    TRIG12_IN_PERI_TR_IO_INPUT11 = 0x00000C0Cu,
    TRIG12_IN_PERI_TR_IO_INPUT12 = 0x00000C0Du,
    TRIG12_IN_PERI_TR_IO_INPUT13 = 0x00000C0Eu,
    TRIG12_IN_PERI_TR_IO_INPUT14 = 0x00000C0Fu,
    TRIG12_IN_PERI_TR_IO_INPUT15 = 0x00000C10u,
    TRIG12_IN_PERI_TR_IO_INPUT16 = 0x00000C11u,
    TRIG12_IN_PERI_TR_IO_INPUT17 = 0x00000C12u,
    TRIG12_IN_PERI_TR_IO_INPUT18 = 0x00000C13u,
    TRIG12_IN_PERI_TR_IO_INPUT19 = 0x00000C14u,
    TRIG12_IN_PERI_TR_IO_INPUT20 = 0x00000C15u,
    TRIG12_IN_PERI_TR_IO_INPUT21 = 0x00000C16u,
    TRIG12_IN_PERI_TR_IO_INPUT22 = 0x00000C17u,
    TRIG12_IN_PERI_TR_IO_INPUT23 = 0x00000C18u,
    TRIG12_IN_PERI_TR_IO_INPUT24 = 0x00000C19u,
    TRIG12_IN_PERI_TR_IO_INPUT25 = 0x00000C1Au,
    TRIG12_IN_PERI_TR_IO_INPUT26 = 0x00000C1Bu,
    TRIG12_IN_PERI_TR_IO_INPUT27 = 0x00000C1Cu
} en_trig_input_grp12_t;
typedef enum
{
    TRIG13_IN_CPUSS_ZERO = 0x00000D00u,
    TRIG13_IN_SCB0_TR_TX_REQ = 0x00000D01u,
    TRIG13_IN_SCB0_TR_RX_REQ = 0x00000D02u,
    TRIG13_IN_SCB1_TR_TX_REQ = 0x00000D03u,
    TRIG13_IN_SCB1_TR_RX_REQ = 0x00000D04u,
    TRIG13_IN_SCB2_TR_TX_REQ = 0x00000D05u,
    TRIG13_IN_SCB2_TR_RX_REQ = 0x00000D06u,
    TRIG13_IN_SCB3_TR_TX_REQ = 0x00000D07u,
    TRIG13_IN_SCB3_TR_RX_REQ = 0x00000D08u,
    TRIG13_IN_SCB4_TR_TX_REQ = 0x00000D09u,
    TRIG13_IN_SCB4_TR_RX_REQ = 0x00000D0Au,
    TRIG13_IN_SCB5_TR_TX_REQ = 0x00000D0Bu,
    TRIG13_IN_SCB5_TR_RX_REQ = 0x00000D0Cu,
    TRIG13_IN_SCB6_TR_TX_REQ = 0x00000D0Du,
    TRIG13_IN_SCB6_TR_RX_REQ = 0x00000D0Eu,
    TRIG13_IN_SCB7_TR_TX_REQ = 0x00000D0Fu,
    TRIG13_IN_SCB7_TR_RX_REQ = 0x00000D10u,
    TRIG13_IN_SCB8_TR_TX_REQ = 0x00000D11u,
    TRIG13_IN_SCB8_TR_RX_REQ = 0x00000D12u,
    TRIG13_IN_AUDIOSS_TR_PDM_RX_REQ = 0x00000D13u,
    TRIG13_IN_AUDIOSS_TR_I2S_TX_REQ = 0x00000D14u,
    TRIG13_IN_AUDIOSS_TR_I2S_RX_REQ = 0x00000D15u,
    TRIG13_IN_SMIF_TR_TX_REQ = 0x00000D16u,
    TRIG13_IN_SMIF_TR_RX_REQ = 0x00000D17u,
    TRIG13_IN_USB_DMA_REQ0 = 0x00000D18u,
    TRIG13_IN_USB_DMA_REQ1 = 0x00000D19u,
    TRIG13_IN_USB_DMA_REQ2 = 0x00000D1Au,
    TRIG13_IN_USB_DMA_REQ3 = 0x00000D1Bu,
    TRIG13_IN_USB_DMA_REQ4 = 0x00000D1Cu,
    TRIG13_IN_USB_DMA_REQ5 = 0x00000D1Du,
    TRIG13_IN_USB_DMA_REQ6 = 0x00000D1Eu,
    TRIG13_IN_USB_DMA_REQ7 = 0x00000D1Fu,
    TRIG13_IN_CSD_TR_ADC_DONE = 0x00000D20u,
    TRIG13_IN_CSD_DSI_SENSE_OUT = 0x00000D21u
} en_trig_input_grp13_t;
typedef enum
{
    TRIG14_IN_CPUSS_ZERO = 0x00000E00u,
    TRIG14_IN_UDB_TR_UDB0 = 0x00000E01u,
    TRIG14_IN_UDB_TR_UDB1 = 0x00000E02u,
    TRIG14_IN_UDB_TR_UDB2 = 0x00000E03u,
    TRIG14_IN_UDB_TR_UDB3 = 0x00000E04u,
    TRIG14_IN_UDB_TR_UDB4 = 0x00000E05u,
    TRIG14_IN_UDB_TR_UDB5 = 0x00000E06u,
    TRIG14_IN_UDB_TR_UDB6 = 0x00000E07u,
    TRIG14_IN_UDB_TR_UDB7 = 0x00000E08u,
    TRIG14_IN_UDB_TR_UDB8 = 0x00000E09u,
    TRIG14_IN_UDB_TR_UDB9 = 0x00000E0Au,
    TRIG14_IN_UDB_TR_UDB10 = 0x00000E0Bu,
    TRIG14_IN_UDB_TR_UDB11 = 0x00000E0Cu,
    TRIG14_IN_UDB_TR_UDB12 = 0x00000E0Du,
    TRIG14_IN_UDB_TR_UDB13 = 0x00000E0Eu,
    TRIG14_IN_UDB_TR_UDB14 = 0x00000E0Fu,
    TRIG14_IN_UDB_TR_UDB15 = 0x00000E10u,
    TRIG14_IN_UDB_DSI_OUT_TR0 = 0x00000E11u,
    TRIG14_IN_UDB_DSI_OUT_TR1 = 0x00000E12u,
    TRIG14_IN_CPUSS_CTI_TR_OUT0 = 0x00000E13u,
    TRIG14_IN_CPUSS_CTI_TR_OUT1 = 0x00000E14u,
    TRIG14_IN_PASS_TR_SAR_OUT = 0x00000E15u,
    TRIG14_IN_PASS_TR_CTDAC_EMPTY = 0x00000E16u,
    TRIG14_IN_PASS_DSI_CTB_CMP0 = 0x00000E17u,
    TRIG14_IN_PASS_DSI_CTB_CMP1 = 0x00000E18u,
    TRIG14_IN_LPCOMP_DSI_COMP0 = 0x00000E19u,
    TRIG14_IN_LPCOMP_DSI_COMP1 = 0x00000E1Au,
    TRIG14_IN_SCB0_TR_I2C_SCL_FILTERED = 0x00000E1Bu,
    TRIG14_IN_SCB1_TR_I2C_SCL_FILTERED = 0x00000E1Cu,
    TRIG14_IN_SCB2_TR_I2C_SCL_FILTERED = 0x00000E1Du,
    TRIG14_IN_SCB3_TR_I2C_SCL_FILTERED = 0x00000E1Eu,
    TRIG14_IN_SCB4_TR_I2C_SCL_FILTERED = 0x00000E1Fu,
    TRIG14_IN_SCB5_TR_I2C_SCL_FILTERED = 0x00000E20u,
    TRIG14_IN_SCB6_TR_I2C_SCL_FILTERED = 0x00000E21u,
    TRIG14_IN_SCB7_TR_I2C_SCL_FILTERED = 0x00000E22u,
    TRIG14_IN_SCB8_TR_I2C_SCL_FILTERED = 0x00000E23u,
    TRIG14_IN_CPUSS_TR_FAULT0 = 0x00000E24u,
    TRIG14_IN_CPUSS_TR_FAULT1 = 0x00000E25u
} en_trig_input_grp14_t;
typedef enum
{
    TRIG0_OUT_CPUSS_DW0_TR_IN0 = 0x40000000u,
    TRIG0_OUT_CPUSS_DW0_TR_IN1 = 0x40000001u,
    TRIG0_OUT_CPUSS_DW0_TR_IN2 = 0x40000002u,
    TRIG0_OUT_CPUSS_DW0_TR_IN3 = 0x40000003u,
    TRIG0_OUT_CPUSS_DW0_TR_IN4 = 0x40000004u,
    TRIG0_OUT_CPUSS_DW0_TR_IN5 = 0x40000005u,
    TRIG0_OUT_CPUSS_DW0_TR_IN6 = 0x40000006u,
    TRIG0_OUT_CPUSS_DW0_TR_IN7 = 0x40000007u,
    TRIG0_OUT_CPUSS_DW0_TR_IN8 = 0x40000008u,
    TRIG0_OUT_CPUSS_DW0_TR_IN9 = 0x40000009u,
    TRIG0_OUT_CPUSS_DW0_TR_IN10 = 0x4000000Au,
    TRIG0_OUT_CPUSS_DW0_TR_IN11 = 0x4000000Bu,
    TRIG0_OUT_CPUSS_DW0_TR_IN12 = 0x4000000Cu,
    TRIG0_OUT_CPUSS_DW0_TR_IN13 = 0x4000000Du,
    TRIG0_OUT_CPUSS_DW0_TR_IN14 = 0x4000000Eu,
    TRIG0_OUT_CPUSS_DW0_TR_IN15 = 0x4000000Fu
} en_trig_output_grp0_t;
typedef enum
{
    TRIG1_OUT_CPUSS_DW1_TR_IN0 = 0x40000100u,
    TRIG1_OUT_CPUSS_DW1_TR_IN1 = 0x40000101u,
    TRIG1_OUT_CPUSS_DW1_TR_IN2 = 0x40000102u,
    TRIG1_OUT_CPUSS_DW1_TR_IN3 = 0x40000103u,
    TRIG1_OUT_CPUSS_DW1_TR_IN4 = 0x40000104u,
    TRIG1_OUT_CPUSS_DW1_TR_IN5 = 0x40000105u,
    TRIG1_OUT_CPUSS_DW1_TR_IN6 = 0x40000106u,
    TRIG1_OUT_CPUSS_DW1_TR_IN7 = 0x40000107u,
    TRIG1_OUT_CPUSS_DW1_TR_IN8 = 0x40000108u,
    TRIG1_OUT_CPUSS_DW1_TR_IN9 = 0x40000109u,
    TRIG1_OUT_CPUSS_DW1_TR_IN10 = 0x4000010Au,
    TRIG1_OUT_CPUSS_DW1_TR_IN11 = 0x4000010Bu,
    TRIG1_OUT_CPUSS_DW1_TR_IN12 = 0x4000010Cu,
    TRIG1_OUT_CPUSS_DW1_TR_IN13 = 0x4000010Du,
    TRIG1_OUT_CPUSS_DW1_TR_IN14 = 0x4000010Eu,
    TRIG1_OUT_CPUSS_DW1_TR_IN15 = 0x4000010Fu
} en_trig_output_grp1_t;
typedef enum
{
    TRIG2_OUT_TCPWM0_TR_IN0 = 0x40000200u,
    TRIG2_OUT_TCPWM0_TR_IN1 = 0x40000201u,
    TRIG2_OUT_TCPWM0_TR_IN2 = 0x40000202u,
    TRIG2_OUT_TCPWM0_TR_IN3 = 0x40000203u,
    TRIG2_OUT_TCPWM0_TR_IN4 = 0x40000204u,
    TRIG2_OUT_TCPWM0_TR_IN5 = 0x40000205u,
    TRIG2_OUT_TCPWM0_TR_IN6 = 0x40000206u,
    TRIG2_OUT_TCPWM0_TR_IN7 = 0x40000207u,
    TRIG2_OUT_TCPWM0_TR_IN8 = 0x40000208u,
    TRIG2_OUT_TCPWM0_TR_IN9 = 0x40000209u,
    TRIG2_OUT_TCPWM0_TR_IN10 = 0x4000020Au,
    TRIG2_OUT_TCPWM0_TR_IN11 = 0x4000020Bu,
    TRIG2_OUT_TCPWM0_TR_IN12 = 0x4000020Cu,
    TRIG2_OUT_TCPWM0_TR_IN13 = 0x4000020Du
} en_trig_output_grp2_t;
typedef enum
{
    TRIG3_OUT_TCPWM1_TR_IN0 = 0x40000300u,
    TRIG3_OUT_TCPWM1_TR_IN1 = 0x40000301u,
    TRIG3_OUT_TCPWM1_TR_IN2 = 0x40000302u,
    TRIG3_OUT_TCPWM1_TR_IN3 = 0x40000303u,
    TRIG3_OUT_TCPWM1_TR_IN4 = 0x40000304u,
    TRIG3_OUT_TCPWM1_TR_IN5 = 0x40000305u,
    TRIG3_OUT_TCPWM1_TR_IN6 = 0x40000306u,
    TRIG3_OUT_TCPWM1_TR_IN7 = 0x40000307u,
    TRIG3_OUT_TCPWM1_TR_IN8 = 0x40000308u,
    TRIG3_OUT_TCPWM1_TR_IN9 = 0x40000309u,
    TRIG3_OUT_TCPWM1_TR_IN10 = 0x4000030Au,
    TRIG3_OUT_TCPWM1_TR_IN11 = 0x4000030Bu,
    TRIG3_OUT_TCPWM1_TR_IN12 = 0x4000030Cu,
    TRIG3_OUT_TCPWM1_TR_IN13 = 0x4000030Du
} en_trig_output_grp3_t;
typedef enum
{
    TRIG4_OUT_PROFILE_TR_START = 0x40000400u,
    TRIG4_OUT_PROFILE_TR_STOP = 0x40000401u
} en_trig_output_grp4_t;
typedef enum
{
    TRIG5_OUT_CPUSS_CTI_TR_IN0 = 0x40000500u,
    TRIG5_OUT_CPUSS_CTI_TR_IN1 = 0x40000501u
} en_trig_output_grp5_t;
typedef enum
{
    TRIG6_OUT_PASS_TR_SAR_IN = 0x40000600u
} en_trig_output_grp6_t;
typedef enum
{
    TRIG7_OUT_UDB_TR_IN0 = 0x40000700u,
    TRIG7_OUT_UDB_TR_IN1 = 0x40000701u
} en_trig_output_grp7_t;
typedef enum
{
    TRIG8_OUT_PERI_TR_IO_OUTPUT0 = 0x40000800u,
    TRIG8_OUT_PERI_TR_IO_OUTPUT1 = 0x40000801u
} en_trig_output_grp8_t;
typedef enum
{
    TRIG9_OUT_USB_DMA_BURSTEND0 = 0x40000900u,
    TRIG9_OUT_USB_DMA_BURSTEND1 = 0x40000901u,
    TRIG9_OUT_USB_DMA_BURSTEND2 = 0x40000902u,
    TRIG9_OUT_USB_DMA_BURSTEND3 = 0x40000903u,
    TRIG9_OUT_USB_DMA_BURSTEND4 = 0x40000904u,
    TRIG9_OUT_USB_DMA_BURSTEND5 = 0x40000905u,
    TRIG9_OUT_USB_DMA_BURSTEND6 = 0x40000906u,
    TRIG9_OUT_USB_DMA_BURSTEND7 = 0x40000907u
} en_trig_output_grp9_t;
typedef enum
{
    TRIG10_OUT_UDB_TR_DW_ACK0 = 0x40000A00u,
    TRIG10_OUT_TR_GROUP0_INPUT1 = 0x40000A00u,
    TRIG10_OUT_TR_GROUP1_INPUT1 = 0x40000A00u,
    TRIG10_OUT_TR_GROUP2_INPUT1 = 0x40000A00u,
    TRIG10_OUT_TR_GROUP3_INPUT1 = 0x40000A00u,
    TRIG10_OUT_TR_GROUP4_INPUT1 = 0x40000A00u,
    TRIG10_OUT_TR_GROUP5_INPUT1 = 0x40000A00u,
    TRIG10_OUT_TR_GROUP6_INPUT1 = 0x40000A00u,
    TRIG10_OUT_TR_GROUP7_INPUT1 = 0x40000A00u,
    TRIG10_OUT_TR_GROUP8_INPUT1 = 0x40000A00u,
    TRIG10_OUT_UDB_TR_DW_ACK1 = 0x40000A01u,
    TRIG10_OUT_TR_GROUP0_INPUT2 = 0x40000A01u,
    TRIG10_OUT_TR_GROUP1_INPUT2 = 0x40000A01u,
    TRIG10_OUT_TR_GROUP2_INPUT2 = 0x40000A01u,
    TRIG10_OUT_TR_GROUP3_INPUT2 = 0x40000A01u,
    TRIG10_OUT_TR_GROUP4_INPUT2 = 0x40000A01u,
    TRIG10_OUT_TR_GROUP5_INPUT2 = 0x40000A01u,
    TRIG10_OUT_TR_GROUP6_INPUT2 = 0x40000A01u,
    TRIG10_OUT_TR_GROUP7_INPUT2 = 0x40000A01u,
    TRIG10_OUT_TR_GROUP8_INPUT2 = 0x40000A01u,
    TRIG10_OUT_UDB_TR_DW_ACK2 = 0x40000A02u,
    TRIG10_OUT_TR_GROUP0_INPUT3 = 0x40000A02u,
    TRIG10_OUT_TR_GROUP1_INPUT3 = 0x40000A02u,
    TRIG10_OUT_TR_GROUP2_INPUT3 = 0x40000A02u,
    TRIG10_OUT_TR_GROUP3_INPUT3 = 0x40000A02u,
    TRIG10_OUT_TR_GROUP4_INPUT3 = 0x40000A02u,
    TRIG10_OUT_TR_GROUP5_INPUT3 = 0x40000A02u,
    TRIG10_OUT_TR_GROUP6_INPUT3 = 0x40000A02u,
    TRIG10_OUT_TR_GROUP7_INPUT3 = 0x40000A02u,
    TRIG10_OUT_TR_GROUP8_INPUT3 = 0x40000A02u,
    TRIG10_OUT_UDB_TR_DW_ACK3 = 0x40000A03u,
    TRIG10_OUT_TR_GROUP0_INPUT4 = 0x40000A03u,
    TRIG10_OUT_TR_GROUP1_INPUT4 = 0x40000A03u,
    TRIG10_OUT_TR_GROUP2_INPUT4 = 0x40000A03u,
    TRIG10_OUT_TR_GROUP3_INPUT4 = 0x40000A03u,
    TRIG10_OUT_TR_GROUP4_INPUT4 = 0x40000A03u,
    TRIG10_OUT_TR_GROUP5_INPUT4 = 0x40000A03u,
    TRIG10_OUT_TR_GROUP6_INPUT4 = 0x40000A03u,
    TRIG10_OUT_TR_GROUP7_INPUT4 = 0x40000A03u,
    TRIG10_OUT_TR_GROUP8_INPUT4 = 0x40000A03u,
    TRIG10_OUT_UDB_TR_DW_ACK4 = 0x40000A04u,
    TRIG10_OUT_TR_GROUP0_INPUT5 = 0x40000A04u,
    TRIG10_OUT_TR_GROUP1_INPUT5 = 0x40000A04u,
    TRIG10_OUT_TR_GROUP2_INPUT5 = 0x40000A04u,
    TRIG10_OUT_TR_GROUP3_INPUT5 = 0x40000A04u,
    TRIG10_OUT_TR_GROUP4_INPUT5 = 0x40000A04u,
    TRIG10_OUT_TR_GROUP5_INPUT5 = 0x40000A04u,
    TRIG10_OUT_TR_GROUP6_INPUT5 = 0x40000A04u,
    TRIG10_OUT_TR_GROUP7_INPUT5 = 0x40000A04u,
    TRIG10_OUT_TR_GROUP8_INPUT5 = 0x40000A04u,
    TRIG10_OUT_UDB_TR_DW_ACK5 = 0x40000A05u,
    TRIG10_OUT_TR_GROUP0_INPUT6 = 0x40000A05u,
    TRIG10_OUT_TR_GROUP1_INPUT6 = 0x40000A05u,
    TRIG10_OUT_TR_GROUP2_INPUT6 = 0x40000A05u,
    TRIG10_OUT_TR_GROUP3_INPUT6 = 0x40000A05u,
    TRIG10_OUT_TR_GROUP4_INPUT6 = 0x40000A05u,
    TRIG10_OUT_TR_GROUP5_INPUT6 = 0x40000A05u,
    TRIG10_OUT_TR_GROUP6_INPUT6 = 0x40000A05u,
    TRIG10_OUT_TR_GROUP7_INPUT6 = 0x40000A05u,
    TRIG10_OUT_TR_GROUP8_INPUT6 = 0x40000A05u,
    TRIG10_OUT_UDB_TR_DW_ACK6 = 0x40000A06u,
    TRIG10_OUT_TR_GROUP0_INPUT7 = 0x40000A06u,
    TRIG10_OUT_TR_GROUP1_INPUT7 = 0x40000A06u,
    TRIG10_OUT_TR_GROUP2_INPUT7 = 0x40000A06u,
    TRIG10_OUT_TR_GROUP3_INPUT7 = 0x40000A06u,
    TRIG10_OUT_TR_GROUP4_INPUT7 = 0x40000A06u,
    TRIG10_OUT_TR_GROUP5_INPUT7 = 0x40000A06u,
    TRIG10_OUT_TR_GROUP6_INPUT7 = 0x40000A06u,
    TRIG10_OUT_TR_GROUP7_INPUT7 = 0x40000A06u,
    TRIG10_OUT_TR_GROUP8_INPUT7 = 0x40000A06u,
    TRIG10_OUT_UDB_TR_DW_ACK7 = 0x40000A07u,
    TRIG10_OUT_TR_GROUP0_INPUT8 = 0x40000A07u,
    TRIG10_OUT_TR_GROUP1_INPUT8 = 0x40000A07u,
    TRIG10_OUT_TR_GROUP2_INPUT8 = 0x40000A07u,
    TRIG10_OUT_TR_GROUP3_INPUT8 = 0x40000A07u,
    TRIG10_OUT_TR_GROUP4_INPUT8 = 0x40000A07u,
    TRIG10_OUT_TR_GROUP5_INPUT8 = 0x40000A07u,
    TRIG10_OUT_TR_GROUP6_INPUT8 = 0x40000A07u,
    TRIG10_OUT_TR_GROUP7_INPUT8 = 0x40000A07u,
    TRIG10_OUT_TR_GROUP8_INPUT8 = 0x40000A07u
} en_trig_output_grp10_t;
typedef enum
{
    TRIG11_OUT_TR_GROUP0_INPUT9 = 0x40000B00u,
    TRIG11_OUT_TR_GROUP1_INPUT9 = 0x40000B00u,
    TRIG11_OUT_TR_GROUP2_INPUT9 = 0x40000B00u,
    TRIG11_OUT_TR_GROUP3_INPUT9 = 0x40000B00u,
    TRIG11_OUT_TR_GROUP4_INPUT9 = 0x40000B00u,
    TRIG11_OUT_TR_GROUP5_INPUT9 = 0x40000B00u,
    TRIG11_OUT_TR_GROUP6_INPUT9 = 0x40000B00u,
    TRIG11_OUT_TR_GROUP7_INPUT9 = 0x40000B00u,
    TRIG11_OUT_TR_GROUP8_INPUT9 = 0x40000B00u,
    TRIG11_OUT_TR_GROUP0_INPUT10 = 0x40000B01u,
    TRIG11_OUT_TR_GROUP1_INPUT10 = 0x40000B01u,
    TRIG11_OUT_TR_GROUP2_INPUT10 = 0x40000B01u,
    TRIG11_OUT_TR_GROUP3_INPUT10 = 0x40000B01u,
    TRIG11_OUT_TR_GROUP4_INPUT10 = 0x40000B01u,
    TRIG11_OUT_TR_GROUP5_INPUT10 = 0x40000B01u,
    TRIG11_OUT_TR_GROUP6_INPUT10 = 0x40000B01u,
    TRIG11_OUT_TR_GROUP7_INPUT10 = 0x40000B01u,
    TRIG11_OUT_TR_GROUP8_INPUT10 = 0x40000B01u,
    TRIG11_OUT_TR_GROUP0_INPUT11 = 0x40000B02u,
    TRIG11_OUT_TR_GROUP1_INPUT11 = 0x40000B02u,
    TRIG11_OUT_TR_GROUP2_INPUT11 = 0x40000B02u,
    TRIG11_OUT_TR_GROUP3_INPUT11 = 0x40000B02u,
    TRIG11_OUT_TR_GROUP4_INPUT11 = 0x40000B02u,
    TRIG11_OUT_TR_GROUP5_INPUT11 = 0x40000B02u,
    TRIG11_OUT_TR_GROUP6_INPUT11 = 0x40000B02u,
    TRIG11_OUT_TR_GROUP7_INPUT11 = 0x40000B02u,
    TRIG11_OUT_TR_GROUP8_INPUT11 = 0x40000B02u,
    TRIG11_OUT_TR_GROUP0_INPUT12 = 0x40000B03u,
    TRIG11_OUT_TR_GROUP1_INPUT12 = 0x40000B03u,
    TRIG11_OUT_TR_GROUP2_INPUT12 = 0x40000B03u,
    TRIG11_OUT_TR_GROUP3_INPUT12 = 0x40000B03u,
    TRIG11_OUT_TR_GROUP4_INPUT12 = 0x40000B03u,
    TRIG11_OUT_TR_GROUP5_INPUT12 = 0x40000B03u,
    TRIG11_OUT_TR_GROUP6_INPUT12 = 0x40000B03u,
    TRIG11_OUT_TR_GROUP7_INPUT12 = 0x40000B03u,
    TRIG11_OUT_TR_GROUP8_INPUT12 = 0x40000B03u,
    TRIG11_OUT_TR_GROUP0_INPUT13 = 0x40000B04u,
    TRIG11_OUT_TR_GROUP1_INPUT13 = 0x40000B04u,
    TRIG11_OUT_TR_GROUP2_INPUT13 = 0x40000B04u,
    TRIG11_OUT_TR_GROUP3_INPUT13 = 0x40000B04u,
    TRIG11_OUT_TR_GROUP4_INPUT13 = 0x40000B04u,
    TRIG11_OUT_TR_GROUP5_INPUT13 = 0x40000B04u,
    TRIG11_OUT_TR_GROUP6_INPUT13 = 0x40000B04u,
    TRIG11_OUT_TR_GROUP7_INPUT13 = 0x40000B04u,
    TRIG11_OUT_TR_GROUP8_INPUT13 = 0x40000B04u,
    TRIG11_OUT_TR_GROUP0_INPUT14 = 0x40000B05u,
    TRIG11_OUT_TR_GROUP1_INPUT14 = 0x40000B05u,
    TRIG11_OUT_TR_GROUP2_INPUT14 = 0x40000B05u,
    TRIG11_OUT_TR_GROUP3_INPUT14 = 0x40000B05u,
    TRIG11_OUT_TR_GROUP4_INPUT14 = 0x40000B05u,
    TRIG11_OUT_TR_GROUP5_INPUT14 = 0x40000B05u,
    TRIG11_OUT_TR_GROUP6_INPUT14 = 0x40000B05u,
    TRIG11_OUT_TR_GROUP7_INPUT14 = 0x40000B05u,
    TRIG11_OUT_TR_GROUP8_INPUT14 = 0x40000B05u,
    TRIG11_OUT_TR_GROUP0_INPUT15 = 0x40000B06u,
    TRIG11_OUT_TR_GROUP1_INPUT15 = 0x40000B06u,
    TRIG11_OUT_TR_GROUP2_INPUT15 = 0x40000B06u,
    TRIG11_OUT_TR_GROUP3_INPUT15 = 0x40000B06u,
    TRIG11_OUT_TR_GROUP4_INPUT15 = 0x40000B06u,
    TRIG11_OUT_TR_GROUP5_INPUT15 = 0x40000B06u,
    TRIG11_OUT_TR_GROUP6_INPUT15 = 0x40000B06u,
    TRIG11_OUT_TR_GROUP7_INPUT15 = 0x40000B06u,
    TRIG11_OUT_TR_GROUP8_INPUT15 = 0x40000B06u,
    TRIG11_OUT_TR_GROUP0_INPUT16 = 0x40000B07u,
    TRIG11_OUT_TR_GROUP1_INPUT16 = 0x40000B07u,
    TRIG11_OUT_TR_GROUP2_INPUT16 = 0x40000B07u,
    TRIG11_OUT_TR_GROUP3_INPUT16 = 0x40000B07u,
    TRIG11_OUT_TR_GROUP4_INPUT16 = 0x40000B07u,
    TRIG11_OUT_TR_GROUP5_INPUT16 = 0x40000B07u,
    TRIG11_OUT_TR_GROUP6_INPUT16 = 0x40000B07u,
    TRIG11_OUT_TR_GROUP7_INPUT16 = 0x40000B07u,
    TRIG11_OUT_TR_GROUP8_INPUT16 = 0x40000B07u,
    TRIG11_OUT_TR_GROUP0_INPUT17 = 0x40000B08u,
    TRIG11_OUT_TR_GROUP1_INPUT17 = 0x40000B08u,
    TRIG11_OUT_TR_GROUP2_INPUT17 = 0x40000B08u,
    TRIG11_OUT_TR_GROUP3_INPUT17 = 0x40000B08u,
    TRIG11_OUT_TR_GROUP4_INPUT17 = 0x40000B08u,
    TRIG11_OUT_TR_GROUP5_INPUT17 = 0x40000B08u,
    TRIG11_OUT_TR_GROUP6_INPUT17 = 0x40000B08u,
    TRIG11_OUT_TR_GROUP7_INPUT17 = 0x40000B08u,
    TRIG11_OUT_TR_GROUP8_INPUT17 = 0x40000B08u,
    TRIG11_OUT_TR_GROUP0_INPUT18 = 0x40000B09u,
    TRIG11_OUT_TR_GROUP1_INPUT18 = 0x40000B09u,
    TRIG11_OUT_TR_GROUP2_INPUT18 = 0x40000B09u,
    TRIG11_OUT_TR_GROUP3_INPUT18 = 0x40000B09u,
    TRIG11_OUT_TR_GROUP4_INPUT18 = 0x40000B09u,
    TRIG11_OUT_TR_GROUP5_INPUT18 = 0x40000B09u,
    TRIG11_OUT_TR_GROUP6_INPUT18 = 0x40000B09u,
    TRIG11_OUT_TR_GROUP7_INPUT18 = 0x40000B09u,
    TRIG11_OUT_TR_GROUP8_INPUT18 = 0x40000B09u,
    TRIG11_OUT_TR_GROUP0_INPUT19 = 0x40000B0Au,
    TRIG11_OUT_TR_GROUP1_INPUT19 = 0x40000B0Au,
    TRIG11_OUT_TR_GROUP2_INPUT19 = 0x40000B0Au,
    TRIG11_OUT_TR_GROUP3_INPUT19 = 0x40000B0Au,
    TRIG11_OUT_TR_GROUP4_INPUT19 = 0x40000B0Au,
    TRIG11_OUT_TR_GROUP5_INPUT19 = 0x40000B0Au,
    TRIG11_OUT_TR_GROUP6_INPUT19 = 0x40000B0Au,
    TRIG11_OUT_TR_GROUP7_INPUT19 = 0x40000B0Au,
    TRIG11_OUT_TR_GROUP8_INPUT19 = 0x40000B0Au,
    TRIG11_OUT_TR_GROUP0_INPUT20 = 0x40000B0Bu,
    TRIG11_OUT_TR_GROUP1_INPUT20 = 0x40000B0Bu,
    TRIG11_OUT_TR_GROUP2_INPUT20 = 0x40000B0Bu,
    TRIG11_OUT_TR_GROUP3_INPUT20 = 0x40000B0Bu,
    TRIG11_OUT_TR_GROUP4_INPUT20 = 0x40000B0Bu,
    TRIG11_OUT_TR_GROUP5_INPUT20 = 0x40000B0Bu,
    TRIG11_OUT_TR_GROUP6_INPUT20 = 0x40000B0Bu,
    TRIG11_OUT_TR_GROUP7_INPUT20 = 0x40000B0Bu,
    TRIG11_OUT_TR_GROUP8_INPUT20 = 0x40000B0Bu,
    TRIG11_OUT_TR_GROUP0_INPUT21 = 0x40000B0Cu,
    TRIG11_OUT_TR_GROUP1_INPUT21 = 0x40000B0Cu,
    TRIG11_OUT_TR_GROUP2_INPUT21 = 0x40000B0Cu,
    TRIG11_OUT_TR_GROUP3_INPUT21 = 0x40000B0Cu,
    TRIG11_OUT_TR_GROUP4_INPUT21 = 0x40000B0Cu,
    TRIG11_OUT_TR_GROUP5_INPUT21 = 0x40000B0Cu,
    TRIG11_OUT_TR_GROUP6_INPUT21 = 0x40000B0Cu,
    TRIG11_OUT_TR_GROUP7_INPUT21 = 0x40000B0Cu,
    TRIG11_OUT_TR_GROUP8_INPUT21 = 0x40000B0Cu,
    TRIG11_OUT_TR_GROUP0_INPUT22 = 0x40000B0Du,
    TRIG11_OUT_TR_GROUP1_INPUT22 = 0x40000B0Du,
    TRIG11_OUT_TR_GROUP2_INPUT22 = 0x40000B0Du,
    TRIG11_OUT_TR_GROUP3_INPUT22 = 0x40000B0Du,
    TRIG11_OUT_TR_GROUP4_INPUT22 = 0x40000B0Du,
    TRIG11_OUT_TR_GROUP5_INPUT22 = 0x40000B0Du,
    TRIG11_OUT_TR_GROUP6_INPUT22 = 0x40000B0Du,
    TRIG11_OUT_TR_GROUP7_INPUT22 = 0x40000B0Du,
    TRIG11_OUT_TR_GROUP8_INPUT22 = 0x40000B0Du,
    TRIG11_OUT_TR_GROUP0_INPUT23 = 0x40000B0Eu,
    TRIG11_OUT_TR_GROUP1_INPUT23 = 0x40000B0Eu,
    TRIG11_OUT_TR_GROUP2_INPUT23 = 0x40000B0Eu,
    TRIG11_OUT_TR_GROUP3_INPUT23 = 0x40000B0Eu,
    TRIG11_OUT_TR_GROUP4_INPUT23 = 0x40000B0Eu,
    TRIG11_OUT_TR_GROUP5_INPUT23 = 0x40000B0Eu,
    TRIG11_OUT_TR_GROUP6_INPUT23 = 0x40000B0Eu,
    TRIG11_OUT_TR_GROUP7_INPUT23 = 0x40000B0Eu,
    TRIG11_OUT_TR_GROUP8_INPUT23 = 0x40000B0Eu,
    TRIG11_OUT_TR_GROUP0_INPUT24 = 0x40000B0Fu,
    TRIG11_OUT_TR_GROUP1_INPUT24 = 0x40000B0Fu,
    TRIG11_OUT_TR_GROUP2_INPUT24 = 0x40000B0Fu,
    TRIG11_OUT_TR_GROUP3_INPUT24 = 0x40000B0Fu,
    TRIG11_OUT_TR_GROUP4_INPUT24 = 0x40000B0Fu,
    TRIG11_OUT_TR_GROUP5_INPUT24 = 0x40000B0Fu,
    TRIG11_OUT_TR_GROUP6_INPUT24 = 0x40000B0Fu,
    TRIG11_OUT_TR_GROUP7_INPUT24 = 0x40000B0Fu,
    TRIG11_OUT_TR_GROUP8_INPUT24 = 0x40000B0Fu
} en_trig_output_grp11_t;
typedef enum
{
    TRIG12_OUT_TR_GROUP2_INPUT25 = 0x40000C00u,
    TRIG12_OUT_TR_GROUP3_INPUT25 = 0x40000C00u,
    TRIG12_OUT_TR_GROUP4_INPUT25 = 0x40000C00u,
    TRIG12_OUT_TR_GROUP5_INPUT25 = 0x40000C00u,
    TRIG12_OUT_TR_GROUP6_INPUT25 = 0x40000C00u,
    TRIG12_OUT_TR_GROUP7_INPUT25 = 0x40000C00u,
    TRIG12_OUT_TR_GROUP8_INPUT25 = 0x40000C00u,
    TRIG12_OUT_TR_GROUP2_INPUT26 = 0x40000C01u,
    TRIG12_OUT_TR_GROUP3_INPUT26 = 0x40000C01u,
    TRIG12_OUT_TR_GROUP4_INPUT26 = 0x40000C01u,
    TRIG12_OUT_TR_GROUP5_INPUT26 = 0x40000C01u,
    TRIG12_OUT_TR_GROUP6_INPUT26 = 0x40000C01u,
    TRIG12_OUT_TR_GROUP7_INPUT26 = 0x40000C01u,
    TRIG12_OUT_TR_GROUP8_INPUT26 = 0x40000C01u,
    TRIG12_OUT_TR_GROUP2_INPUT27 = 0x40000C02u,
    TRIG12_OUT_TR_GROUP3_INPUT27 = 0x40000C02u,
    TRIG12_OUT_TR_GROUP4_INPUT27 = 0x40000C02u,
    TRIG12_OUT_TR_GROUP5_INPUT27 = 0x40000C02u,
    TRIG12_OUT_TR_GROUP6_INPUT27 = 0x40000C02u,
    TRIG12_OUT_TR_GROUP7_INPUT27 = 0x40000C02u,
    TRIG12_OUT_TR_GROUP8_INPUT27 = 0x40000C02u,
    TRIG12_OUT_TR_GROUP2_INPUT28 = 0x40000C03u,
    TRIG12_OUT_TR_GROUP3_INPUT28 = 0x40000C03u,
    TRIG12_OUT_TR_GROUP4_INPUT28 = 0x40000C03u,
    TRIG12_OUT_TR_GROUP5_INPUT28 = 0x40000C03u,
    TRIG12_OUT_TR_GROUP6_INPUT28 = 0x40000C03u,
    TRIG12_OUT_TR_GROUP7_INPUT28 = 0x40000C03u,
    TRIG12_OUT_TR_GROUP8_INPUT28 = 0x40000C03u,
    TRIG12_OUT_TR_GROUP2_INPUT29 = 0x40000C04u,
    TRIG12_OUT_TR_GROUP3_INPUT29 = 0x40000C04u,
    TRIG12_OUT_TR_GROUP4_INPUT29 = 0x40000C04u,
    TRIG12_OUT_TR_GROUP5_INPUT29 = 0x40000C04u,
    TRIG12_OUT_TR_GROUP6_INPUT29 = 0x40000C04u,
    TRIG12_OUT_TR_GROUP7_INPUT29 = 0x40000C04u,
    TRIG12_OUT_TR_GROUP8_INPUT29 = 0x40000C04u,
    TRIG12_OUT_TR_GROUP2_INPUT30 = 0x40000C05u,
    TRIG12_OUT_TR_GROUP3_INPUT30 = 0x40000C05u,
    TRIG12_OUT_TR_GROUP4_INPUT30 = 0x40000C05u,
    TRIG12_OUT_TR_GROUP5_INPUT30 = 0x40000C05u,
    TRIG12_OUT_TR_GROUP6_INPUT30 = 0x40000C05u,
    TRIG12_OUT_TR_GROUP7_INPUT30 = 0x40000C05u,
    TRIG12_OUT_TR_GROUP8_INPUT30 = 0x40000C05u,
    TRIG12_OUT_TR_GROUP2_INPUT31 = 0x40000C06u,
    TRIG12_OUT_TR_GROUP3_INPUT31 = 0x40000C06u,
    TRIG12_OUT_TR_GROUP4_INPUT31 = 0x40000C06u,
    TRIG12_OUT_TR_GROUP5_INPUT31 = 0x40000C06u,
    TRIG12_OUT_TR_GROUP6_INPUT31 = 0x40000C06u,
    TRIG12_OUT_TR_GROUP7_INPUT31 = 0x40000C06u,
    TRIG12_OUT_TR_GROUP8_INPUT31 = 0x40000C06u,
    TRIG12_OUT_TR_GROUP2_INPUT32 = 0x40000C07u,
    TRIG12_OUT_TR_GROUP3_INPUT32 = 0x40000C07u,
    TRIG12_OUT_TR_GROUP4_INPUT32 = 0x40000C07u,
    TRIG12_OUT_TR_GROUP5_INPUT32 = 0x40000C07u,
    TRIG12_OUT_TR_GROUP6_INPUT32 = 0x40000C07u,
    TRIG12_OUT_TR_GROUP7_INPUT32 = 0x40000C07u,
    TRIG12_OUT_TR_GROUP8_INPUT32 = 0x40000C07u,
    TRIG12_OUT_TR_GROUP0_INPUT25 = 0x40000C08u,
    TRIG12_OUT_TR_GROUP1_INPUT25 = 0x40000C08u,
    TRIG12_OUT_TR_GROUP0_INPUT26 = 0x40000C09u,
    TRIG12_OUT_TR_GROUP1_INPUT26 = 0x40000C09u
} en_trig_output_grp12_t;
typedef enum
{
    TRIG13_OUT_TR_GROUP0_INPUT27 = 0x40000D00u,
    TRIG13_OUT_TR_GROUP1_INPUT27 = 0x40000D00u,
    TRIG13_OUT_TR_GROUP0_INPUT28 = 0x40000D01u,
    TRIG13_OUT_TR_GROUP1_INPUT28 = 0x40000D01u,
    TRIG13_OUT_TR_GROUP0_INPUT29 = 0x40000D02u,
    TRIG13_OUT_TR_GROUP1_INPUT29 = 0x40000D02u,
    TRIG13_OUT_TR_GROUP0_INPUT30 = 0x40000D03u,
    TRIG13_OUT_TR_GROUP1_INPUT30 = 0x40000D03u,
    TRIG13_OUT_TR_GROUP0_INPUT31 = 0x40000D04u,
    TRIG13_OUT_TR_GROUP1_INPUT31 = 0x40000D04u,
    TRIG13_OUT_TR_GROUP0_INPUT32 = 0x40000D05u,
    TRIG13_OUT_TR_GROUP1_INPUT32 = 0x40000D05u,
    TRIG13_OUT_TR_GROUP0_INPUT33 = 0x40000D06u,
    TRIG13_OUT_TR_GROUP1_INPUT33 = 0x40000D06u,
    TRIG13_OUT_TR_GROUP0_INPUT34 = 0x40000D07u,
    TRIG13_OUT_TR_GROUP1_INPUT34 = 0x40000D07u,
    TRIG13_OUT_TR_GROUP0_INPUT35 = 0x40000D08u,
    TRIG13_OUT_TR_GROUP1_INPUT35 = 0x40000D08u,
    TRIG13_OUT_TR_GROUP0_INPUT36 = 0x40000D09u,
    TRIG13_OUT_TR_GROUP1_INPUT36 = 0x40000D09u,
    TRIG13_OUT_TR_GROUP0_INPUT37 = 0x40000D0Au,
    TRIG13_OUT_TR_GROUP1_INPUT37 = 0x40000D0Au,
    TRIG13_OUT_TR_GROUP0_INPUT38 = 0x40000D0Bu,
    TRIG13_OUT_TR_GROUP1_INPUT38 = 0x40000D0Bu,
    TRIG13_OUT_TR_GROUP0_INPUT39 = 0x40000D0Cu,
    TRIG13_OUT_TR_GROUP1_INPUT39 = 0x40000D0Cu,
    TRIG13_OUT_TR_GROUP0_INPUT40 = 0x40000D0Du,
    TRIG13_OUT_TR_GROUP1_INPUT40 = 0x40000D0Du,
    TRIG13_OUT_TR_GROUP0_INPUT41 = 0x40000D0Eu,
    TRIG13_OUT_TR_GROUP1_INPUT41 = 0x40000D0Eu,
    TRIG13_OUT_TR_GROUP0_INPUT42 = 0x40000D0Fu,
    TRIG13_OUT_TR_GROUP1_INPUT42 = 0x40000D0Fu,
    TRIG13_OUT_TR_GROUP2_INPUT33 = 0x40000D10u,
    TRIG13_OUT_TR_GROUP3_INPUT33 = 0x40000D10u,
    TRIG13_OUT_TR_GROUP4_INPUT33 = 0x40000D10u,
    TRIG13_OUT_TR_GROUP5_INPUT33 = 0x40000D10u,
    TRIG13_OUT_TR_GROUP6_INPUT33 = 0x40000D10u,
    TRIG13_OUT_TR_GROUP7_INPUT33 = 0x40000D10u,
    TRIG13_OUT_TR_GROUP8_INPUT33 = 0x40000D10u,
    TRIG13_OUT_TR_GROUP2_INPUT34 = 0x40000D11u,
    TRIG13_OUT_TR_GROUP3_INPUT34 = 0x40000D11u,
    TRIG13_OUT_TR_GROUP4_INPUT34 = 0x40000D11u,
    TRIG13_OUT_TR_GROUP5_INPUT34 = 0x40000D11u,
    TRIG13_OUT_TR_GROUP6_INPUT34 = 0x40000D11u,
    TRIG13_OUT_TR_GROUP7_INPUT34 = 0x40000D11u,
    TRIG13_OUT_TR_GROUP8_INPUT34 = 0x40000D11u
} en_trig_output_grp13_t;
typedef enum
{
    TRIG14_OUT_TR_GROUP0_INPUT43 = 0x40000E00u,
    TRIG14_OUT_TR_GROUP1_INPUT43 = 0x40000E00u,
    TRIG14_OUT_TR_GROUP0_INPUT44 = 0x40000E01u,
    TRIG14_OUT_TR_GROUP1_INPUT44 = 0x40000E01u,
    TRIG14_OUT_TR_GROUP0_INPUT45 = 0x40000E02u,
    TRIG14_OUT_TR_GROUP1_INPUT45 = 0x40000E02u,
    TRIG14_OUT_TR_GROUP0_INPUT46 = 0x40000E03u,
    TRIG14_OUT_TR_GROUP1_INPUT46 = 0x40000E03u,
    TRIG14_OUT_TR_GROUP0_INPUT47 = 0x40000E04u,
    TRIG14_OUT_TR_GROUP1_INPUT47 = 0x40000E04u,
    TRIG14_OUT_TR_GROUP0_INPUT48 = 0x40000E05u,
    TRIG14_OUT_TR_GROUP1_INPUT48 = 0x40000E05u,
    TRIG14_OUT_TR_GROUP0_INPUT49 = 0x40000E06u,
    TRIG14_OUT_TR_GROUP1_INPUT49 = 0x40000E06u,
    TRIG14_OUT_TR_GROUP0_INPUT50 = 0x40000E07u,
    TRIG14_OUT_TR_GROUP1_INPUT50 = 0x40000E07u,
    TRIG14_OUT_TR_GROUP2_INPUT35 = 0x40000E08u,
    TRIG14_OUT_TR_GROUP3_INPUT35 = 0x40000E08u,
    TRIG14_OUT_TR_GROUP4_INPUT35 = 0x40000E08u,
    TRIG14_OUT_TR_GROUP5_INPUT35 = 0x40000E08u,
    TRIG14_OUT_TR_GROUP6_INPUT35 = 0x40000E08u,
    TRIG14_OUT_TR_GROUP7_INPUT35 = 0x40000E08u,
    TRIG14_OUT_TR_GROUP8_INPUT35 = 0x40000E08u,
    TRIG14_OUT_TR_GROUP2_INPUT36 = 0x40000E09u,
    TRIG14_OUT_TR_GROUP3_INPUT36 = 0x40000E09u,
    TRIG14_OUT_TR_GROUP4_INPUT36 = 0x40000E09u,
    TRIG14_OUT_TR_GROUP5_INPUT36 = 0x40000E09u,
    TRIG14_OUT_TR_GROUP6_INPUT36 = 0x40000E09u,
    TRIG14_OUT_TR_GROUP7_INPUT36 = 0x40000E09u,
    TRIG14_OUT_TR_GROUP8_INPUT36 = 0x40000E09u,
    TRIG14_OUT_TR_GROUP2_INPUT37 = 0x40000E0Au,
    TRIG14_OUT_TR_GROUP3_INPUT37 = 0x40000E0Au,
    TRIG14_OUT_TR_GROUP4_INPUT37 = 0x40000E0Au,
    TRIG14_OUT_TR_GROUP5_INPUT37 = 0x40000E0Au,
    TRIG14_OUT_TR_GROUP6_INPUT37 = 0x40000E0Au,
    TRIG14_OUT_TR_GROUP7_INPUT37 = 0x40000E0Au,
    TRIG14_OUT_TR_GROUP8_INPUT37 = 0x40000E0Au,
    TRIG14_OUT_TR_GROUP2_INPUT38 = 0x40000E0Bu,
    TRIG14_OUT_TR_GROUP3_INPUT38 = 0x40000E0Bu,
    TRIG14_OUT_TR_GROUP4_INPUT38 = 0x40000E0Bu,
    TRIG14_OUT_TR_GROUP5_INPUT38 = 0x40000E0Bu,
    TRIG14_OUT_TR_GROUP6_INPUT38 = 0x40000E0Bu,
    TRIG14_OUT_TR_GROUP7_INPUT38 = 0x40000E0Bu,
    TRIG14_OUT_TR_GROUP8_INPUT38 = 0x40000E0Bu,
    TRIG14_OUT_TR_GROUP2_INPUT39 = 0x40000E0Cu,
    TRIG14_OUT_TR_GROUP3_INPUT39 = 0x40000E0Cu,
    TRIG14_OUT_TR_GROUP4_INPUT39 = 0x40000E0Cu,
    TRIG14_OUT_TR_GROUP5_INPUT39 = 0x40000E0Cu,
    TRIG14_OUT_TR_GROUP6_INPUT39 = 0x40000E0Cu,
    TRIG14_OUT_TR_GROUP7_INPUT39 = 0x40000E0Cu,
    TRIG14_OUT_TR_GROUP8_INPUT39 = 0x40000E0Cu,
    TRIG14_OUT_TR_GROUP2_INPUT40 = 0x40000E0Du,
    TRIG14_OUT_TR_GROUP3_INPUT40 = 0x40000E0Du,
    TRIG14_OUT_TR_GROUP4_INPUT40 = 0x40000E0Du,
    TRIG14_OUT_TR_GROUP5_INPUT40 = 0x40000E0Du,
    TRIG14_OUT_TR_GROUP6_INPUT40 = 0x40000E0Du,
    TRIG14_OUT_TR_GROUP7_INPUT40 = 0x40000E0Du,
    TRIG14_OUT_TR_GROUP8_INPUT40 = 0x40000E0Du,
    TRIG14_OUT_TR_GROUP2_INPUT41 = 0x40000E0Eu,
    TRIG14_OUT_TR_GROUP3_INPUT41 = 0x40000E0Eu,
    TRIG14_OUT_TR_GROUP4_INPUT41 = 0x40000E0Eu,
    TRIG14_OUT_TR_GROUP5_INPUT41 = 0x40000E0Eu,
    TRIG14_OUT_TR_GROUP6_INPUT41 = 0x40000E0Eu,
    TRIG14_OUT_TR_GROUP7_INPUT41 = 0x40000E0Eu,
    TRIG14_OUT_TR_GROUP8_INPUT41 = 0x40000E0Eu,
    TRIG14_OUT_TR_GROUP2_INPUT42 = 0x40000E0Fu,
    TRIG14_OUT_TR_GROUP3_INPUT42 = 0x40000E0Fu,
    TRIG14_OUT_TR_GROUP4_INPUT42 = 0x40000E0Fu,
    TRIG14_OUT_TR_GROUP5_INPUT42 = 0x40000E0Fu,
    TRIG14_OUT_TR_GROUP6_INPUT42 = 0x40000E0Fu,
    TRIG14_OUT_TR_GROUP7_INPUT42 = 0x40000E0Fu,
    TRIG14_OUT_TR_GROUP8_INPUT42 = 0x40000E0Fu
} en_trig_output_grp14_t;
typedef enum
{
    TRIGGER_TYPE_LEVEL = 0u,
    TRIGGER_TYPE_EDGE = 1u
} en_trig_type_t;
typedef enum
{
    CPUSS_MPU_VIO_0 = 0x0000u,
    CPUSS_MPU_VIO_1 = 0x0001u,
    CPUSS_MPU_VIO_2 = 0x0002u,
    CPUSS_MPU_VIO_3 = 0x0003u,
    CPUSS_MPU_VIO_14 = 0x000Eu,
    CPUSS_MPU_VIO_15 = 0x000Fu,
    CPUSS_MPU_VIO_16 = 0x0010u,
    PERI_MS_VIO_0 = 0x001Cu,
    PERI_MS_VIO_1 = 0x001Du,
    PERI_MS_VIO_2 = 0x001Eu,
    PERI_MS_VIO_3 = 0x001Fu,
    PERI_GROUP_VIO_0 = 0x0020u,
    PERI_GROUP_VIO_1 = 0x0021u,
    PERI_GROUP_VIO_2 = 0x0022u,
    PERI_GROUP_VIO_3 = 0x0023u,
    PERI_GROUP_VIO_4 = 0x0024u,
    PERI_GROUP_VIO_6 = 0x0026u,
    PERI_GROUP_VIO_9 = 0x0029u,
    PERI_GROUP_VIO_10 = 0x002Au,
    CPUSS_FLASHC_MAIN_BUS_ERR = 0x0032u
} en_sysfault_source_t;
typedef enum
{
    PROFILE_ONE = 0,
    CPUSS_MONITOR_CM0 = 1,
    CPUSS_MONITOR_CM4 = 2,
    CPUSS_MONITOR_FLASH = 3,
    CPUSS_MONITOR_DW0_AHB = 4,
    CPUSS_MONITOR_DW1_AHB = 5,
    CPUSS_MONITOR_CRYPTO = 6,
    USB_MONITOR_AHB = 7,
    SCB0_MONITOR_AHB = 8,
    SCB1_MONITOR_AHB = 9,
    SCB2_MONITOR_AHB = 10,
    SCB3_MONITOR_AHB = 11,
    SCB4_MONITOR_AHB = 12,
    SCB5_MONITOR_AHB = 13,
    SCB6_MONITOR_AHB = 14,
    SCB7_MONITOR_AHB = 15,
    SCB8_MONITOR_AHB = 16,
    UDB_MONITOR_UDB0 = 17,
    UDB_MONITOR_UDB1 = 18,
    UDB_MONITOR_UDB2 = 19,
    UDB_MONITOR_UDB3 = 20,
    SMIF_MONITOR_SMIF_SPI_SELECT0 = 21,
    SMIF_MONITOR_SMIF_SPI_SELECT1 = 22,
    SMIF_MONITOR_SMIF_SPI_SELECT2 = 23,
    SMIF_MONITOR_SMIF_SPI_SELECT3 = 24,
    SMIF_MONITOR_SMIF_SPI_SELECT_ANY = 25,
    BLESS_EXT_LNA_RX_CTL_OUT = 26,
    BLESS_EXT_PA_TX_CTL_OUT = 27
} en_ep_mon_sel_t;
typedef enum
{
    CPUSS_MS_ID_CM0 = 0,
    CPUSS_MS_ID_CRYPTO = 1,
    CPUSS_MS_ID_DW0 = 2,
    CPUSS_MS_ID_DW1 = 3,
    CPUSS_MS_ID_CM4 = 14,
    CPUSS_MS_ID_TC = 15
} en_prot_master_t;
typedef struct {
   volatile const uint8_t RESERVED;
  volatile uint8_t SI_REVISION_ID;
  volatile uint16_t SILICON_ID;
   volatile const uint32_t RESERVED1[2];
  volatile uint16_t FAMILY_ID;
  volatile uint8_t SYSCALL_ERASE_PROT;
   volatile const uint8_t RESERVED2[5];
  volatile uint32_t CPUSS_WOUNDING;
   volatile const uint32_t RESERVED3[4];
  volatile uint32_t SFLASH_SVN;
   volatile const uint32_t RESERVED4[20];
  volatile uint32_t FB_FLAGS;
   volatile const uint32_t RESERVED5[352];
  volatile uint8_t DIE_LOT[3];
  volatile uint8_t DIE_WAFER;
  volatile uint8_t DIE_X;
  volatile uint8_t DIE_Y;
  volatile uint8_t DIE_SORT;
  volatile uint8_t DIE_MINOR;
  volatile uint8_t DIE_DAY;
  volatile uint8_t DIE_MONTH;
  volatile uint8_t DIE_YEAR;
   volatile const uint8_t RESERVED6[61];
  volatile uint16_t SAR_TEMP_MULTIPLIER;
  volatile uint16_t SAR_TEMP_OFFSET;
   volatile const uint32_t RESERVED7[8];
  volatile uint32_t CSP_PANEL_ID;
   volatile const uint32_t RESERVED8[52];
  volatile uint8_t LDO_0P9V_TRIM;
  volatile uint8_t LDO_1P1V_TRIM;
   volatile const uint16_t RESERVED9[95];
  volatile uint32_t BLE_DEVICE_ADDRESS[128];
  volatile uint32_t USER_FREE_ROW1[128];
  volatile uint32_t USER_FREE_ROW2[128];
  volatile uint32_t USER_FREE_ROW3[128];
   volatile const uint32_t RESERVED10[302];
  volatile uint8_t DEVICE_UID[16];
  volatile uint8_t MASTER_KEY[16];
  volatile uint32_t STANDARD_SMPU_STRUCT_SLAVE_ADDR[16];
  volatile uint32_t STANDARD_SMPU_STRUCT_SLAVE_ATTR[16];
  volatile uint32_t STANDARD_SMPU_STRUCT_MASTER_ATTR[16];
  volatile uint32_t STANDARD_MPU_STRUCT[16];
  volatile uint32_t STANDARD_PPU_STRUCT[16];
   volatile const uint32_t RESERVED11[122];
  volatile uint16_t PILO_FREQ_STEP;
   volatile const uint16_t RESERVED12;
  volatile uint32_t CSDV2_CSD0_ADC_VREF0;
  volatile uint32_t CSDV2_CSD0_ADC_VREF1;
  volatile uint32_t CSDV2_CSD0_ADC_VREF2;
  volatile uint32_t PWR_TRIM_WAKE_CTL;
   volatile const uint16_t RESERVED13;
  volatile uint16_t RADIO_LDO_TRIMS;
  volatile uint32_t CPUSS_TRIM_ROM_CTL_ULP;
  volatile uint32_t CPUSS_TRIM_RAM_CTL_ULP;
  volatile uint32_t CPUSS_TRIM_ROM_CTL_LP;
  volatile uint32_t CPUSS_TRIM_RAM_CTL_LP;
   volatile const uint32_t RESERVED14[7];
  volatile uint32_t CPUSS_TRIM_ROM_CTL_HALF_ULP;
  volatile uint32_t CPUSS_TRIM_RAM_CTL_HALF_ULP;
  volatile uint32_t CPUSS_TRIM_ROM_CTL_HALF_LP;
  volatile uint32_t CPUSS_TRIM_RAM_CTL_HALF_LP;
   volatile const uint32_t RESERVED15[491];
  volatile uint32_t FLASH_BOOT_OBJECT_SIZE;
  volatile uint32_t FLASH_BOOT_APP_ID;
  volatile uint32_t FLASH_BOOT_ATTRIBUTE;
  volatile uint32_t FLASH_BOOT_N_CORES;
  volatile uint32_t FLASH_BOOT_VT_OFFSET;
  volatile uint32_t FLASH_BOOT_CORE_CPUID;
   volatile const uint32_t RESERVED16[48];
  volatile uint8_t FLASH_BOOT_CODE[14632];
  volatile uint8_t PUBLIC_KEY[3072];
  volatile uint32_t BOOT_PROT_SETTINGS[384];
   volatile const uint32_t RESERVED17[768];
  volatile uint32_t TOC1_OBJECT_SIZE;
  volatile uint32_t TOC1_MAGIC_NUMBER;
  volatile uint32_t TOC1_FHASH_OBJECTS;
  volatile uint32_t TOC1_GENERAL_TRIM_ADDR_UNUSED;
  volatile uint32_t TOC1_UNIQUE_ID_ADDR;
  volatile uint32_t TOC1_FB_OBJECT_ADDR;
  volatile uint32_t TOC1_SYSCALL_TABLE_ADDR_UNUSED;
  volatile uint32_t TOC1_OBJECT_ADDR_UNUSED;
   volatile const uint32_t RESERVED18[119];
  volatile uint32_t TOC1_CRC_ADDR;
  volatile uint32_t RTOC1_OBJECT_SIZE;
  volatile uint32_t RTOC1_MAGIC_NUMBER;
  volatile uint32_t RTOC1_FHASH_OBJECTS;
  volatile uint32_t RTOC1_GENERAL_TRIM_ADDR_UNUSED;
  volatile uint32_t RTOC1_UNIQUE_ID_ADDR;
  volatile uint32_t RTOC1_FB_OBJECT_ADDR;
  volatile uint32_t RTOC1_SYSCALL_TABLE_ADDR_UNUSED;
  volatile uint32_t RTOC1_OBJECT_ADDR_UNUSED;
   volatile const uint32_t RESERVED19[119];
  volatile uint32_t RTOC1_CRC_ADDR;
  volatile uint32_t TOC2_OBJECT_SIZE;
  volatile uint32_t TOC2_MAGIC_NUMBER;
  volatile uint32_t TOC2_KEY_BLOCK_ADDR;
  volatile uint32_t TOC2_SMIF_CFG_STRUCT_ADDR;
  volatile uint32_t TOC2_FIRST_USER_APP_ADDR;
  volatile uint32_t TOC2_FIRST_USER_APP_FORMAT;
  volatile uint32_t TOC2_SECOND_USER_APP_ADDR;
  volatile uint32_t TOC2_SECOND_USER_APP_FORMAT;
  volatile uint32_t TOC2_SHASH_OBJECTS;
  volatile uint32_t TOC2_SIGNATURE_VERIF_KEY;
   volatile const uint32_t RESERVED20[115];
  volatile uint32_t TOC2_REVISION;
  volatile uint32_t TOC2_FLAGS;
  volatile uint32_t TOC2_CRC_ADDR;
  volatile uint32_t RTOC2_OBJECT_SIZE;
  volatile uint32_t RTOC2_MAGIC_NUMBER;
  volatile uint32_t RTOC2_KEY_BLOCK_ADDR;
  volatile uint32_t RTOC2_SMIF_CFG_STRUCT_ADDR;
  volatile uint32_t RTOC2_FIRST_USER_APP_ADDR;
  volatile uint32_t RTOC2_FIRST_USER_APP_FORMAT;
  volatile uint32_t RTOC2_SECOND_USER_APP_ADDR;
  volatile uint32_t RTOC2_SECOND_USER_APP_FORMAT;
  volatile uint32_t RTOC2_SHASH_OBJECTS;
  volatile uint32_t RTOC2_SIGNATURE_VERIF_KEY;
   volatile const uint32_t RESERVED21[115];
  volatile uint32_t RTOC2_REVISION;
  volatile uint32_t RTOC2_FLAGS;
  volatile uint32_t RTOC2_CRC_ADDR;
} SFLASH_V1_Type;
typedef struct {
  volatile uint32_t CLOCK_CTL;
   volatile const uint32_t RESERVED[7];
  volatile uint32_t SL_CTL;
  volatile uint32_t TIMEOUT_CTL;
   volatile const uint32_t RESERVED1[6];
} PERI_GR_V1_Type;
typedef struct {
  volatile uint32_t TR_OUT_CTL[128];
} PERI_TR_GR_V1_Type;
typedef struct {
  volatile uint32_t ADDR0;
  volatile uint32_t ATT0;
   volatile const uint32_t RESERVED[6];
   volatile const uint32_t ADDR1;
  volatile uint32_t ATT1;
   volatile const uint32_t RESERVED1[6];
} PERI_PPU_PR_V1_Type;
typedef struct {
   volatile const uint32_t ADDR0;
  volatile uint32_t ATT0;
   volatile const uint32_t RESERVED[6];
   volatile const uint32_t ADDR1;
  volatile uint32_t ATT1;
   volatile const uint32_t RESERVED1[6];
} PERI_PPU_GR_V1_Type;
typedef struct {
   volatile const uint32_t ADDR0;
  volatile uint32_t ATT0;
   volatile const uint32_t RESERVED[6];
   volatile const uint32_t ADDR1;
  volatile uint32_t ATT1;
   volatile const uint32_t RESERVED1[6];
} PERI_GR_PPU_SL_V1_Type;
typedef struct {
   volatile const uint32_t ADDR0;
  volatile uint32_t ATT0;
   volatile const uint32_t RESERVED[6];
   volatile const uint32_t ADDR1;
  volatile uint32_t ATT1;
   volatile const uint32_t RESERVED1[6];
} PERI_GR_PPU_RG_V1_Type;
typedef struct {
        PERI_GR_V1_Type GR[16];
  volatile uint32_t DIV_CMD;
   volatile const uint32_t RESERVED[255];
  volatile uint32_t DIV_8_CTL[64];
  volatile uint32_t DIV_16_CTL[64];
  volatile uint32_t DIV_16_5_CTL[64];
  volatile uint32_t DIV_24_5_CTL[63];
   volatile const uint32_t RESERVED1;
  volatile uint32_t CLOCK_CTL[128];
   volatile const uint32_t RESERVED2[128];
  volatile uint32_t TR_CMD;
   volatile const uint32_t RESERVED3[1023];
        PERI_TR_GR_V1_Type TR_GR[16];
        PERI_PPU_PR_V1_Type PPU_PR[32];
   volatile const uint32_t RESERVED4[512];
        PERI_PPU_GR_V1_Type PPU_GR[16];
} PERI_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t STATUS;
  volatile uint32_t RAM_PWRUP_DELAY;
   volatile const uint32_t RESERVED[5];
   volatile const uint32_t ERROR_STATUS0;
  volatile uint32_t ERROR_STATUS1;
   volatile const uint32_t RESERVED1[6];
  volatile uint32_t INSTR_FF_CTL;
   volatile const uint32_t INSTR_FF_STATUS;
   volatile uint32_t INSTR_FF_WR;
   volatile const uint32_t RESERVED2[13];
   volatile const uint32_t RF_DATA[16];
   volatile const uint32_t RESERVED3[16];
  volatile uint32_t AES_CTL;
   volatile const uint32_t RESERVED4[31];
   volatile const uint32_t STR_RESULT;
   volatile const uint32_t RESERVED5[31];
  volatile uint32_t PR_LFSR_CTL0;
  volatile uint32_t PR_LFSR_CTL1;
  volatile uint32_t PR_LFSR_CTL2;
   volatile const uint32_t RESERVED6;
  volatile uint32_t PR_RESULT;
   volatile const uint32_t RESERVED7[27];
  volatile uint32_t TR_CTL0;
  volatile uint32_t TR_CTL1;
  volatile uint32_t TR_RESULT;
   volatile const uint32_t RESERVED8[5];
  volatile uint32_t TR_GARO_CTL;
  volatile uint32_t TR_FIRO_CTL;
   volatile const uint32_t RESERVED9[6];
  volatile uint32_t TR_MON_CTL;
   volatile const uint32_t RESERVED10;
  volatile uint32_t TR_MON_CMD;
   volatile const uint32_t RESERVED11;
  volatile uint32_t TR_MON_RC_CTL;
   volatile const uint32_t RESERVED12;
   volatile const uint32_t TR_MON_RC_STATUS0;
   volatile const uint32_t TR_MON_RC_STATUS1;
  volatile uint32_t TR_MON_AP_CTL;
   volatile const uint32_t RESERVED13;
   volatile const uint32_t TR_MON_AP_STATUS0;
   volatile const uint32_t TR_MON_AP_STATUS1;
   volatile const uint32_t RESERVED14[4];
  volatile uint32_t SHA_CTL;
   volatile const uint32_t RESERVED15[63];
  volatile uint32_t CRC_CTL;
   volatile const uint32_t RESERVED16[3];
  volatile uint32_t CRC_DATA_CTL;
   volatile const uint32_t RESERVED17[3];
  volatile uint32_t CRC_POL_CTL;
   volatile const uint32_t RESERVED18[3];
  volatile uint32_t CRC_LFSR_CTL;
   volatile const uint32_t RESERVED19[3];
  volatile uint32_t CRC_REM_CTL;
   volatile const uint32_t RESERVED20;
   volatile const uint32_t CRC_REM_RESULT;
   volatile const uint32_t RESERVED21[13];
  volatile uint32_t VU_CTL0;
  volatile uint32_t VU_CTL1;
   volatile const uint32_t RESERVED22[2];
   volatile const uint32_t VU_STATUS;
   volatile const uint32_t RESERVED23[203];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED24[3596];
  volatile uint32_t MEM_BUFF[4096];
} CRYPTO_V1_Type;
typedef struct {
  volatile uint32_t CM0_CTL;
   volatile const uint32_t RESERVED;
   volatile const uint32_t CM0_STATUS;
   volatile const uint32_t RESERVED1;
  volatile uint32_t CM0_CLOCK_CTL;
   volatile const uint32_t RESERVED2[3];
  volatile uint32_t CM0_INT_CTL0;
  volatile uint32_t CM0_INT_CTL1;
  volatile uint32_t CM0_INT_CTL2;
  volatile uint32_t CM0_INT_CTL3;
  volatile uint32_t CM0_INT_CTL4;
  volatile uint32_t CM0_INT_CTL5;
  volatile uint32_t CM0_INT_CTL6;
  volatile uint32_t CM0_INT_CTL7;
   volatile const uint32_t RESERVED3[16];
  volatile uint32_t CM4_PWR_CTL;
  volatile uint32_t CM4_PWR_DELAY_CTL;
   volatile const uint32_t CM4_STATUS;
   volatile const uint32_t RESERVED4;
  volatile uint32_t CM4_CLOCK_CTL;
   volatile const uint32_t RESERVED5[3];
  volatile uint32_t CM4_NMI_CTL;
   volatile const uint32_t RESERVED6[23];
  volatile uint32_t RAM0_CTL0;
   volatile const uint32_t RESERVED7[15];
  volatile uint32_t RAM0_PWR_MACRO_CTL[16];
  volatile uint32_t RAM1_CTL0;
   volatile const uint32_t RESERVED8[3];
  volatile uint32_t RAM1_PWR_CTL;
   volatile const uint32_t RESERVED9[3];
  volatile uint32_t RAM2_CTL0;
   volatile const uint32_t RESERVED10[3];
  volatile uint32_t RAM2_PWR_CTL;
   volatile const uint32_t RESERVED11[3];
  volatile uint32_t RAM_PWR_DELAY_CTL;
   volatile const uint32_t RESERVED12[3];
  volatile uint32_t ROM_CTL;
   volatile const uint32_t RESERVED13[7];
  volatile uint32_t UDB_PWR_CTL;
  volatile uint32_t UDB_PWR_DELAY_CTL;
   volatile const uint32_t RESERVED14[4];
   volatile const uint32_t DP_STATUS;
   volatile const uint32_t RESERVED15[5];
  volatile uint32_t BUFF_CTL;
   volatile const uint32_t RESERVED16[3];
  volatile uint32_t DDFT_CTL;
   volatile const uint32_t RESERVED17[3];
  volatile uint32_t SYSTICK_CTL;
   volatile const uint32_t RESERVED18[27];
  volatile uint32_t CM0_VECTOR_TABLE_BASE;
   volatile const uint32_t RESERVED19[3];
  volatile uint32_t CM4_VECTOR_TABLE_BASE;
   volatile const uint32_t RESERVED20[23];
  volatile uint32_t CM0_PC0_HANDLER;
   volatile const uint32_t RESERVED21[55];
   volatile const uint32_t IDENTITY;
   volatile const uint32_t RESERVED22[63];
  volatile uint32_t PROTECTION;
   volatile const uint32_t RESERVED23[7];
  volatile uint32_t CM0_NMI_CTL;
   volatile const uint32_t RESERVED24[7];
  volatile uint32_t AP_CTL;
   volatile const uint32_t RESERVED25[23];
   volatile const uint32_t MBIST_STAT;
   volatile const uint32_t RESERVED26[14999];
  volatile uint32_t TRIM_ROM_CTL;
  volatile uint32_t TRIM_RAM_CTL;
} CPUSS_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED[2];
  volatile uint32_t STATUS;
   volatile const uint32_t DATA[4];
   volatile const uint32_t RESERVED1[8];
   volatile const uint32_t PENDING0;
   volatile const uint32_t PENDING1;
   volatile const uint32_t PENDING2;
   volatile const uint32_t RESERVED2;
  volatile uint32_t MASK0;
  volatile uint32_t MASK1;
  volatile uint32_t MASK2;
   volatile const uint32_t RESERVED3[25];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED4[12];
} FAULT_STRUCT_V1_Type;
typedef struct {
        FAULT_STRUCT_V1_Type STRUCT[4];
} FAULT_V1_Type;
typedef struct {
   volatile const uint32_t ACQUIRE;
   volatile uint32_t RELEASE;
   volatile uint32_t NOTIFY;
  volatile uint32_t DATA;
   volatile const uint32_t LOCK_STATUS;
   volatile const uint32_t RESERVED[3];
} IPC_STRUCT_V1_Type;
typedef struct {
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED[4];
} IPC_INTR_STRUCT_V1_Type;
typedef struct {
        IPC_STRUCT_V1_Type STRUCT[16];
   volatile const uint32_t RESERVED[896];
        IPC_INTR_STRUCT_V1_Type INTR_STRUCT[16];
} IPC_V1_Type;
typedef struct {
  volatile uint32_t ADDR0;
  volatile uint32_t ATT0;
   volatile const uint32_t RESERVED[6];
   volatile const uint32_t ADDR1;
  volatile uint32_t ATT1;
   volatile const uint32_t RESERVED1[6];
} PROT_SMPU_SMPU_STRUCT_V1_Type;
typedef struct {
  volatile uint32_t MS0_CTL;
  volatile uint32_t MS1_CTL;
  volatile uint32_t MS2_CTL;
  volatile uint32_t MS3_CTL;
  volatile uint32_t MS4_CTL;
  volatile uint32_t MS5_CTL;
  volatile uint32_t MS6_CTL;
  volatile uint32_t MS7_CTL;
  volatile uint32_t MS8_CTL;
  volatile uint32_t MS9_CTL;
  volatile uint32_t MS10_CTL;
  volatile uint32_t MS11_CTL;
  volatile uint32_t MS12_CTL;
  volatile uint32_t MS13_CTL;
  volatile uint32_t MS14_CTL;
  volatile uint32_t MS15_CTL;
   volatile const uint32_t RESERVED[2032];
        PROT_SMPU_SMPU_STRUCT_V1_Type SMPU_STRUCT[32];
   volatile const uint32_t RESERVED1[1536];
} PROT_SMPU_V1_Type;
typedef struct {
  volatile uint32_t ADDR;
  volatile uint32_t ATT;
   volatile const uint32_t RESERVED[6];
} PROT_MPU_MPU_STRUCT_V1_Type;
typedef struct {
  volatile uint32_t MS_CTL;
   volatile const uint32_t MS_CTL_READ_MIR[127];
        PROT_MPU_MPU_STRUCT_V1_Type MPU_STRUCT[16];
} PROT_MPU_V1_Type;
typedef struct {
        PROT_SMPU_V1_Type SMPU;
        PROT_MPU_V1_Type CYMPU[16];
} PROT_V1_Type;
typedef struct {
  volatile uint32_t FM_CTL;
   volatile const uint32_t STATUS;
  volatile uint32_t FM_ADDR;
   volatile const uint32_t GEOMETRY;
   volatile const uint32_t GEOMETRY_SUPERVISORY;
  volatile uint32_t TIMER_CTL;
  volatile uint32_t ANA_CTL0;
  volatile uint32_t ANA_CTL1;
   volatile const uint32_t GEOMETRY_GEN;
  volatile uint32_t TEST_CTL;
  volatile uint32_t WAIT_CTL;
   volatile const uint32_t MONITOR_STATUS;
  volatile uint32_t SCRATCH_CTL;
  volatile uint32_t HV_CTL;
   volatile uint32_t ACLK_CTL;
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile uint32_t FM_HV_DATA_ALL;
  volatile uint32_t CAL_CTL0;
  volatile uint32_t CAL_CTL1;
  volatile uint32_t CAL_CTL2;
  volatile uint32_t CAL_CTL3;
   volatile uint32_t BOOKMARK;
   volatile const uint32_t RESERVED[7];
  volatile uint32_t RED_CTL01;
  volatile uint32_t RED_CTL23;
  volatile uint32_t RED_CTL45;
  volatile uint32_t RED_CTL67;
  volatile uint32_t RED_CTL_SM01;
   volatile const uint32_t RESERVED1[27];
   volatile const uint32_t TM_CMPR[32];
   volatile const uint32_t RESERVED2[416];
  volatile uint32_t FM_HV_DATA[256];
   volatile const uint32_t FM_MEM_DATA[256];
} FLASHC_FM_CTL_V1_Type;
typedef struct {
  volatile uint32_t FLASH_CTL;
  volatile uint32_t FLASH_PWR_CTL;
  volatile uint32_t FLASH_CMD;
   volatile const uint32_t RESERVED[61];
  volatile uint32_t BIST_CTL;
  volatile uint32_t BIST_CMD;
  volatile uint32_t BIST_ADDR_START;
  volatile uint32_t BIST_DATA[8];
   volatile const uint32_t BIST_DATA_ACT[8];
   volatile const uint32_t BIST_DATA_EXP[8];
   volatile const uint32_t BIST_ADDR;
  volatile uint32_t BIST_STATUS;
   volatile const uint32_t RESERVED1[163];
  volatile uint32_t CM0_CA_CTL0;
  volatile uint32_t CM0_CA_CTL1;
  volatile uint32_t CM0_CA_CTL2;
  volatile uint32_t CM0_CA_CMD;
   volatile const uint32_t RESERVED2[12];
   volatile const uint32_t CM0_CA_STATUS0;
   volatile const uint32_t CM0_CA_STATUS1;
   volatile const uint32_t CM0_CA_STATUS2;
   volatile const uint32_t RESERVED3[13];
  volatile uint32_t CM4_CA_CTL0;
  volatile uint32_t CM4_CA_CTL1;
  volatile uint32_t CM4_CA_CTL2;
  volatile uint32_t CM4_CA_CMD;
   volatile const uint32_t RESERVED4[12];
   volatile const uint32_t CM4_CA_STATUS0;
   volatile const uint32_t CM4_CA_STATUS1;
   volatile const uint32_t CM4_CA_STATUS2;
   volatile const uint32_t RESERVED5[13];
  volatile uint32_t CRYPTO_BUFF_CTL;
   volatile const uint32_t RESERVED6;
  volatile uint32_t CRYPTO_BUFF_CMD;
   volatile const uint32_t RESERVED7[29];
  volatile uint32_t DW0_BUFF_CTL;
   volatile const uint32_t RESERVED8;
  volatile uint32_t DW0_BUFF_CMD;
   volatile const uint32_t RESERVED9[29];
  volatile uint32_t DW1_BUFF_CTL;
   volatile const uint32_t RESERVED10;
  volatile uint32_t DW1_BUFF_CMD;
   volatile const uint32_t RESERVED11[29];
  volatile uint32_t DAP_BUFF_CTL;
   volatile const uint32_t RESERVED12;
  volatile uint32_t DAP_BUFF_CMD;
   volatile const uint32_t RESERVED13[29];
  volatile uint32_t EXT_MS0_BUFF_CTL;
   volatile const uint32_t RESERVED14;
  volatile uint32_t EXT_MS0_BUFF_CMD;
   volatile const uint32_t RESERVED15[29];
  volatile uint32_t EXT_MS1_BUFF_CTL;
   volatile const uint32_t RESERVED16;
  volatile uint32_t EXT_MS1_BUFF_CMD;
   volatile const uint32_t RESERVED17[14877];
        FLASHC_FM_CTL_V1_Type FM_CTL;
} FLASHC_V1_Type;
typedef struct {
   volatile const uint32_t RESERVED;
  volatile uint32_t MCWDT_CNTLOW;
  volatile uint32_t MCWDT_CNTHIGH;
  volatile uint32_t MCWDT_MATCH;
  volatile uint32_t MCWDT_CONFIG;
  volatile uint32_t MCWDT_CTL;
  volatile uint32_t MCWDT_INTR;
  volatile uint32_t MCWDT_INTR_SET;
  volatile uint32_t MCWDT_INTR_MASK;
   volatile const uint32_t MCWDT_INTR_MASKED;
  volatile uint32_t MCWDT_LOCK;
   volatile const uint32_t RESERVED1[5];
} MCWDT_STRUCT_V1_Type;
typedef struct {
  volatile uint32_t PWR_CTL;
  volatile uint32_t PWR_HIBERNATE;
  volatile uint32_t PWR_LVD_CTL;
   volatile const uint32_t RESERVED[2];
  volatile uint32_t PWR_BUCK_CTL;
  volatile uint32_t PWR_BUCK_CTL2;
   volatile const uint32_t PWR_LVD_STATUS;
   volatile const uint32_t RESERVED1[24];
  volatile uint32_t PWR_HIB_DATA[16];
   volatile const uint32_t RESERVED2[48];
  volatile uint32_t WDT_CTL;
  volatile uint32_t WDT_CNT;
  volatile uint32_t WDT_MATCH;
   volatile const uint32_t RESERVED3[29];
        MCWDT_STRUCT_V1_Type MCWDT_STRUCT[4];
  volatile uint32_t CLK_DSI_SELECT[16];
  volatile uint32_t CLK_PATH_SELECT[16];
  volatile uint32_t CLK_ROOT_SELECT[16];
   volatile const uint32_t RESERVED4[80];
  volatile uint32_t CLK_SELECT;
  volatile uint32_t CLK_TIMER_CTL;
   volatile const uint32_t RESERVED5;
  volatile uint32_t CLK_ILO_CONFIG;
  volatile uint32_t CLK_IMO_CONFIG;
  volatile uint32_t CLK_OUTPUT_FAST;
  volatile uint32_t CLK_OUTPUT_SLOW;
  volatile uint32_t CLK_CAL_CNT1;
   volatile const uint32_t CLK_CAL_CNT2;
   volatile const uint32_t RESERVED6[2];
  volatile uint32_t CLK_ECO_CONFIG;
   volatile const uint32_t CLK_ECO_STATUS;
   volatile const uint32_t RESERVED7[2];
  volatile uint32_t CLK_PILO_CONFIG;
   volatile const uint32_t RESERVED8;
  volatile uint32_t CLK_MF_SELECT;
  volatile uint32_t CLK_MFO_CONFIG;
   volatile const uint32_t RESERVED9[13];
  volatile uint32_t CLK_FLL_CONFIG;
  volatile uint32_t CLK_FLL_CONFIG2;
  volatile uint32_t CLK_FLL_CONFIG3;
  volatile uint32_t CLK_FLL_CONFIG4;
  volatile uint32_t CLK_FLL_STATUS;
   volatile const uint32_t RESERVED10[27];
  volatile uint32_t CLK_PLL_CONFIG[15];
   volatile const uint32_t RESERVED11;
  volatile uint32_t CLK_PLL_STATUS[15];
   volatile const uint32_t RESERVED12[33];
  volatile uint32_t SRSS_INTR;
  volatile uint32_t SRSS_INTR_SET;
  volatile uint32_t SRSS_INTR_MASK;
   volatile const uint32_t SRSS_INTR_MASKED;
  volatile uint32_t SRSS_INTR_CFG;
   volatile const uint32_t RESERVED13[59];
  volatile uint32_t RES_CAUSE;
  volatile uint32_t RES_CAUSE2;
   volatile const uint32_t RESERVED14[7614];
  volatile uint32_t PWR_TRIM_REF_CTL;
  volatile uint32_t PWR_TRIM_BODOVP_CTL;
  volatile uint32_t CLK_TRIM_CCO_CTL;
  volatile uint32_t CLK_TRIM_CCO_CTL2;
   volatile const uint32_t RESERVED15[8];
  volatile uint32_t PWR_TRIM_WAKE_CTL;
   volatile const uint32_t RESERVED16[8183];
  volatile uint32_t PWR_TRIM_LVD_CTL;
   volatile const uint32_t RESERVED17;
  volatile uint32_t CLK_TRIM_ILO_CTL;
  volatile uint32_t PWR_TRIM_PWRSYS_CTL;
  volatile uint32_t CLK_TRIM_ECO_CTL;
  volatile uint32_t CLK_TRIM_PILO_CTL;
  volatile uint32_t CLK_TRIM_PILO_CTL2;
  volatile uint32_t CLK_TRIM_PILO_CTL3;
} SRSS_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED;
  volatile uint32_t RTC_RW;
  volatile uint32_t CAL_CTL;
   volatile const uint32_t STATUS;
  volatile uint32_t RTC_TIME;
  volatile uint32_t RTC_DATE;
  volatile uint32_t ALM1_TIME;
  volatile uint32_t ALM1_DATE;
  volatile uint32_t ALM2_TIME;
  volatile uint32_t ALM2_DATE;
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t OSCCNT;
   volatile const uint32_t TICKS;
  volatile uint32_t PMIC_CTL;
  volatile uint32_t RESET;
   volatile const uint32_t RESERVED1[1005];
  volatile uint32_t BREG[64];
   volatile const uint32_t RESERVED2[15232];
  volatile uint32_t TRIM;
} BACKUP_V1_Type;
typedef struct {
  volatile uint32_t CH_CTL;
   volatile const uint32_t CH_STATUS;
  volatile uint32_t CH_IDX;
  volatile uint32_t CH_CURR_PTR;
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
} DW_CH_STRUCT_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t STATUS;
   volatile const uint32_t PENDING;
   volatile const uint32_t RESERVED;
   volatile const uint32_t STATUS_INTR;
   volatile const uint32_t STATUS_INTR_MASKED;
   volatile const uint32_t RESERVED1[2];
   volatile const uint32_t ACT_DESCR_CTL;
   volatile const uint32_t ACT_DESCR_SRC;
   volatile const uint32_t ACT_DESCR_DST;
   volatile const uint32_t RESERVED2;
   volatile const uint32_t ACT_DESCR_X_CTL;
   volatile const uint32_t ACT_DESCR_Y_CTL;
   volatile const uint32_t ACT_DESCR_NEXT_PTR;
   volatile const uint32_t RESERVED3;
   volatile const uint32_t ACT_SRC;
   volatile const uint32_t ACT_DST;
   volatile const uint32_t RESERVED4[494];
        DW_CH_STRUCT_V1_Type CH_STRUCT[32];
} DW_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED[3];
  volatile uint32_t CMD;
   volatile const uint32_t RESERVED1[3];
  volatile uint32_t SEQ_DEFAULT;
   volatile const uint32_t RESERVED2[7];
  volatile uint32_t SEQ_READ_CTL_0;
  volatile uint32_t SEQ_READ_CTL_1;
  volatile uint32_t SEQ_READ_CTL_2;
  volatile uint32_t SEQ_READ_CTL_3;
  volatile uint32_t SEQ_READ_CTL_4;
  volatile uint32_t SEQ_READ_CTL_5;
   volatile const uint32_t RESERVED3[2];
  volatile uint32_t SEQ_PROGRAM_CTL_0;
  volatile uint32_t SEQ_PROGRAM_CTL_1;
  volatile uint32_t SEQ_PROGRAM_CTL_2;
  volatile uint32_t SEQ_PROGRAM_CTL_3;
  volatile uint32_t SEQ_PROGRAM_CTL_4;
  volatile uint32_t SEQ_PROGRAM_CTL_5;
} EFUSE_V1_Type;
typedef struct {
    uint8_t CM0_DISABLE;
    uint8_t CM4_DISABLE;
    uint8_t SYS_DISABLE;
    uint8_t SYS_AP_MPU_ENABLE;
    uint8_t SFLASH_ALLOWED[2];
    uint8_t MMIO_ALLOWED[2];
} cy_stc_dead_access_restrict0_t;
typedef struct {
    uint8_t FLASH_ALLOWED[3];
    uint8_t SRAM_ALLOWED[3];
    uint8_t UNUSED;
    uint8_t DIRECT_EXECUTE_DISABLE;
} cy_stc_dead_access_restrict1_t;
typedef struct {
    uint8_t CM0_DISABLE;
    uint8_t CM4_DISABLE;
    uint8_t SYS_DISABLE;
    uint8_t SYS_AP_MPU_ENABLE;
    uint8_t SFLASH_ALLOWED[2];
    uint8_t MMIO_ALLOWED[2];
} cy_stc_secure_access_restrict0_t;
typedef struct {
    uint8_t FLASH_ALLOWED[3];
    uint8_t SRAM_ALLOWED[3];
    uint8_t SMIF_XIP_ALLOWED;
    uint8_t DIRECT_EXECUTE_DISABLE;
} cy_stc_secure_access_restrict1_t;
typedef struct {
    uint8_t NORMAL;
    uint8_t SECURE_WITH_DEBUG;
    uint8_t SECURE;
    uint8_t RMA;
    uint8_t RESERVED[4];
} cy_stc_lifecycle_stage_t;
typedef struct {
    uint8_t CUSTOMER_USE[8];
} cy_stc_customer_data_t;
typedef struct {
    uint8_t RESERVED[312];
    cy_stc_dead_access_restrict0_t DEAD_ACCESS_RESTRICT0;
    cy_stc_dead_access_restrict1_t DEAD_ACCESS_RESTRICT1;
    cy_stc_secure_access_restrict0_t SECURE_ACCESS_RESTRICT0;
    cy_stc_secure_access_restrict1_t SECURE_ACCESS_RESTRICT1;
    cy_stc_lifecycle_stage_t LIFECYCLE_STAGE;
    uint8_t RESERVED1[160];
    cy_stc_customer_data_t CUSTOMER_DATA[64];
} cy_stc_efuse_data_t;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED;
  volatile uint32_t CNT;
   volatile const uint32_t RESERVED1;
} PROFILE_CNT_STRUCT_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t STATUS;
   volatile const uint32_t RESERVED[2];
  volatile uint32_t CMD;
   volatile const uint32_t RESERVED1[491];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED2[12];
        PROFILE_CNT_STRUCT_V1_Type CNT_STRUCT[16];
} PROFILE_V1_Type;
typedef struct {
  volatile uint32_t PORT_SEL0;
  volatile uint32_t PORT_SEL1;
   volatile const uint32_t RESERVED[2];
} HSIOM_PRT_V1_Type;
typedef struct {
        HSIOM_PRT_V1_Type PRT[128];
   volatile const uint32_t RESERVED[1536];
  volatile uint32_t AMUX_SPLIT_CTL[64];
} HSIOM_V1_Type;
typedef struct {
  volatile uint32_t OUT;
  volatile uint32_t OUT_CLR;
  volatile uint32_t OUT_SET;
  volatile uint32_t OUT_INV;
   volatile const uint32_t IN;
  volatile uint32_t INTR;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_CFG;
  volatile uint32_t CFG;
  volatile uint32_t CFG_IN;
  volatile uint32_t CFG_OUT;
  volatile uint32_t CFG_SIO;
   volatile const uint32_t RESERVED;
  volatile uint32_t CFG_IN_GPIO5V;
   volatile const uint32_t RESERVED1[16];
} GPIO_PRT_V1_Type;
typedef struct {
        GPIO_PRT_V1_Type PRT[128];
   volatile const uint32_t INTR_CAUSE0;
   volatile const uint32_t INTR_CAUSE1;
   volatile const uint32_t INTR_CAUSE2;
   volatile const uint32_t INTR_CAUSE3;
   volatile const uint32_t VDD_ACTIVE;
  volatile uint32_t VDD_INTR;
  volatile uint32_t VDD_INTR_MASK;
   volatile const uint32_t VDD_INTR_MASKED;
  volatile uint32_t VDD_INTR_SET;
} GPIO_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED[3];
  volatile uint32_t SYNC_CTL;
   volatile const uint32_t RESERVED1[3];
  volatile uint32_t LUT_SEL[8];
  volatile uint32_t LUT_CTL[8];
   volatile const uint32_t RESERVED2[24];
  volatile uint32_t DU_SEL;
  volatile uint32_t DU_CTL;
   volatile const uint32_t RESERVED3[10];
  volatile uint32_t DATA;
   volatile const uint32_t RESERVED4[3];
} SMARTIO_PRT_V1_Type;
typedef struct {
        SMARTIO_PRT_V1_Type PRT[128];
} SMARTIO_V1_Type;
typedef struct {
  volatile uint32_t A[64];
  volatile uint32_t D[64];
  volatile uint32_t F[64];
  volatile uint32_t CTL_ST[64];
  volatile uint32_t ACTL_MSK[64];
   volatile const uint32_t MC[64];
   volatile const uint32_t RESERVED[128];
} UDB_WRKONE_V1_Type;
typedef struct {
  volatile uint32_t A0[64];
  volatile uint32_t A1[64];
  volatile uint32_t D0[64];
  volatile uint32_t D1[64];
  volatile uint32_t F0[64];
  volatile uint32_t F1[64];
   volatile const uint32_t ST[64];
  volatile uint32_t CTL[64];
  volatile uint32_t MSK[64];
  volatile uint32_t ACTL[64];
   volatile const uint32_t MC[64];
   volatile const uint32_t RESERVED[320];
} UDB_WRKMULT_V1_Type;
typedef struct {
  volatile uint32_t PLD_IT[12];
  volatile uint32_t PLD_ORT0;
  volatile uint32_t PLD_ORT1;
  volatile uint32_t PLD_CFG0;
  volatile uint32_t PLD_CFG1;
  volatile uint32_t DPATH_CFG0;
  volatile uint32_t DPATH_CFG1;
  volatile uint32_t DPATH_CFG2;
  volatile uint32_t DPATH_CFG3;
  volatile uint32_t DPATH_CFG4;
  volatile uint32_t SC_CFG0;
  volatile uint32_t SC_CFG1;
  volatile uint32_t RC_CFG0;
  volatile uint32_t RC_CFG1;
  volatile uint32_t DPATH_OPC[4];
   volatile const uint32_t RESERVED[3];
} UDB_UDBPAIR_UDBSNG_V1_Type;
typedef struct {
  volatile uint32_t TOP_V_BOT;
  volatile uint32_t LVO1_V_2;
  volatile uint32_t RVO1_V_2;
  volatile uint32_t TUI_CFG0;
  volatile uint32_t TUI_CFG1;
  volatile uint32_t TUI_CFG2;
  volatile uint32_t TUI_CFG3;
  volatile uint32_t TUI_CFG4;
  volatile uint32_t TUI_CFG5;
  volatile uint32_t BUI_CFG0;
  volatile uint32_t BUI_CFG1;
  volatile uint32_t BUI_CFG2;
  volatile uint32_t BUI_CFG3;
  volatile uint32_t BUI_CFG4;
  volatile uint32_t BUI_CFG5;
  volatile uint32_t RVO_CFG0;
  volatile uint32_t RVO_CFG1;
  volatile uint32_t RVO_CFG2;
  volatile uint32_t RVO_CFG3;
  volatile uint32_t LVO_CFG0;
  volatile uint32_t LVO_CFG1;
  volatile uint32_t RHO_CFG0;
  volatile uint32_t RHO_CFG1;
  volatile uint32_t RHO_CFG2;
  volatile uint32_t LHO_CFG0;
  volatile uint32_t LHO_CFG1;
  volatile uint32_t LHO_CFG2;
  volatile uint32_t LHO_CFG3;
  volatile uint32_t LHO_CFG4;
  volatile uint32_t LHO_CFG5;
  volatile uint32_t LHO_CFG6;
  volatile uint32_t LHO_CFG7;
  volatile uint32_t LHO_CFG8;
  volatile uint32_t LHO_CFG9;
  volatile uint32_t LHO_CFG10;
  volatile uint32_t LHO_CFG11;
   volatile const uint32_t RESERVED[28];
} UDB_UDBPAIR_ROUTE_V1_Type;
typedef struct {
        UDB_UDBPAIR_UDBSNG_V1_Type UDBSNG[2];
        UDB_UDBPAIR_ROUTE_V1_Type ROUTE;
} UDB_UDBPAIR_V1_Type;
typedef struct {
  volatile uint32_t LVO1_V_2;
  volatile uint32_t RVO1_V_2;
  volatile uint32_t DOP_CFG0;
  volatile uint32_t DOP_CFG1;
  volatile uint32_t DOP_CFG2;
  volatile uint32_t DOP_CFG3;
  volatile uint32_t DOT_CFG0;
  volatile uint32_t DOT_CFG1;
  volatile uint32_t DOT_CFG2;
  volatile uint32_t DOT_CFG3;
  volatile uint32_t RVO_CFG0;
  volatile uint32_t RVO_CFG1;
  volatile uint32_t RVO_CFG2;
  volatile uint32_t RVO_CFG3;
  volatile uint32_t LVO_CFG0;
  volatile uint32_t LVO_CFG1;
  volatile uint32_t RHO_CFG0;
  volatile uint32_t RHO_CFG1;
  volatile uint32_t RHO_CFG2;
  volatile uint32_t LHO_CFG0;
  volatile uint32_t LHO_CFG1;
  volatile uint32_t LHO_CFG2;
  volatile uint32_t LHO_CFG3;
  volatile uint32_t LHO_CFG4;
  volatile uint32_t LHO_CFG5;
  volatile uint32_t LHO_CFG6;
  volatile uint32_t LHO_CFG7;
  volatile uint32_t LHO_CFG8;
  volatile uint32_t LHO_CFG9;
  volatile uint32_t LHO_CFG10;
  volatile uint32_t LHO_CFG11;
   volatile const uint32_t RESERVED;
} UDB_DSI_V1_Type;
typedef struct {
  volatile uint32_t CFG0;
  volatile uint32_t CFG1;
  volatile uint32_t CFG2;
  volatile uint32_t CFG3;
  volatile uint32_t CFG4;
  volatile uint32_t CFG5;
  volatile uint32_t CFG6;
  volatile uint32_t CFG7;
  volatile uint32_t CFG8;
  volatile uint32_t CFG9;
  volatile uint32_t CFG10;
  volatile uint32_t CFG11;
  volatile uint32_t CFG12;
  volatile uint32_t CFG13;
  volatile uint32_t CFG14;
   volatile const uint32_t RESERVED;
} UDB_PA_V1_Type;
typedef struct {
  volatile uint32_t MDCLK_EN;
  volatile uint32_t MBCLK_EN;
  volatile uint32_t BOTSEL_L;
  volatile uint32_t BOTSEL_U;
  volatile uint32_t QCLK_EN[16];
   volatile const uint32_t RESERVED[12];
} UDB_BCTL_V1_Type;
typedef struct {
  volatile uint32_t BANK_CTL;
  volatile uint32_t INT_CLK_CTL;
  volatile uint32_t INT_CFG;
  volatile uint32_t TR_CLK_CTL;
  volatile uint32_t TR_CFG;
  volatile uint32_t PRIVATE;
   volatile const uint32_t RESERVED[2];
} UDB_UDBIF_V1_Type;
typedef struct {
        UDB_WRKONE_V1_Type WRKONE;
   volatile const uint32_t RESERVED[512];
        UDB_WRKMULT_V1_Type WRKMULT;
        UDB_UDBPAIR_V1_Type UDBPAIR[32];
        UDB_DSI_V1_Type DSI[32];
        UDB_PA_V1_Type PA[32];
        UDB_BCTL_V1_Type BCTL;
   volatile const uint32_t RESERVED1[32];
        UDB_UDBIF_V1_Type UDBIF;
} UDB_V1_Type;
typedef struct {
  volatile uint32_t CONFIG;
   volatile const uint32_t STATUS;
   volatile const uint32_t RESERVED[2];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED1[8];
  volatile uint32_t CMP0_CTRL;
   volatile const uint32_t RESERVED2[3];
  volatile uint32_t CMP0_SW;
  volatile uint32_t CMP0_SW_CLEAR;
   volatile const uint32_t RESERVED3[10];
  volatile uint32_t CMP1_CTRL;
   volatile const uint32_t RESERVED4[3];
  volatile uint32_t CMP1_SW;
  volatile uint32_t CMP1_SW_CLEAR;
} LPCOMP_V1_Type;
typedef struct {
  volatile uint32_t CONFIG;
  volatile uint32_t SPARE;
   volatile const uint32_t RESERVED[30];
   volatile const uint32_t STATUS;
   volatile const uint32_t STAT_SEQ;
   volatile const uint32_t STAT_CNTS;
   volatile const uint32_t STAT_HCNT;
   volatile const uint32_t RESERVED1[16];
   volatile const uint32_t RESULT_VAL1;
   volatile const uint32_t RESULT_VAL2;
   volatile const uint32_t RESERVED2[2];
   volatile const uint32_t ADC_RES;
   volatile const uint32_t RESERVED3[3];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED4[32];
  volatile uint32_t HSCMP;
  volatile uint32_t AMBUF;
  volatile uint32_t REFGEN;
  volatile uint32_t CSDCMP;
   volatile const uint32_t RESERVED5[24];
  volatile uint32_t SW_RES;
   volatile const uint32_t RESERVED6[3];
  volatile uint32_t SENSE_PERIOD;
  volatile uint32_t SENSE_DUTY;
   volatile const uint32_t RESERVED7[30];
  volatile uint32_t SW_HS_P_SEL;
  volatile uint32_t SW_HS_N_SEL;
  volatile uint32_t SW_SHIELD_SEL;
   volatile const uint32_t RESERVED8;
  volatile uint32_t SW_AMUXBUF_SEL;
  volatile uint32_t SW_BYP_SEL;
   volatile const uint32_t RESERVED9[2];
  volatile uint32_t SW_CMP_P_SEL;
  volatile uint32_t SW_CMP_N_SEL;
  volatile uint32_t SW_REFGEN_SEL;
   volatile const uint32_t RESERVED10;
  volatile uint32_t SW_FW_MOD_SEL;
  volatile uint32_t SW_FW_TANK_SEL;
   volatile const uint32_t RESERVED11[2];
  volatile uint32_t SW_DSI_SEL;
   volatile const uint32_t RESERVED12[3];
  volatile uint32_t IO_SEL;
   volatile const uint32_t RESERVED13[11];
  volatile uint32_t SEQ_TIME;
   volatile const uint32_t RESERVED14[3];
  volatile uint32_t SEQ_INIT_CNT;
  volatile uint32_t SEQ_NORM_CNT;
   volatile const uint32_t RESERVED15[2];
  volatile uint32_t ADC_CTL;
   volatile const uint32_t RESERVED16[7];
  volatile uint32_t SEQ_START;
   volatile const uint32_t RESERVED17[47];
  volatile uint32_t IDACA;
   volatile const uint32_t RESERVED18[63];
  volatile uint32_t IDACB;
} CSD_V1_Type;
typedef struct {
  volatile uint32_t CTRL;
   volatile const uint32_t STATUS;
  volatile uint32_t COUNTER;
  volatile uint32_t CC;
  volatile uint32_t CC_BUFF;
  volatile uint32_t PERIOD;
  volatile uint32_t PERIOD_BUFF;
   volatile const uint32_t RESERVED;
  volatile uint32_t TR_CTRL0;
  volatile uint32_t TR_CTRL1;
  volatile uint32_t TR_CTRL2;
   volatile const uint32_t RESERVED1;
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
} TCPWM_CNT_V1_Type;
typedef struct {
  volatile uint32_t CTRL;
  volatile uint32_t CTRL_CLR;
  volatile uint32_t CTRL_SET;
  volatile uint32_t CMD_CAPTURE;
  volatile uint32_t CMD_RELOAD;
  volatile uint32_t CMD_STOP;
  volatile uint32_t CMD_START;
   volatile const uint32_t INTR_CAUSE;
   volatile const uint32_t RESERVED[56];
        TCPWM_CNT_V1_Type CNT[32];
} TCPWM_V1_Type;
typedef struct {
   volatile const uint32_t ID;
  volatile uint32_t DIVIDER;
  volatile uint32_t CONTROL;
   volatile const uint32_t RESERVED[61];
  volatile uint32_t DATA0[8];
   volatile const uint32_t RESERVED1[56];
  volatile uint32_t DATA1[8];
   volatile const uint32_t RESERVED2[56];
  volatile uint32_t DATA2[8];
   volatile const uint32_t RESERVED3[56];
  volatile uint32_t DATA3[8];
} LCD_V1_Type;
typedef struct {
  volatile uint32_t CTRL;
   volatile const uint32_t RESERVED[3];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
  volatile uint32_t RADIO_REG1_ADDR;
  volatile uint32_t RADIO_REG2_ADDR;
  volatile uint32_t RADIO_REG3_ADDR;
  volatile uint32_t RADIO_REG4_ADDR;
  volatile uint32_t RADIO_REG5_ADDR;
   volatile const uint32_t RESERVED1[3];
  volatile uint32_t CPU_WRITE_REG;
  volatile uint32_t CPU_READ_REG;
   volatile const uint32_t RESERVED2[46];
} BLE_RCB_RCBLL_V1_Type;
typedef struct {
  volatile uint32_t CTRL;
   volatile const uint32_t STATUS;
   volatile const uint32_t RESERVED[2];
  volatile uint32_t TX_CTRL;
  volatile uint32_t TX_FIFO_CTRL;
   volatile const uint32_t TX_FIFO_STATUS;
   volatile uint32_t TX_FIFO_WR;
  volatile uint32_t RX_CTRL;
  volatile uint32_t RX_FIFO_CTRL;
   volatile const uint32_t RX_FIFO_STATUS;
   volatile const uint32_t RX_FIFO_RD;
   volatile const uint32_t RX_FIFO_RD_SILENT;
   volatile const uint32_t RESERVED1[3];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED2[44];
        BLE_RCB_RCBLL_V1_Type RCBLL;
} BLE_RCB_V1_Type;
typedef struct {
   volatile uint32_t COMMAND_REGISTER;
   volatile const uint32_t RESERVED;
  volatile uint32_t EVENT_INTR;
   volatile const uint32_t RESERVED1;
  volatile uint32_t EVENT_ENABLE;
   volatile const uint32_t RESERVED2;
  volatile uint32_t ADV_PARAMS;
  volatile uint32_t ADV_INTERVAL_TIMEOUT;
  volatile uint32_t ADV_INTR;
   volatile const uint32_t ADV_NEXT_INSTANT;
  volatile uint32_t SCAN_INTERVAL;
  volatile uint32_t SCAN_WINDOW;
  volatile uint32_t SCAN_PARAM;
   volatile const uint32_t RESERVED3;
  volatile uint32_t SCAN_INTR;
   volatile const uint32_t SCAN_NEXT_INSTANT;
  volatile uint32_t INIT_INTERVAL;
  volatile uint32_t INIT_WINDOW;
  volatile uint32_t INIT_PARAM;
   volatile const uint32_t RESERVED4;
  volatile uint32_t INIT_INTR;
   volatile const uint32_t INIT_NEXT_INSTANT;
  volatile uint32_t DEVICE_RAND_ADDR_L;
  volatile uint32_t DEVICE_RAND_ADDR_M;
  volatile uint32_t DEVICE_RAND_ADDR_H;
   volatile const uint32_t RESERVED5;
  volatile uint32_t PEER_ADDR_L;
  volatile uint32_t PEER_ADDR_M;
  volatile uint32_t PEER_ADDR_H;
   volatile const uint32_t RESERVED6;
  volatile uint32_t WL_ADDR_TYPE;
  volatile uint32_t WL_ENABLE;
  volatile uint32_t TRANSMIT_WINDOW_OFFSET;
  volatile uint32_t TRANSMIT_WINDOW_SIZE;
  volatile uint32_t DATA_CHANNELS_L0;
  volatile uint32_t DATA_CHANNELS_M0;
  volatile uint32_t DATA_CHANNELS_H0;
   volatile const uint32_t RESERVED7;
  volatile uint32_t DATA_CHANNELS_L1;
  volatile uint32_t DATA_CHANNELS_M1;
  volatile uint32_t DATA_CHANNELS_H1;
   volatile const uint32_t RESERVED8;
  volatile uint32_t CONN_INTR;
   volatile const uint32_t CONN_STATUS;
  volatile uint32_t CONN_INDEX;
   volatile const uint32_t RESERVED9;
  volatile uint32_t WAKEUP_CONFIG;
   volatile const uint32_t RESERVED10;
  volatile uint32_t WAKEUP_CONTROL;
  volatile uint32_t CLOCK_CONFIG;
   volatile const uint32_t TIM_COUNTER_L;
  volatile uint32_t WAKEUP_CONFIG_EXTD;
   volatile const uint32_t RESERVED11[2];
  volatile uint32_t POC_REG__TIM_CONTROL;
   volatile const uint32_t RESERVED12;
  volatile uint32_t ADV_TX_DATA_FIFO;
   volatile const uint32_t RESERVED13;
  volatile uint32_t ADV_SCN_RSP_TX_FIFO;
   volatile const uint32_t RESERVED14[3];
   volatile const uint32_t INIT_SCN_ADV_RX_FIFO;
   volatile const uint32_t RESERVED15;
  volatile uint32_t CONN_INTERVAL;
  volatile uint32_t SUP_TIMEOUT;
  volatile uint32_t SLAVE_LATENCY;
  volatile uint32_t CE_LENGTH;
  volatile uint32_t PDU_ACCESS_ADDR_L_REGISTER;
  volatile uint32_t PDU_ACCESS_ADDR_H_REGISTER;
  volatile uint32_t CONN_CE_INSTANT;
  volatile uint32_t CE_CNFG_STS_REGISTER;
   volatile const uint32_t NEXT_CE_INSTANT;
   volatile const uint32_t CONN_CE_COUNTER;
  volatile uint32_t DATA_LIST_SENT_UPDATE__STATUS;
  volatile uint32_t DATA_LIST_ACK_UPDATE__STATUS;
  volatile uint32_t CE_CNFG_STS_REGISTER_EXT;
  volatile uint32_t CONN_EXT_INTR;
  volatile uint32_t CONN_EXT_INTR_MASK;
   volatile const uint32_t RESERVED16;
  volatile uint32_t DATA_MEM_DESCRIPTOR[5];
   volatile const uint32_t RESERVED17[3];
  volatile uint32_t WINDOW_WIDEN_INTVL;
  volatile uint32_t WINDOW_WIDEN_WINOFF;
   volatile const uint32_t RESERVED18[2];
  volatile uint32_t LE_RF_TEST_MODE;
   volatile const uint32_t DTM_RX_PKT_COUNT;
  volatile uint32_t LE_RF_TEST_MODE_EXT;
   volatile const uint32_t RESERVED19[3];
   volatile const uint32_t TXRX_HOP;
   volatile const uint32_t RESERVED20;
  volatile uint32_t TX_RX_ON_DELAY;
   volatile const uint32_t RESERVED21[5];
  volatile uint32_t ADV_ACCADDR_L;
  volatile uint32_t ADV_ACCADDR_H;
  volatile uint32_t ADV_CH_TX_POWER_LVL_LS;
  volatile uint32_t ADV_CH_TX_POWER_LVL_MS;
  volatile uint32_t CONN_CH_TX_POWER_LVL_LS;
  volatile uint32_t CONN_CH_TX_POWER_LVL_MS;
  volatile uint32_t DEV_PUB_ADDR_L;
  volatile uint32_t DEV_PUB_ADDR_M;
  volatile uint32_t DEV_PUB_ADDR_H;
   volatile const uint32_t RESERVED22;
  volatile uint32_t OFFSET_TO_FIRST_INSTANT;
  volatile uint32_t ADV_CONFIG;
  volatile uint32_t SCAN_CONFIG;
  volatile uint32_t INIT_CONFIG;
  volatile uint32_t CONN_CONFIG;
   volatile const uint32_t RESERVED23;
  volatile uint32_t CONN_PARAM1;
  volatile uint32_t CONN_PARAM2;
  volatile uint32_t CONN_INTR_MASK;
  volatile uint32_t SLAVE_TIMING_CONTROL;
  volatile uint32_t RECEIVE_TRIG_CTRL;
   volatile const uint32_t RESERVED24;
   volatile const uint32_t LL_DBG_1;
   volatile const uint32_t LL_DBG_2;
   volatile const uint32_t LL_DBG_3;
   volatile const uint32_t LL_DBG_4;
   volatile const uint32_t LL_DBG_5;
   volatile const uint32_t LL_DBG_6;
   volatile const uint32_t LL_DBG_7;
   volatile const uint32_t LL_DBG_8;
   volatile const uint32_t LL_DBG_9;
   volatile const uint32_t LL_DBG_10;
   volatile const uint32_t RESERVED25[2];
  volatile uint32_t PEER_ADDR_INIT_L;
  volatile uint32_t PEER_ADDR_INIT_M;
  volatile uint32_t PEER_ADDR_INIT_H;
  volatile uint32_t PEER_SEC_ADDR_ADV_L;
  volatile uint32_t PEER_SEC_ADDR_ADV_M;
  volatile uint32_t PEER_SEC_ADDR_ADV_H;
  volatile uint32_t INIT_WINDOW_TIMER_CTRL;
  volatile uint32_t CONN_CONFIG_EXT;
   volatile const uint32_t RESERVED26[2];
  volatile uint32_t DPLL_CONFIG;
   volatile const uint32_t RESERVED27;
  volatile uint32_t INIT_NI_VAL;
   volatile const uint32_t INIT_WINDOW_OFFSET;
   volatile const uint32_t INIT_WINDOW_NI_ANCHOR_PT;
   volatile const uint32_t RESERVED28[78];
  volatile uint32_t CONN_UPDATE_NEW_INTERVAL;
  volatile uint32_t CONN_UPDATE_NEW_LATENCY;
  volatile uint32_t CONN_UPDATE_NEW_SUP_TO;
  volatile uint32_t CONN_UPDATE_NEW_SL_INTERVAL;
   volatile const uint32_t RESERVED29[3];
  volatile uint32_t CONN_REQ_WORD0;
  volatile uint32_t CONN_REQ_WORD1;
  volatile uint32_t CONN_REQ_WORD2;
  volatile uint32_t CONN_REQ_WORD3;
  volatile uint32_t CONN_REQ_WORD4;
  volatile uint32_t CONN_REQ_WORD5;
  volatile uint32_t CONN_REQ_WORD6;
  volatile uint32_t CONN_REQ_WORD7;
  volatile uint32_t CONN_REQ_WORD8;
  volatile uint32_t CONN_REQ_WORD9;
  volatile uint32_t CONN_REQ_WORD10;
  volatile uint32_t CONN_REQ_WORD11;
   volatile const uint32_t RESERVED30[389];
  volatile uint32_t PDU_RESP_TIMER;
   volatile const uint32_t NEXT_RESP_TIMER_EXP;
   volatile const uint32_t NEXT_SUP_TO;
  volatile uint32_t LLH_FEATURE_CONFIG;
  volatile uint32_t WIN_MIN_STEP_SIZE;
  volatile uint32_t SLV_WIN_ADJ;
  volatile uint32_t SL_CONN_INTERVAL;
  volatile uint32_t LE_PING_TIMER_ADDR;
  volatile uint32_t LE_PING_TIMER_OFFSET;
   volatile const uint32_t LE_PING_TIMER_NEXT_EXP;
   volatile const uint32_t LE_PING_TIMER_WRAP_COUNT;
   volatile const uint32_t RESERVED31[244];
  volatile uint32_t TX_EN_EXT_DELAY;
  volatile uint32_t TX_RX_SYNTH_DELAY;
  volatile uint32_t EXT_PA_LNA_DLY_CNFG;
   volatile const uint32_t RESERVED32;
  volatile uint32_t LL_CONFIG;
   volatile const uint32_t RESERVED33[59];
  volatile uint32_t LL_CONTROL;
  volatile uint32_t DEV_PA_ADDR_L;
  volatile uint32_t DEV_PA_ADDR_M;
  volatile uint32_t DEV_PA_ADDR_H;
  volatile uint32_t RSLV_LIST_ENABLE[16];
   volatile const uint32_t RESERVED34[20];
  volatile uint32_t WL_CONNECTION_STATUS;
   volatile const uint32_t RESERVED35[535];
  volatile uint32_t CONN_RXMEM_BASE_ADDR_DLE;
   volatile const uint32_t RESERVED36[1023];
  volatile uint32_t CONN_TXMEM_BASE_ADDR_DLE;
   volatile const uint32_t RESERVED37[16383];
  volatile uint32_t CONN_1_PARAM_MEM_BASE_ADDR;
   volatile const uint32_t RESERVED38[31];
  volatile uint32_t CONN_2_PARAM_MEM_BASE_ADDR;
   volatile const uint32_t RESERVED39[31];
  volatile uint32_t CONN_3_PARAM_MEM_BASE_ADDR;
   volatile const uint32_t RESERVED40[31];
  volatile uint32_t CONN_4_PARAM_MEM_BASE_ADDR;
   volatile const uint32_t RESERVED41[1439];
  volatile uint32_t NI_TIMER;
  volatile uint32_t US_OFFSET;
  volatile uint32_t NEXT_CONN;
  volatile uint32_t NI_ABORT;
   volatile const uint32_t RESERVED42[4];
   volatile const uint32_t CONN_NI_STATUS;
   volatile const uint32_t NEXT_SUP_TO_STATUS;
   volatile const uint32_t MMMS_CONN_STATUS;
   volatile const uint32_t BT_SLOT_CAPT_STATUS;
   volatile const uint32_t US_CAPT_STATUS;
   volatile const uint32_t US_OFFSET_STATUS;
   volatile const uint32_t ACCU_WINDOW_WIDEN_STATUS;
   volatile const uint32_t EARLY_INTR_STATUS;
  volatile uint32_t MMMS_CONFIG;
   volatile const uint32_t US_COUNTER;
  volatile uint32_t US_CAPT_PREV;
   volatile const uint32_t EARLY_INTR_NI;
   volatile const uint32_t RESERVED43[12];
   volatile const uint32_t MMMS_MASTER_CREATE_BT_CAPT;
   volatile const uint32_t MMMS_SLAVE_CREATE_BT_CAPT;
   volatile const uint32_t MMMS_SLAVE_CREATE_US_CAPT;
   volatile const uint32_t RESERVED44[29];
  volatile uint32_t MMMS_DATA_MEM_DESCRIPTOR[16];
   volatile const uint32_t RESERVED45[48];
  volatile uint32_t CONN_1_DATA_LIST_SENT;
  volatile uint32_t CONN_1_DATA_LIST_ACK;
  volatile uint32_t CONN_1_CE_DATA_LIST_CFG;
   volatile const uint32_t RESERVED46;
  volatile uint32_t CONN_2_DATA_LIST_SENT;
  volatile uint32_t CONN_2_DATA_LIST_ACK;
  volatile uint32_t CONN_2_CE_DATA_LIST_CFG;
   volatile const uint32_t RESERVED47;
  volatile uint32_t CONN_3_DATA_LIST_SENT;
  volatile uint32_t CONN_3_DATA_LIST_ACK;
  volatile uint32_t CONN_3_CE_DATA_LIST_CFG;
   volatile const uint32_t RESERVED48;
  volatile uint32_t CONN_4_DATA_LIST_SENT;
  volatile uint32_t CONN_4_DATA_LIST_ACK;
  volatile uint32_t CONN_4_CE_DATA_LIST_CFG;
   volatile const uint32_t RESERVED49[113];
  volatile uint32_t MMMS_ADVCH_NI_ENABLE;
  volatile uint32_t MMMS_ADVCH_NI_VALID;
  volatile uint32_t MMMS_ADVCH_NI_ABORT;
   volatile const uint32_t RESERVED50;
  volatile uint32_t CONN_PARAM_NEXT_SUP_TO;
  volatile uint32_t CONN_PARAM_ACC_WIN_WIDEN;
   volatile const uint32_t RESERVED51[2];
  volatile uint32_t HW_LOAD_OFFSET;
   volatile const uint32_t ADV_RAND;
   volatile const uint32_t MMMS_RX_PKT_CNTR;
   volatile const uint32_t RESERVED52;
   volatile const uint32_t CONN_RX_PKT_CNTR[8];
   volatile const uint32_t RESERVED53[236];
  volatile uint32_t WHITELIST_BASE_ADDR;
   volatile const uint32_t RESERVED54[47];
  volatile uint32_t RSLV_LIST_PEER_IDNTT_BASE_ADDR;
   volatile const uint32_t RESERVED55[47];
  volatile uint32_t RSLV_LIST_PEER_RPA_BASE_ADDR;
   volatile const uint32_t RESERVED56[47];
  volatile uint32_t RSLV_LIST_RCVD_INIT_RPA_BASE_ADDR;
   volatile const uint32_t RESERVED57[47];
  volatile uint32_t RSLV_LIST_TX_INIT_RPA_BASE_ADDR;
   volatile const uint32_t RESERVED58[9535];
} BLE_BLELL_V1_Type;
typedef struct {
   volatile const uint32_t RESERVED[24];
  volatile uint32_t DDFT_CONFIG;
  volatile uint32_t XTAL_CLK_DIV_CONFIG;
  volatile uint32_t INTR_STAT;
  volatile uint32_t INTR_MASK;
  volatile uint32_t LL_CLK_EN;
  volatile uint32_t LF_CLK_CTRL;
  volatile uint32_t EXT_PA_LNA_CTRL;
   volatile const uint32_t RESERVED1;
   volatile const uint32_t LL_PKT_RSSI_CH_ENERGY;
   volatile const uint32_t BT_CLOCK_CAPT;
   volatile const uint32_t RESERVED2[6];
  volatile uint32_t MT_CFG;
  volatile uint32_t MT_DELAY_CFG;
  volatile uint32_t MT_DELAY_CFG2;
  volatile uint32_t MT_DELAY_CFG3;
  volatile uint32_t MT_VIO_CTRL;
   volatile const uint32_t MT_STATUS;
   volatile const uint32_t PWR_CTRL_SM_ST;
   volatile const uint32_t RESERVED3;
  volatile uint32_t HVLDO_CTRL;
  volatile uint32_t MISC_EN_CTRL;
   volatile const uint32_t RESERVED4[2];
  volatile uint32_t EFUSE_CONFIG;
  volatile uint32_t EFUSE_TIM_CTRL1;
  volatile uint32_t EFUSE_TIM_CTRL2;
  volatile uint32_t EFUSE_TIM_CTRL3;
   volatile const uint32_t EFUSE_RDATA_L;
   volatile const uint32_t EFUSE_RDATA_H;
  volatile uint32_t EFUSE_WDATA_L;
  volatile uint32_t EFUSE_WDATA_H;
  volatile uint32_t DIV_BY_625_CFG;
   volatile const uint32_t DIV_BY_625_STS;
   volatile const uint32_t RESERVED5[2];
  volatile uint32_t PACKET_COUNTER0;
  volatile uint32_t PACKET_COUNTER2;
  volatile uint32_t IV_MASTER0;
  volatile uint32_t IV_SLAVE0;
   volatile uint32_t ENC_KEY[4];
  volatile uint32_t MIC_IN0;
   volatile const uint32_t MIC_OUT0;
  volatile uint32_t ENC_PARAMS;
  volatile uint32_t ENC_CONFIG;
  volatile uint32_t ENC_INTR_EN;
  volatile uint32_t ENC_INTR;
   volatile const uint32_t RESERVED6[2];
  volatile uint32_t B1_DATA_REG[4];
  volatile uint32_t ENC_MEM_BASE_ADDR;
   volatile const uint32_t RESERVED7[875];
  volatile uint32_t TRIM_LDO_0;
  volatile uint32_t TRIM_LDO_1;
  volatile uint32_t TRIM_LDO_2;
  volatile uint32_t TRIM_LDO_3;
  volatile uint32_t TRIM_MXD[4];
   volatile const uint32_t RESERVED8[4];
  volatile uint32_t TRIM_LDO_4;
  volatile uint32_t TRIM_LDO_5;
   volatile const uint32_t RESERVED9[50];
} BLE_BLESS_V1_Type;
typedef struct {
        BLE_RCB_V1_Type RCB;
   volatile const uint32_t RESERVED[896];
        BLE_BLELL_V1_Type BLELL;
        BLE_BLESS_V1_Type BLESS;
} BLE_V1_Type;
typedef struct {
  volatile uint32_t EP0_DR[8];
  volatile uint32_t CR0;
  volatile uint32_t CR1;
  volatile uint32_t SIE_EP_INT_EN;
  volatile uint32_t SIE_EP_INT_SR;
  volatile uint32_t SIE_EP1_CNT0;
  volatile uint32_t SIE_EP1_CNT1;
  volatile uint32_t SIE_EP1_CR0;
   volatile const uint32_t RESERVED;
  volatile uint32_t USBIO_CR0;
  volatile uint32_t USBIO_CR2;
  volatile uint32_t USBIO_CR1;
   volatile const uint32_t RESERVED1;
  volatile uint32_t DYN_RECONFIG;
   volatile const uint32_t RESERVED2[3];
   volatile const uint32_t SOF0;
   volatile const uint32_t SOF1;
   volatile const uint32_t RESERVED3[2];
  volatile uint32_t SIE_EP2_CNT0;
  volatile uint32_t SIE_EP2_CNT1;
  volatile uint32_t SIE_EP2_CR0;
   volatile const uint32_t RESERVED4;
   volatile const uint32_t OSCLK_DR0;
   volatile const uint32_t OSCLK_DR1;
   volatile const uint32_t RESERVED5[6];
  volatile uint32_t EP0_CR;
  volatile uint32_t EP0_CNT;
   volatile const uint32_t RESERVED6[2];
  volatile uint32_t SIE_EP3_CNT0;
  volatile uint32_t SIE_EP3_CNT1;
  volatile uint32_t SIE_EP3_CR0;
   volatile const uint32_t RESERVED7[13];
  volatile uint32_t SIE_EP4_CNT0;
  volatile uint32_t SIE_EP4_CNT1;
  volatile uint32_t SIE_EP4_CR0;
   volatile const uint32_t RESERVED8[13];
  volatile uint32_t SIE_EP5_CNT0;
  volatile uint32_t SIE_EP5_CNT1;
  volatile uint32_t SIE_EP5_CR0;
   volatile const uint32_t RESERVED9[13];
  volatile uint32_t SIE_EP6_CNT0;
  volatile uint32_t SIE_EP6_CNT1;
  volatile uint32_t SIE_EP6_CR0;
   volatile const uint32_t RESERVED10[13];
  volatile uint32_t SIE_EP7_CNT0;
  volatile uint32_t SIE_EP7_CNT1;
  volatile uint32_t SIE_EP7_CR0;
   volatile const uint32_t RESERVED11[13];
  volatile uint32_t SIE_EP8_CNT0;
  volatile uint32_t SIE_EP8_CNT1;
  volatile uint32_t SIE_EP8_CR0;
   volatile const uint32_t RESERVED12;
  volatile uint32_t ARB_EP1_CFG;
  volatile uint32_t ARB_EP1_INT_EN;
  volatile uint32_t ARB_EP1_SR;
   volatile const uint32_t RESERVED13;
  volatile uint32_t ARB_RW1_WA;
  volatile uint32_t ARB_RW1_WA_MSB;
  volatile uint32_t ARB_RW1_RA;
  volatile uint32_t ARB_RW1_RA_MSB;
  volatile uint32_t ARB_RW1_DR;
   volatile const uint32_t RESERVED14[3];
  volatile uint32_t BUF_SIZE;
   volatile const uint32_t RESERVED15;
  volatile uint32_t EP_ACTIVE;
  volatile uint32_t EP_TYPE;
  volatile uint32_t ARB_EP2_CFG;
  volatile uint32_t ARB_EP2_INT_EN;
  volatile uint32_t ARB_EP2_SR;
   volatile const uint32_t RESERVED16;
  volatile uint32_t ARB_RW2_WA;
  volatile uint32_t ARB_RW2_WA_MSB;
  volatile uint32_t ARB_RW2_RA;
  volatile uint32_t ARB_RW2_RA_MSB;
  volatile uint32_t ARB_RW2_DR;
   volatile const uint32_t RESERVED17[3];
  volatile uint32_t ARB_CFG;
  volatile uint32_t USB_CLK_EN;
  volatile uint32_t ARB_INT_EN;
   volatile const uint32_t ARB_INT_SR;
  volatile uint32_t ARB_EP3_CFG;
  volatile uint32_t ARB_EP3_INT_EN;
  volatile uint32_t ARB_EP3_SR;
   volatile const uint32_t RESERVED18;
  volatile uint32_t ARB_RW3_WA;
  volatile uint32_t ARB_RW3_WA_MSB;
  volatile uint32_t ARB_RW3_RA;
  volatile uint32_t ARB_RW3_RA_MSB;
  volatile uint32_t ARB_RW3_DR;
   volatile const uint32_t RESERVED19[3];
  volatile uint32_t CWA;
  volatile uint32_t CWA_MSB;
   volatile const uint32_t RESERVED20[2];
  volatile uint32_t ARB_EP4_CFG;
  volatile uint32_t ARB_EP4_INT_EN;
  volatile uint32_t ARB_EP4_SR;
   volatile const uint32_t RESERVED21;
  volatile uint32_t ARB_RW4_WA;
  volatile uint32_t ARB_RW4_WA_MSB;
  volatile uint32_t ARB_RW4_RA;
  volatile uint32_t ARB_RW4_RA_MSB;
  volatile uint32_t ARB_RW4_DR;
   volatile const uint32_t RESERVED22[3];
  volatile uint32_t DMA_THRES;
  volatile uint32_t DMA_THRES_MSB;
   volatile const uint32_t RESERVED23[2];
  volatile uint32_t ARB_EP5_CFG;
  volatile uint32_t ARB_EP5_INT_EN;
  volatile uint32_t ARB_EP5_SR;
   volatile const uint32_t RESERVED24;
  volatile uint32_t ARB_RW5_WA;
  volatile uint32_t ARB_RW5_WA_MSB;
  volatile uint32_t ARB_RW5_RA;
  volatile uint32_t ARB_RW5_RA_MSB;
  volatile uint32_t ARB_RW5_DR;
   volatile const uint32_t RESERVED25[3];
  volatile uint32_t BUS_RST_CNT;
   volatile const uint32_t RESERVED26[3];
  volatile uint32_t ARB_EP6_CFG;
  volatile uint32_t ARB_EP6_INT_EN;
  volatile uint32_t ARB_EP6_SR;
   volatile const uint32_t RESERVED27;
  volatile uint32_t ARB_RW6_WA;
  volatile uint32_t ARB_RW6_WA_MSB;
  volatile uint32_t ARB_RW6_RA;
  volatile uint32_t ARB_RW6_RA_MSB;
  volatile uint32_t ARB_RW6_DR;
   volatile const uint32_t RESERVED28[7];
  volatile uint32_t ARB_EP7_CFG;
  volatile uint32_t ARB_EP7_INT_EN;
  volatile uint32_t ARB_EP7_SR;
   volatile const uint32_t RESERVED29;
  volatile uint32_t ARB_RW7_WA;
  volatile uint32_t ARB_RW7_WA_MSB;
  volatile uint32_t ARB_RW7_RA;
  volatile uint32_t ARB_RW7_RA_MSB;
  volatile uint32_t ARB_RW7_DR;
   volatile const uint32_t RESERVED30[7];
  volatile uint32_t ARB_EP8_CFG;
  volatile uint32_t ARB_EP8_INT_EN;
  volatile uint32_t ARB_EP8_SR;
   volatile const uint32_t RESERVED31;
  volatile uint32_t ARB_RW8_WA;
  volatile uint32_t ARB_RW8_WA_MSB;
  volatile uint32_t ARB_RW8_RA;
  volatile uint32_t ARB_RW8_RA_MSB;
  volatile uint32_t ARB_RW8_DR;
   volatile const uint32_t RESERVED32[7];
  volatile uint32_t MEM_DATA[512];
   volatile const uint32_t RESERVED33[280];
   volatile const uint32_t SOF16;
   volatile const uint32_t RESERVED34[7];
   volatile const uint32_t OSCLK_DR16;
   volatile const uint32_t RESERVED35[99];
  volatile uint32_t ARB_RW1_WA16;
   volatile const uint32_t RESERVED36;
  volatile uint32_t ARB_RW1_RA16;
   volatile const uint32_t RESERVED37;
  volatile uint32_t ARB_RW1_DR16;
   volatile const uint32_t RESERVED38[11];
  volatile uint32_t ARB_RW2_WA16;
   volatile const uint32_t RESERVED39;
  volatile uint32_t ARB_RW2_RA16;
   volatile const uint32_t RESERVED40;
  volatile uint32_t ARB_RW2_DR16;
   volatile const uint32_t RESERVED41[11];
  volatile uint32_t ARB_RW3_WA16;
   volatile const uint32_t RESERVED42;
  volatile uint32_t ARB_RW3_RA16;
   volatile const uint32_t RESERVED43;
  volatile uint32_t ARB_RW3_DR16;
   volatile const uint32_t RESERVED44[3];
  volatile uint32_t CWA16;
   volatile const uint32_t RESERVED45[7];
  volatile uint32_t ARB_RW4_WA16;
   volatile const uint32_t RESERVED46;
  volatile uint32_t ARB_RW4_RA16;
   volatile const uint32_t RESERVED47;
  volatile uint32_t ARB_RW4_DR16;
   volatile const uint32_t RESERVED48[3];
  volatile uint32_t DMA_THRES16;
   volatile const uint32_t RESERVED49[7];
  volatile uint32_t ARB_RW5_WA16;
   volatile const uint32_t RESERVED50;
  volatile uint32_t ARB_RW5_RA16;
   volatile const uint32_t RESERVED51;
  volatile uint32_t ARB_RW5_DR16;
   volatile const uint32_t RESERVED52[11];
  volatile uint32_t ARB_RW6_WA16;
   volatile const uint32_t RESERVED53;
  volatile uint32_t ARB_RW6_RA16;
   volatile const uint32_t RESERVED54;
  volatile uint32_t ARB_RW6_DR16;
   volatile const uint32_t RESERVED55[11];
  volatile uint32_t ARB_RW7_WA16;
   volatile const uint32_t RESERVED56;
  volatile uint32_t ARB_RW7_RA16;
   volatile const uint32_t RESERVED57;
  volatile uint32_t ARB_RW7_DR16;
   volatile const uint32_t RESERVED58[11];
  volatile uint32_t ARB_RW8_WA16;
   volatile const uint32_t RESERVED59;
  volatile uint32_t ARB_RW8_RA16;
   volatile const uint32_t RESERVED60;
  volatile uint32_t ARB_RW8_DR16;
   volatile const uint32_t RESERVED61[775];
} USBFS_USBDEV_V1_Type;
typedef struct {
  volatile uint32_t POWER_CTL;
   volatile const uint32_t RESERVED;
  volatile uint32_t USBIO_CTL;
  volatile uint32_t FLOW_CTL;
  volatile uint32_t LPM_CTL;
   volatile const uint32_t LPM_STAT;
   volatile const uint32_t RESERVED1[2];
  volatile uint32_t INTR_SIE;
  volatile uint32_t INTR_SIE_SET;
  volatile uint32_t INTR_SIE_MASK;
   volatile const uint32_t INTR_SIE_MASKED;
  volatile uint32_t INTR_LVL_SEL;
   volatile const uint32_t INTR_CAUSE_HI;
   volatile const uint32_t INTR_CAUSE_MED;
   volatile const uint32_t INTR_CAUSE_LO;
   volatile const uint32_t RESERVED2[12];
  volatile uint32_t DFT_CTL;
   volatile const uint32_t RESERVED3[995];
} USBFS_USBLPM_V1_Type;
typedef struct {
  volatile uint32_t HOST_CTL0;
   volatile const uint32_t RESERVED[3];
  volatile uint32_t HOST_CTL1;
   volatile const uint32_t RESERVED1[59];
  volatile uint32_t HOST_CTL2;
  volatile uint32_t HOST_ERR;
  volatile uint32_t HOST_STATUS;
  volatile uint32_t HOST_FCOMP;
  volatile uint32_t HOST_RTIMER;
  volatile uint32_t HOST_ADDR;
  volatile uint32_t HOST_EOF;
  volatile uint32_t HOST_FRAME;
  volatile uint32_t HOST_TOKEN;
   volatile const uint32_t RESERVED2[183];
  volatile uint32_t HOST_EP1_CTL;
   volatile const uint32_t HOST_EP1_STATUS;
  volatile uint32_t HOST_EP1_RW1_DR;
  volatile uint32_t HOST_EP1_RW2_DR;
   volatile const uint32_t RESERVED3[60];
  volatile uint32_t HOST_EP2_CTL;
   volatile const uint32_t HOST_EP2_STATUS;
  volatile uint32_t HOST_EP2_RW1_DR;
  volatile uint32_t HOST_EP2_RW2_DR;
   volatile const uint32_t RESERVED4[188];
  volatile uint32_t HOST_LVL1_SEL;
  volatile uint32_t HOST_LVL2_SEL;
   volatile const uint32_t RESERVED5[62];
   volatile const uint32_t INTR_USBHOST_CAUSE_HI;
   volatile const uint32_t INTR_USBHOST_CAUSE_MED;
   volatile const uint32_t INTR_USBHOST_CAUSE_LO;
   volatile const uint32_t RESERVED6[5];
   volatile const uint32_t INTR_HOST_EP_CAUSE_HI;
   volatile const uint32_t INTR_HOST_EP_CAUSE_MED;
   volatile const uint32_t INTR_HOST_EP_CAUSE_LO;
   volatile const uint32_t RESERVED7[5];
  volatile uint32_t INTR_USBHOST;
  volatile uint32_t INTR_USBHOST_SET;
  volatile uint32_t INTR_USBHOST_MASK;
   volatile const uint32_t INTR_USBHOST_MASKED;
   volatile const uint32_t RESERVED8[44];
  volatile uint32_t INTR_HOST_EP;
  volatile uint32_t INTR_HOST_EP_SET;
  volatile uint32_t INTR_HOST_EP_MASK;
   volatile const uint32_t INTR_HOST_EP_MASKED;
   volatile const uint32_t RESERVED9[60];
  volatile uint32_t HOST_DMA_ENBL;
   volatile const uint32_t RESERVED10[7];
  volatile uint32_t HOST_EP1_BLK;
   volatile const uint32_t RESERVED11[3];
  volatile uint32_t HOST_EP2_BLK;
   volatile const uint32_t RESERVED12[1331];
} USBFS_USBHOST_V1_Type;
typedef struct {
        USBFS_USBDEV_V1_Type USBDEV;
        USBFS_USBLPM_V1_Type USBLPM;
   volatile const uint32_t RESERVED[1024];
        USBFS_USBHOST_V1_Type USBHOST;
} USBFS_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED;
  volatile uint32_t ADDR;
  volatile uint32_t MASK;
   volatile const uint32_t RESERVED1[4];
  volatile uint32_t ADDR_CTL;
   volatile const uint32_t RESERVED2[7];
  volatile uint32_t RD_CMD_CTL;
  volatile uint32_t RD_ADDR_CTL;
  volatile uint32_t RD_MODE_CTL;
  volatile uint32_t RD_DUMMY_CTL;
  volatile uint32_t RD_DATA_CTL;
   volatile const uint32_t RESERVED3[3];
  volatile uint32_t WR_CMD_CTL;
  volatile uint32_t WR_ADDR_CTL;
  volatile uint32_t WR_MODE_CTL;
  volatile uint32_t WR_DUMMY_CTL;
  volatile uint32_t WR_DATA_CTL;
   volatile const uint32_t RESERVED4[3];
} SMIF_DEVICE_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t STATUS;
   volatile const uint32_t RESERVED[15];
   volatile const uint32_t TX_CMD_FIFO_STATUS;
   volatile const uint32_t RESERVED1[2];
   volatile uint32_t TX_CMD_FIFO_WR;
   volatile const uint32_t RESERVED2[11];
  volatile uint32_t TX_DATA_FIFO_CTL;
   volatile const uint32_t TX_DATA_FIFO_STATUS;
   volatile const uint32_t RESERVED3[2];
   volatile uint32_t TX_DATA_FIFO_WR1;
   volatile uint32_t TX_DATA_FIFO_WR2;
   volatile uint32_t TX_DATA_FIFO_WR4;
   volatile const uint32_t RESERVED4[9];
  volatile uint32_t RX_DATA_FIFO_CTL;
   volatile const uint32_t RX_DATA_FIFO_STATUS;
   volatile const uint32_t RESERVED5[2];
   volatile const uint32_t RX_DATA_FIFO_RD1;
   volatile const uint32_t RX_DATA_FIFO_RD2;
   volatile const uint32_t RX_DATA_FIFO_RD4;
   volatile const uint32_t RESERVED6;
   volatile const uint32_t RX_DATA_FIFO_RD1_SILENT;
   volatile const uint32_t RESERVED7[7];
  volatile uint32_t SLOW_CA_CTL;
   volatile const uint32_t RESERVED8;
  volatile uint32_t SLOW_CA_CMD;
   volatile const uint32_t RESERVED9[29];
  volatile uint32_t FAST_CA_CTL;
   volatile const uint32_t RESERVED10;
  volatile uint32_t FAST_CA_CMD;
   volatile const uint32_t RESERVED11[29];
  volatile uint32_t CRYPTO_CMD;
   volatile const uint32_t RESERVED12[7];
  volatile uint32_t CRYPTO_INPUT0;
  volatile uint32_t CRYPTO_INPUT1;
  volatile uint32_t CRYPTO_INPUT2;
  volatile uint32_t CRYPTO_INPUT3;
   volatile const uint32_t RESERVED13[4];
   volatile uint32_t CRYPTO_KEY0;
   volatile uint32_t CRYPTO_KEY1;
   volatile uint32_t CRYPTO_KEY2;
   volatile uint32_t CRYPTO_KEY3;
   volatile const uint32_t RESERVED14[4];
  volatile uint32_t CRYPTO_OUTPUT0;
  volatile uint32_t CRYPTO_OUTPUT1;
  volatile uint32_t CRYPTO_OUTPUT2;
  volatile uint32_t CRYPTO_OUTPUT3;
   volatile const uint32_t RESERVED15[340];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED16[12];
        SMIF_DEVICE_V1_Type DEVICE[4];
} SMIF_V1_Type;
typedef struct {
  volatile uint32_t CTRL;
   volatile const uint32_t STATUS;
  volatile uint32_t CMD_RESP_CTRL;
   volatile const uint32_t CMD_RESP_STATUS;
   volatile const uint32_t RESERVED[4];
  volatile uint32_t SPI_CTRL;
   volatile const uint32_t SPI_STATUS;
   volatile const uint32_t RESERVED1[6];
  volatile uint32_t UART_CTRL;
  volatile uint32_t UART_TX_CTRL;
  volatile uint32_t UART_RX_CTRL;
   volatile const uint32_t UART_RX_STATUS;
  volatile uint32_t UART_FLOW_CTRL;
   volatile const uint32_t RESERVED2[3];
  volatile uint32_t I2C_CTRL;
   volatile const uint32_t I2C_STATUS;
  volatile uint32_t I2C_M_CMD;
  volatile uint32_t I2C_S_CMD;
  volatile uint32_t I2C_CFG;
   volatile const uint32_t RESERVED3[99];
  volatile uint32_t TX_CTRL;
  volatile uint32_t TX_FIFO_CTRL;
   volatile const uint32_t TX_FIFO_STATUS;
   volatile const uint32_t RESERVED4[13];
   volatile uint32_t TX_FIFO_WR;
   volatile const uint32_t RESERVED5[47];
  volatile uint32_t RX_CTRL;
  volatile uint32_t RX_FIFO_CTRL;
   volatile const uint32_t RX_FIFO_STATUS;
   volatile const uint32_t RESERVED6;
  volatile uint32_t RX_MATCH;
   volatile const uint32_t RESERVED7[11];
   volatile const uint32_t RX_FIFO_RD;
   volatile const uint32_t RX_FIFO_RD_SILENT;
   volatile const uint32_t RESERVED8[46];
  volatile uint32_t EZ_DATA[512];
   volatile const uint32_t RESERVED9[128];
   volatile const uint32_t INTR_CAUSE;
   volatile const uint32_t RESERVED10[31];
  volatile uint32_t INTR_I2C_EC;
   volatile const uint32_t RESERVED11;
  volatile uint32_t INTR_I2C_EC_MASK;
   volatile const uint32_t INTR_I2C_EC_MASKED;
   volatile const uint32_t RESERVED12[12];
  volatile uint32_t INTR_SPI_EC;
   volatile const uint32_t RESERVED13;
  volatile uint32_t INTR_SPI_EC_MASK;
   volatile const uint32_t INTR_SPI_EC_MASKED;
   volatile const uint32_t RESERVED14[12];
  volatile uint32_t INTR_M;
  volatile uint32_t INTR_M_SET;
  volatile uint32_t INTR_M_MASK;
   volatile const uint32_t INTR_M_MASKED;
   volatile const uint32_t RESERVED15[12];
  volatile uint32_t INTR_S;
  volatile uint32_t INTR_S_SET;
  volatile uint32_t INTR_S_MASK;
   volatile const uint32_t INTR_S_MASKED;
   volatile const uint32_t RESERVED16[12];
  volatile uint32_t INTR_TX;
  volatile uint32_t INTR_TX_SET;
  volatile uint32_t INTR_TX_MASK;
   volatile const uint32_t INTR_TX_MASKED;
   volatile const uint32_t RESERVED17[12];
  volatile uint32_t INTR_RX;
  volatile uint32_t INTR_RX_SET;
  volatile uint32_t INTR_RX_MASK;
   volatile const uint32_t INTR_RX_MASKED;
} CySCB_V1_Type;
typedef struct {
  volatile uint32_t CTB_CTRL;
  volatile uint32_t OA_RES0_CTRL;
  volatile uint32_t OA_RES1_CTRL;
   volatile const uint32_t COMP_STAT;
   volatile const uint32_t RESERVED[4];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED1[20];
  volatile uint32_t OA0_SW;
  volatile uint32_t OA0_SW_CLEAR;
  volatile uint32_t OA1_SW;
  volatile uint32_t OA1_SW_CLEAR;
   volatile const uint32_t RESERVED2[4];
  volatile uint32_t CTD_SW;
  volatile uint32_t CTD_SW_CLEAR;
   volatile const uint32_t RESERVED3[6];
  volatile uint32_t CTB_SW_DS_CTRL;
  volatile uint32_t CTB_SW_SQ_CTRL;
   volatile const uint32_t CTB_SW_STATUS;
   volatile const uint32_t RESERVED4[909];
  volatile uint32_t OA0_OFFSET_TRIM;
  volatile uint32_t OA0_SLOPE_OFFSET_TRIM;
  volatile uint32_t OA0_COMP_TRIM;
  volatile uint32_t OA1_OFFSET_TRIM;
  volatile uint32_t OA1_SLOPE_OFFSET_TRIM;
  volatile uint32_t OA1_COMP_TRIM;
} CTBM_V1_Type;
typedef struct {
  volatile uint32_t CTDAC_CTRL;
   volatile const uint32_t RESERVED[7];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED1[32];
  volatile uint32_t CTDAC_SW;
  volatile uint32_t CTDAC_SW_CLEAR;
   volatile const uint32_t RESERVED2[18];
  volatile uint32_t CTDAC_VAL;
  volatile uint32_t CTDAC_VAL_NXT;
} CTDAC_V1_Type;
typedef struct {
  volatile uint32_t CTRL;
  volatile uint32_t SAMPLE_CTRL;
   volatile const uint32_t RESERVED[2];
  volatile uint32_t SAMPLE_TIME01;
  volatile uint32_t SAMPLE_TIME23;
  volatile uint32_t RANGE_THRES;
  volatile uint32_t RANGE_COND;
  volatile uint32_t CHAN_EN;
  volatile uint32_t START_CTRL;
   volatile const uint32_t RESERVED1[22];
  volatile uint32_t CHAN_CONFIG[16];
   volatile const uint32_t RESERVED2[16];
   volatile const uint32_t CHAN_WORK[16];
   volatile const uint32_t RESERVED3[16];
   volatile const uint32_t CHAN_RESULT[16];
   volatile const uint32_t RESERVED4[16];
   volatile const uint32_t CHAN_WORK_UPDATED;
   volatile const uint32_t CHAN_RESULT_UPDATED;
   volatile const uint32_t CHAN_WORK_NEWVALUE;
   volatile const uint32_t CHAN_RESULT_NEWVALUE;
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
  volatile uint32_t SATURATE_INTR;
  volatile uint32_t SATURATE_INTR_SET;
  volatile uint32_t SATURATE_INTR_MASK;
   volatile const uint32_t SATURATE_INTR_MASKED;
  volatile uint32_t RANGE_INTR;
  volatile uint32_t RANGE_INTR_SET;
  volatile uint32_t RANGE_INTR_MASK;
   volatile const uint32_t RANGE_INTR_MASKED;
   volatile const uint32_t INTR_CAUSE;
   volatile const uint32_t RESERVED5[15];
  volatile uint32_t INJ_CHAN_CONFIG;
   volatile const uint32_t RESERVED6[3];
   volatile const uint32_t INJ_RESULT;
   volatile const uint32_t RESERVED7[3];
   volatile const uint32_t STATUS;
   volatile const uint32_t AVG_STAT;
   volatile const uint32_t RESERVED8[22];
  volatile uint32_t MUX_SWITCH0;
  volatile uint32_t MUX_SWITCH_CLEAR0;
   volatile const uint32_t RESERVED9[14];
  volatile uint32_t MUX_SWITCH_DS_CTRL;
  volatile uint32_t MUX_SWITCH_SQ_CTRL;
   volatile const uint32_t MUX_SWITCH_STATUS;
   volatile const uint32_t RESERVED10[749];
  volatile uint32_t ANA_TRIM0;
  volatile uint32_t ANA_TRIM1;
} SAR_V1_Type;
typedef struct {
  volatile uint32_t AREF_CTRL;
   volatile const uint32_t RESERVED[63];
} PASS_AREF_V1_Type;
typedef struct {
   volatile const uint32_t INTR_CAUSE;
   volatile const uint32_t RESERVED[895];
        PASS_AREF_V1_Type AREF;
  volatile uint32_t VREF_TRIM0;
  volatile uint32_t VREF_TRIM1;
  volatile uint32_t VREF_TRIM2;
  volatile uint32_t VREF_TRIM3;
  volatile uint32_t IZTAT_TRIM0;
  volatile uint32_t IZTAT_TRIM1;
  volatile uint32_t IPTAT_TRIM0;
  volatile uint32_t ICTAT_TRIM0;
} PASS_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED[3];
  volatile uint32_t CLOCK_CTL;
   volatile const uint32_t RESERVED1[3];
  volatile uint32_t CMD;
   volatile const uint32_t RESERVED2[7];
  volatile uint32_t TR_CTL;
   volatile const uint32_t RESERVED3[15];
  volatile uint32_t TX_CTL;
  volatile uint32_t TX_WATCHDOG;
   volatile const uint32_t RESERVED4[6];
  volatile uint32_t RX_CTL;
  volatile uint32_t RX_WATCHDOG;
   volatile const uint32_t RESERVED5[86];
  volatile uint32_t TX_FIFO_CTL;
   volatile const uint32_t TX_FIFO_STATUS;
   volatile uint32_t TX_FIFO_WR;
   volatile const uint32_t RESERVED6[61];
  volatile uint32_t RX_FIFO_CTL;
   volatile const uint32_t RX_FIFO_STATUS;
   volatile const uint32_t RX_FIFO_RD;
   volatile const uint32_t RX_FIFO_RD_SILENT;
   volatile const uint32_t RESERVED7[764];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
} I2S_V1_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED[3];
  volatile uint32_t CLOCK_CTL;
  volatile uint32_t MODE_CTL;
  volatile uint32_t DATA_CTL;
   volatile const uint32_t RESERVED1;
  volatile uint32_t CMD;
   volatile const uint32_t RESERVED2[7];
  volatile uint32_t TR_CTL;
   volatile const uint32_t RESERVED3[175];
  volatile uint32_t RX_FIFO_CTL;
   volatile const uint32_t RX_FIFO_STATUS;
   volatile const uint32_t RX_FIFO_RD;
   volatile const uint32_t RX_FIFO_RD_SILENT;
   volatile const uint32_t RESERVED4[764];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
} PDM_V1_Type;
typedef SFLASH_V1_Type SFLASH_Type;
typedef PERI_GR_V1_Type PERI_GR_Type;
typedef PERI_TR_GR_V1_Type PERI_TR_GR_Type;
typedef PERI_PPU_PR_V1_Type PERI_PPU_PR_Type;
typedef PERI_PPU_GR_V1_Type PERI_PPU_GR_Type;
typedef PERI_GR_PPU_SL_V1_Type PERI_GR_PPU_SL_Type;
typedef PERI_GR_PPU_RG_V1_Type PERI_GR_PPU_RG_Type;
typedef PERI_V1_Type PERI_Type;
typedef CRYPTO_V1_Type CRYPTO_Type;
typedef CPUSS_V1_Type CPUSS_Type;
typedef FAULT_STRUCT_V1_Type FAULT_STRUCT_Type;
typedef FAULT_V1_Type FAULT_Type;
typedef IPC_STRUCT_V1_Type IPC_STRUCT_Type;
typedef IPC_INTR_STRUCT_V1_Type IPC_INTR_STRUCT_Type;
typedef IPC_V1_Type IPC_Type;
typedef PROT_SMPU_SMPU_STRUCT_V1_Type PROT_SMPU_SMPU_STRUCT_Type;
typedef PROT_SMPU_V1_Type PROT_SMPU_Type;
typedef PROT_MPU_MPU_STRUCT_V1_Type PROT_MPU_MPU_STRUCT_Type;
typedef PROT_MPU_V1_Type PROT_MPU_Type;
typedef PROT_V1_Type PROT_Type;
typedef FLASHC_FM_CTL_V1_Type FLASHC_FM_CTL_Type;
typedef FLASHC_V1_Type FLASHC_Type;
typedef MCWDT_STRUCT_V1_Type MCWDT_STRUCT_Type;
typedef SRSS_V1_Type SRSS_Type;
typedef BACKUP_V1_Type BACKUP_Type;
typedef DW_CH_STRUCT_V1_Type DW_CH_STRUCT_Type;
typedef DW_V1_Type DW_Type;
typedef EFUSE_V1_Type EFUSE_Type;
typedef PROFILE_CNT_STRUCT_V1_Type PROFILE_CNT_STRUCT_Type;
typedef PROFILE_V1_Type PROFILE_Type;
typedef HSIOM_PRT_V1_Type HSIOM_PRT_Type;
typedef HSIOM_V1_Type HSIOM_Type;
typedef GPIO_PRT_V1_Type GPIO_PRT_Type;
typedef GPIO_V1_Type GPIO_Type;
typedef SMARTIO_PRT_V1_Type SMARTIO_PRT_Type;
typedef SMARTIO_V1_Type SMARTIO_Type;
typedef UDB_WRKONE_V1_Type UDB_WRKONE_Type;
typedef UDB_WRKMULT_V1_Type UDB_WRKMULT_Type;
typedef UDB_UDBPAIR_UDBSNG_V1_Type UDB_UDBPAIR_UDBSNG_Type;
typedef UDB_UDBPAIR_ROUTE_V1_Type UDB_UDBPAIR_ROUTE_Type;
typedef UDB_UDBPAIR_V1_Type UDB_UDBPAIR_Type;
typedef UDB_DSI_V1_Type UDB_DSI_Type;
typedef UDB_PA_V1_Type UDB_PA_Type;
typedef UDB_BCTL_V1_Type UDB_BCTL_Type;
typedef UDB_UDBIF_V1_Type UDB_UDBIF_Type;
typedef UDB_V1_Type UDB_Type;
typedef LPCOMP_V1_Type LPCOMP_Type;
typedef CSD_V1_Type CSD_Type;
typedef TCPWM_CNT_V1_Type TCPWM_CNT_Type;
typedef TCPWM_V1_Type TCPWM_Type;
typedef LCD_V1_Type LCD_Type;
typedef BLE_RCB_RCBLL_V1_Type BLE_RCB_RCBLL_Type;
typedef BLE_RCB_V1_Type BLE_RCB_Type;
typedef BLE_BLELL_V1_Type BLE_BLELL_Type;
typedef BLE_BLESS_V1_Type BLE_BLESS_Type;
typedef BLE_V1_Type BLE_Type;
typedef USBFS_USBDEV_V1_Type USBFS_USBDEV_Type;
typedef USBFS_USBLPM_V1_Type USBFS_USBLPM_Type;
typedef USBFS_USBHOST_V1_Type USBFS_USBHOST_Type;
typedef USBFS_V1_Type USBFS_Type;
typedef SMIF_DEVICE_V1_Type SMIF_DEVICE_Type;
typedef SMIF_V1_Type SMIF_Type;
typedef CySCB_V1_Type CySCB_Type;
typedef CTBM_V1_Type CTBM_Type;
typedef CTDAC_V1_Type CTDAC_Type;
typedef SAR_V1_Type SAR_Type;
typedef PASS_AREF_V1_Type PASS_AREF_Type;
typedef PASS_V1_Type PASS_Type;
typedef I2S_V1_Type I2S_Type;
typedef PDM_V1_Type PDM_Type;
enum
{
    CY_GPIO_PACKAGE_QFN,
    CY_GPIO_PACKAGE_BGA,
    CY_GPIO_PACKAGE_CSP,
    CY_GPIO_PACKAGE_WLCSP,
    CY_GPIO_PACKAGE_LQFP,
    CY_GPIO_PACKAGE_TQFP,
    CY_GPIO_PACKAGE_TEQFP,
    CY_GPIO_PACKAGE_SMT,
};
enum
{
    AMUXBUS_ADFT0_VDDD,
    AMUXBUS_ADFT1_VDDD,
    AMUXBUS_ANALOG_VDDA,
    AMUXBUS_ANALOG_VDDD,
    AMUXBUS_CSD0,
    AMUXBUS_CSD1,
    AMUXBUS_MAIN,
    AMUXBUS_NOISY,
    AMUXBUS_SAR,
    AMUXBUS_VDDIO_1,
};
typedef enum
{
    AMUX_SPLIT_CTL_0 = 0x0000u,
    AMUX_SPLIT_CTL_1 = 0x0001u,
    AMUX_SPLIT_CTL_2 = 0x0002u,
    AMUX_SPLIT_CTL_3 = 0x0003u,
    AMUX_SPLIT_CTL_4 = 0x0004u,
    AMUX_SPLIT_CTL_5 = 0x0005u,
    AMUX_SPLIT_CTL_6 = 0x0006u,
    AMUX_SPLIT_CTL_7 = 0x0007u,
    AMUX_SPLIT_CTL_8 = 0x0008u
} cy_en_amux_split_t;
typedef enum
{
    HSIOM_SEL_GPIO = 0,
    HSIOM_SEL_GPIO_DSI = 1,
    HSIOM_SEL_DSI_DSI = 2,
    HSIOM_SEL_DSI_GPIO = 3,
    HSIOM_SEL_AMUXA = 4,
    HSIOM_SEL_AMUXB = 5,
    HSIOM_SEL_AMUXA_DSI = 6,
    HSIOM_SEL_AMUXB_DSI = 7,
    HSIOM_SEL_ACT_0 = 8,
    HSIOM_SEL_ACT_1 = 9,
    HSIOM_SEL_ACT_2 = 10,
    HSIOM_SEL_ACT_3 = 11,
    HSIOM_SEL_DS_0 = 12,
    HSIOM_SEL_DS_1 = 13,
    HSIOM_SEL_DS_2 = 14,
    HSIOM_SEL_DS_3 = 15,
    HSIOM_SEL_ACT_4 = 16,
    HSIOM_SEL_ACT_5 = 17,
    HSIOM_SEL_ACT_6 = 18,
    HSIOM_SEL_ACT_7 = 19,
    HSIOM_SEL_ACT_8 = 20,
    HSIOM_SEL_ACT_9 = 21,
    HSIOM_SEL_ACT_10 = 22,
    HSIOM_SEL_ACT_11 = 23,
    HSIOM_SEL_ACT_12 = 24,
    HSIOM_SEL_ACT_13 = 25,
    HSIOM_SEL_ACT_14 = 26,
    HSIOM_SEL_ACT_15 = 27,
    HSIOM_SEL_DS_4 = 28,
    HSIOM_SEL_DS_5 = 29,
    HSIOM_SEL_DS_6 = 30,
    HSIOM_SEL_DS_7 = 31,
    P0_0_GPIO = 0,
    P0_0_GPIO_DSI = 1,
    P0_0_DSI_DSI = 2,
    P0_0_DSI_GPIO = 3,
    P0_0_AMUXA = 4,
    P0_0_AMUXB = 5,
    P0_0_AMUXA_DSI = 6,
    P0_0_AMUXB_DSI = 7,
    P0_0_TCPWM0_LINE0 = 8,
    P0_0_TCPWM1_LINE0 = 9,
    P0_0_CSD_CSD_TX = 10,
    P0_0_CSD_CSD_TX_N = 11,
    P0_0_LCD_COM0 = 12,
    P0_0_LCD_SEG0 = 13,
    P0_0_SRSS_EXT_CLK = 16,
    P0_0_SCB0_SPI_SELECT1 = 20,
    P0_0_PERI_TR_IO_INPUT0 = 24,
    P0_1_GPIO = 0,
    P0_1_GPIO_DSI = 1,
    P0_1_DSI_DSI = 2,
    P0_1_DSI_GPIO = 3,
    P0_1_AMUXA = 4,
    P0_1_AMUXB = 5,
    P0_1_AMUXA_DSI = 6,
    P0_1_AMUXB_DSI = 7,
    P0_1_TCPWM0_LINE_COMPL0 = 8,
    P0_1_TCPWM1_LINE_COMPL0 = 9,
    P0_1_CSD_CSD_TX = 10,
    P0_1_CSD_CSD_TX_N = 11,
    P0_1_LCD_COM1 = 12,
    P0_1_LCD_SEG1 = 13,
    P0_1_SCB0_SPI_SELECT2 = 20,
    P0_1_PERI_TR_IO_INPUT1 = 24,
    P0_1_CPUSS_SWJ_TRSTN = 29,
    P0_2_GPIO = 0,
    P0_2_GPIO_DSI = 1,
    P0_2_DSI_DSI = 2,
    P0_2_DSI_GPIO = 3,
    P0_2_AMUXA = 4,
    P0_2_AMUXB = 5,
    P0_2_AMUXA_DSI = 6,
    P0_2_AMUXB_DSI = 7,
    P0_2_TCPWM0_LINE1 = 8,
    P0_2_TCPWM1_LINE1 = 9,
    P0_2_CSD_CSD_TX = 10,
    P0_2_CSD_CSD_TX_N = 11,
    P0_2_LCD_COM2 = 12,
    P0_2_LCD_SEG2 = 13,
    P0_2_SCB0_UART_RX = 18,
    P0_2_SCB0_I2C_SCL = 19,
    P0_2_SCB0_SPI_MOSI = 20,
    P0_3_GPIO = 0,
    P0_3_GPIO_DSI = 1,
    P0_3_DSI_DSI = 2,
    P0_3_DSI_GPIO = 3,
    P0_3_AMUXA = 4,
    P0_3_AMUXB = 5,
    P0_3_AMUXA_DSI = 6,
    P0_3_AMUXB_DSI = 7,
    P0_3_TCPWM0_LINE_COMPL1 = 8,
    P0_3_TCPWM1_LINE_COMPL1 = 9,
    P0_3_CSD_CSD_TX = 10,
    P0_3_CSD_CSD_TX_N = 11,
    P0_3_LCD_COM3 = 12,
    P0_3_LCD_SEG3 = 13,
    P0_3_SCB0_UART_TX = 18,
    P0_3_SCB0_I2C_SDA = 19,
    P0_3_SCB0_SPI_MISO = 20,
    P0_4_GPIO = 0,
    P0_4_GPIO_DSI = 1,
    P0_4_DSI_DSI = 2,
    P0_4_DSI_GPIO = 3,
    P0_4_AMUXA = 4,
    P0_4_AMUXB = 5,
    P0_4_AMUXA_DSI = 6,
    P0_4_AMUXB_DSI = 7,
    P0_4_TCPWM0_LINE2 = 8,
    P0_4_TCPWM1_LINE2 = 9,
    P0_4_CSD_CSD_TX = 10,
    P0_4_CSD_CSD_TX_N = 11,
    P0_4_LCD_COM4 = 12,
    P0_4_LCD_SEG4 = 13,
    P0_4_SCB0_UART_RTS = 18,
    P0_4_SCB0_SPI_CLK = 20,
    P0_4_PERI_TR_IO_OUTPUT0 = 25,
    P0_5_GPIO = 0,
    P0_5_GPIO_DSI = 1,
    P0_5_DSI_DSI = 2,
    P0_5_DSI_GPIO = 3,
    P0_5_AMUXA = 4,
    P0_5_AMUXB = 5,
    P0_5_AMUXA_DSI = 6,
    P0_5_AMUXB_DSI = 7,
    P0_5_TCPWM0_LINE_COMPL2 = 8,
    P0_5_TCPWM1_LINE_COMPL2 = 9,
    P0_5_CSD_CSD_TX = 10,
    P0_5_CSD_CSD_TX_N = 11,
    P0_5_LCD_COM5 = 12,
    P0_5_LCD_SEG5 = 13,
    P0_5_SRSS_EXT_CLK = 16,
    P0_5_SCB0_UART_CTS = 18,
    P0_5_SCB0_SPI_SELECT0 = 20,
    P0_5_PERI_TR_IO_OUTPUT1 = 25,
    P1_0_GPIO = 0,
    P1_0_GPIO_DSI = 1,
    P1_0_DSI_DSI = 2,
    P1_0_DSI_GPIO = 3,
    P1_0_AMUXA = 4,
    P1_0_AMUXB = 5,
    P1_0_AMUXA_DSI = 6,
    P1_0_AMUXB_DSI = 7,
    P1_0_TCPWM0_LINE3 = 8,
    P1_0_TCPWM1_LINE3 = 9,
    P1_0_CSD_CSD_TX = 10,
    P1_0_CSD_CSD_TX_N = 11,
    P1_0_LCD_COM6 = 12,
    P1_0_LCD_SEG6 = 13,
    P1_0_SCB7_UART_RX = 18,
    P1_0_SCB7_I2C_SCL = 19,
    P1_0_SCB7_SPI_MOSI = 20,
    P1_0_PERI_TR_IO_INPUT2 = 24,
    P1_1_GPIO = 0,
    P1_1_GPIO_DSI = 1,
    P1_1_DSI_DSI = 2,
    P1_1_DSI_GPIO = 3,
    P1_1_AMUXA = 4,
    P1_1_AMUXB = 5,
    P1_1_AMUXA_DSI = 6,
    P1_1_AMUXB_DSI = 7,
    P1_1_TCPWM0_LINE_COMPL3 = 8,
    P1_1_TCPWM1_LINE_COMPL3 = 9,
    P1_1_CSD_CSD_TX = 10,
    P1_1_CSD_CSD_TX_N = 11,
    P1_1_LCD_COM7 = 12,
    P1_1_LCD_SEG7 = 13,
    P1_1_SCB7_UART_TX = 18,
    P1_1_SCB7_I2C_SDA = 19,
    P1_1_SCB7_SPI_MISO = 20,
    P1_1_PERI_TR_IO_INPUT3 = 24,
    P1_2_GPIO = 0,
    P1_2_GPIO_DSI = 1,
    P1_2_DSI_DSI = 2,
    P1_2_DSI_GPIO = 3,
    P1_2_AMUXA = 4,
    P1_2_AMUXB = 5,
    P1_2_AMUXA_DSI = 6,
    P1_2_AMUXB_DSI = 7,
    P1_2_TCPWM0_LINE4 = 8,
    P1_2_TCPWM1_LINE12 = 9,
    P1_2_CSD_CSD_TX = 10,
    P1_2_CSD_CSD_TX_N = 11,
    P1_2_LCD_COM8 = 12,
    P1_2_LCD_SEG8 = 13,
    P1_2_SCB7_UART_RTS = 18,
    P1_2_SCB7_SPI_CLK = 20,
    P1_3_GPIO = 0,
    P1_3_GPIO_DSI = 1,
    P1_3_DSI_DSI = 2,
    P1_3_DSI_GPIO = 3,
    P1_3_AMUXA = 4,
    P1_3_AMUXB = 5,
    P1_3_AMUXA_DSI = 6,
    P1_3_AMUXB_DSI = 7,
    P1_3_TCPWM0_LINE_COMPL4 = 8,
    P1_3_TCPWM1_LINE_COMPL12 = 9,
    P1_3_CSD_CSD_TX = 10,
    P1_3_CSD_CSD_TX_N = 11,
    P1_3_LCD_COM9 = 12,
    P1_3_LCD_SEG9 = 13,
    P1_3_SCB7_UART_CTS = 18,
    P1_3_SCB7_SPI_SELECT0 = 20,
    P1_4_GPIO = 0,
    P1_4_GPIO_DSI = 1,
    P1_4_DSI_DSI = 2,
    P1_4_DSI_GPIO = 3,
    P1_4_AMUXA = 4,
    P1_4_AMUXB = 5,
    P1_4_AMUXA_DSI = 6,
    P1_4_AMUXB_DSI = 7,
    P1_4_TCPWM0_LINE5 = 8,
    P1_4_TCPWM1_LINE13 = 9,
    P1_4_CSD_CSD_TX = 10,
    P1_4_CSD_CSD_TX_N = 11,
    P1_4_LCD_COM10 = 12,
    P1_4_LCD_SEG10 = 13,
    P1_4_SCB7_SPI_SELECT1 = 20,
    P1_5_GPIO = 0,
    P1_5_GPIO_DSI = 1,
    P1_5_DSI_DSI = 2,
    P1_5_DSI_GPIO = 3,
    P1_5_AMUXA = 4,
    P1_5_AMUXB = 5,
    P1_5_AMUXA_DSI = 6,
    P1_5_AMUXB_DSI = 7,
    P1_5_TCPWM0_LINE_COMPL5 = 8,
    P1_5_TCPWM1_LINE_COMPL14 = 9,
    P1_5_CSD_CSD_TX = 10,
    P1_5_CSD_CSD_TX_N = 11,
    P1_5_LCD_COM11 = 12,
    P1_5_LCD_SEG11 = 13,
    P1_5_SCB7_SPI_SELECT2 = 20,
    P5_0_GPIO = 0,
    P5_0_GPIO_DSI = 1,
    P5_0_DSI_DSI = 2,
    P5_0_DSI_GPIO = 3,
    P5_0_AMUXA = 4,
    P5_0_AMUXB = 5,
    P5_0_AMUXA_DSI = 6,
    P5_0_AMUXB_DSI = 7,
    P5_0_TCPWM0_LINE4 = 8,
    P5_0_TCPWM1_LINE4 = 9,
    P5_0_CSD_CSD_TX = 10,
    P5_0_CSD_CSD_TX_N = 11,
    P5_0_LCD_COM30 = 12,
    P5_0_LCD_SEG30 = 13,
    P5_0_SCB5_UART_RX = 18,
    P5_0_SCB5_I2C_SCL = 19,
    P5_0_SCB5_SPI_MOSI = 20,
    P5_0_AUDIOSS_CLK_I2S_IF = 22,
    P5_0_AUDIOSS0_CLK_I2S_IF = 22,
    P5_0_PERI_TR_IO_INPUT10 = 24,
    P5_1_GPIO = 0,
    P5_1_GPIO_DSI = 1,
    P5_1_DSI_DSI = 2,
    P5_1_DSI_GPIO = 3,
    P5_1_AMUXA = 4,
    P5_1_AMUXB = 5,
    P5_1_AMUXA_DSI = 6,
    P5_1_AMUXB_DSI = 7,
    P5_1_TCPWM0_LINE_COMPL4 = 8,
    P5_1_TCPWM1_LINE_COMPL4 = 9,
    P5_1_CSD_CSD_TX = 10,
    P5_1_CSD_CSD_TX_N = 11,
    P5_1_LCD_COM31 = 12,
    P5_1_LCD_SEG31 = 13,
    P5_1_SCB5_UART_TX = 18,
    P5_1_SCB5_I2C_SDA = 19,
    P5_1_SCB5_SPI_MISO = 20,
    P5_1_AUDIOSS_TX_SCK = 22,
    P5_1_AUDIOSS0_TX_SCK = 22,
    P5_1_PERI_TR_IO_INPUT11 = 24,
    P5_2_GPIO = 0,
    P5_2_GPIO_DSI = 1,
    P5_2_DSI_DSI = 2,
    P5_2_DSI_GPIO = 3,
    P5_2_AMUXA = 4,
    P5_2_AMUXB = 5,
    P5_2_AMUXA_DSI = 6,
    P5_2_AMUXB_DSI = 7,
    P5_2_TCPWM0_LINE5 = 8,
    P5_2_TCPWM1_LINE5 = 9,
    P5_2_CSD_CSD_TX = 10,
    P5_2_CSD_CSD_TX_N = 11,
    P5_2_LCD_COM32 = 12,
    P5_2_LCD_SEG32 = 13,
    P5_2_SCB5_UART_RTS = 18,
    P5_2_SCB5_SPI_CLK = 20,
    P5_2_AUDIOSS_TX_WS = 22,
    P5_2_AUDIOSS0_TX_WS = 22,
    P5_3_GPIO = 0,
    P5_3_GPIO_DSI = 1,
    P5_3_DSI_DSI = 2,
    P5_3_DSI_GPIO = 3,
    P5_3_AMUXA = 4,
    P5_3_AMUXB = 5,
    P5_3_AMUXA_DSI = 6,
    P5_3_AMUXB_DSI = 7,
    P5_3_TCPWM0_LINE_COMPL5 = 8,
    P5_3_TCPWM1_LINE_COMPL5 = 9,
    P5_3_CSD_CSD_TX = 10,
    P5_3_CSD_CSD_TX_N = 11,
    P5_3_LCD_COM33 = 12,
    P5_3_LCD_SEG33 = 13,
    P5_3_SCB5_UART_CTS = 18,
    P5_3_SCB5_SPI_SELECT0 = 20,
    P5_3_AUDIOSS_TX_SDO = 22,
    P5_3_AUDIOSS0_TX_SDO = 22,
    P5_4_GPIO = 0,
    P5_4_GPIO_DSI = 1,
    P5_4_DSI_DSI = 2,
    P5_4_DSI_GPIO = 3,
    P5_4_AMUXA = 4,
    P5_4_AMUXB = 5,
    P5_4_AMUXA_DSI = 6,
    P5_4_AMUXB_DSI = 7,
    P5_4_TCPWM0_LINE6 = 8,
    P5_4_TCPWM1_LINE6 = 9,
    P5_4_CSD_CSD_TX = 10,
    P5_4_CSD_CSD_TX_N = 11,
    P5_4_LCD_COM34 = 12,
    P5_4_LCD_SEG34 = 13,
    P5_4_SCB5_SPI_SELECT1 = 20,
    P5_4_AUDIOSS_RX_SCK = 22,
    P5_4_AUDIOSS0_RX_SCK = 22,
    P5_5_GPIO = 0,
    P5_5_GPIO_DSI = 1,
    P5_5_DSI_DSI = 2,
    P5_5_DSI_GPIO = 3,
    P5_5_AMUXA = 4,
    P5_5_AMUXB = 5,
    P5_5_AMUXA_DSI = 6,
    P5_5_AMUXB_DSI = 7,
    P5_5_TCPWM0_LINE_COMPL6 = 8,
    P5_5_TCPWM1_LINE_COMPL6 = 9,
    P5_5_CSD_CSD_TX = 10,
    P5_5_CSD_CSD_TX_N = 11,
    P5_5_LCD_COM35 = 12,
    P5_5_LCD_SEG35 = 13,
    P5_5_SCB5_SPI_SELECT2 = 20,
    P5_5_AUDIOSS_RX_WS = 22,
    P5_5_AUDIOSS0_RX_WS = 22,
    P5_6_GPIO = 0,
    P5_6_GPIO_DSI = 1,
    P5_6_DSI_DSI = 2,
    P5_6_DSI_GPIO = 3,
    P5_6_AMUXA = 4,
    P5_6_AMUXB = 5,
    P5_6_AMUXA_DSI = 6,
    P5_6_AMUXB_DSI = 7,
    P5_6_TCPWM0_LINE7 = 8,
    P5_6_TCPWM1_LINE7 = 9,
    P5_6_CSD_CSD_TX = 10,
    P5_6_CSD_CSD_TX_N = 11,
    P5_6_LCD_COM36 = 12,
    P5_6_LCD_SEG36 = 13,
    P5_6_SCB5_SPI_SELECT3 = 20,
    P5_6_AUDIOSS_RX_SDI = 22,
    P5_6_AUDIOSS0_RX_SDI = 22,
    P6_0_GPIO = 0,
    P6_0_GPIO_DSI = 1,
    P6_0_DSI_DSI = 2,
    P6_0_DSI_GPIO = 3,
    P6_0_AMUXA = 4,
    P6_0_AMUXB = 5,
    P6_0_AMUXA_DSI = 6,
    P6_0_AMUXB_DSI = 7,
    P6_0_TCPWM0_LINE0 = 8,
    P6_0_TCPWM1_LINE8 = 9,
    P6_0_CSD_CSD_TX = 10,
    P6_0_CSD_CSD_TX_N = 11,
    P6_0_LCD_COM38 = 12,
    P6_0_LCD_SEG38 = 13,
    P6_0_SCB8_I2C_SCL = 14,
    P6_0_SCB3_UART_RX = 18,
    P6_0_SCB3_I2C_SCL = 19,
    P6_0_SCB3_SPI_MOSI = 20,
    P6_0_CPUSS_FAULT_OUT0 = 25,
    P6_0_SCB8_SPI_MOSI = 30,
    P6_1_GPIO = 0,
    P6_1_GPIO_DSI = 1,
    P6_1_DSI_DSI = 2,
    P6_1_DSI_GPIO = 3,
    P6_1_AMUXA = 4,
    P6_1_AMUXB = 5,
    P6_1_AMUXA_DSI = 6,
    P6_1_AMUXB_DSI = 7,
    P6_1_TCPWM0_LINE_COMPL0 = 8,
    P6_1_TCPWM1_LINE_COMPL8 = 9,
    P6_1_CSD_CSD_TX = 10,
    P6_1_CSD_CSD_TX_N = 11,
    P6_1_LCD_COM39 = 12,
    P6_1_LCD_SEG39 = 13,
    P6_1_SCB8_I2C_SDA = 14,
    P6_1_SCB3_UART_TX = 18,
    P6_1_SCB3_I2C_SDA = 19,
    P6_1_SCB3_SPI_MISO = 20,
    P6_1_CPUSS_FAULT_OUT1 = 25,
    P6_1_SCB8_SPI_MISO = 30,
    P6_2_GPIO = 0,
    P6_2_GPIO_DSI = 1,
    P6_2_DSI_DSI = 2,
    P6_2_DSI_GPIO = 3,
    P6_2_AMUXA = 4,
    P6_2_AMUXB = 5,
    P6_2_AMUXA_DSI = 6,
    P6_2_AMUXB_DSI = 7,
    P6_2_TCPWM0_LINE1 = 8,
    P6_2_TCPWM1_LINE9 = 9,
    P6_2_CSD_CSD_TX = 10,
    P6_2_CSD_CSD_TX_N = 11,
    P6_2_LCD_COM40 = 12,
    P6_2_LCD_SEG40 = 13,
    P6_2_SCB3_UART_RTS = 18,
    P6_2_SCB3_SPI_CLK = 20,
    P6_2_SCB8_SPI_CLK = 30,
    P6_3_GPIO = 0,
    P6_3_GPIO_DSI = 1,
    P6_3_DSI_DSI = 2,
    P6_3_DSI_GPIO = 3,
    P6_3_AMUXA = 4,
    P6_3_AMUXB = 5,
    P6_3_AMUXA_DSI = 6,
    P6_3_AMUXB_DSI = 7,
    P6_3_TCPWM0_LINE_COMPL1 = 8,
    P6_3_TCPWM1_LINE_COMPL9 = 9,
    P6_3_CSD_CSD_TX = 10,
    P6_3_CSD_CSD_TX_N = 11,
    P6_3_LCD_COM41 = 12,
    P6_3_LCD_SEG41 = 13,
    P6_3_SCB3_UART_CTS = 18,
    P6_3_SCB3_SPI_SELECT0 = 20,
    P6_3_SCB8_SPI_SELECT0 = 30,
    P6_4_GPIO = 0,
    P6_4_GPIO_DSI = 1,
    P6_4_DSI_DSI = 2,
    P6_4_DSI_GPIO = 3,
    P6_4_AMUXA = 4,
    P6_4_AMUXB = 5,
    P6_4_AMUXA_DSI = 6,
    P6_4_AMUXB_DSI = 7,
    P6_4_TCPWM0_LINE2 = 8,
    P6_4_TCPWM1_LINE10 = 9,
    P6_4_CSD_CSD_TX = 10,
    P6_4_CSD_CSD_TX_N = 11,
    P6_4_LCD_COM42 = 12,
    P6_4_LCD_SEG42 = 13,
    P6_4_SCB8_I2C_SCL = 14,
    P6_4_SCB6_UART_RX = 18,
    P6_4_SCB6_I2C_SCL = 19,
    P6_4_SCB6_SPI_MOSI = 20,
    P6_4_PERI_TR_IO_INPUT12 = 24,
    P6_4_PERI_TR_IO_OUTPUT0 = 25,
    P6_4_CPUSS_SWJ_SWO_TDO = 29,
    P6_4_SCB8_SPI_MOSI = 30,
    P6_4_SRSS_DDFT_PIN_IN0 = 31,
    P6_5_GPIO = 0,
    P6_5_GPIO_DSI = 1,
    P6_5_DSI_DSI = 2,
    P6_5_DSI_GPIO = 3,
    P6_5_AMUXA = 4,
    P6_5_AMUXB = 5,
    P6_5_AMUXA_DSI = 6,
    P6_5_AMUXB_DSI = 7,
    P6_5_TCPWM0_LINE_COMPL2 = 8,
    P6_5_TCPWM1_LINE_COMPL10 = 9,
    P6_5_CSD_CSD_TX = 10,
    P6_5_CSD_CSD_TX_N = 11,
    P6_5_LCD_COM43 = 12,
    P6_5_LCD_SEG43 = 13,
    P6_5_SCB8_I2C_SDA = 14,
    P6_5_SCB6_UART_TX = 18,
    P6_5_SCB6_I2C_SDA = 19,
    P6_5_SCB6_SPI_MISO = 20,
    P6_5_PERI_TR_IO_INPUT13 = 24,
    P6_5_PERI_TR_IO_OUTPUT1 = 25,
    P6_5_CPUSS_SWJ_SWDOE_TDI = 29,
    P6_5_SCB8_SPI_MISO = 30,
    P6_5_SRSS_DDFT_PIN_IN1 = 31,
    P6_6_GPIO = 0,
    P6_6_GPIO_DSI = 1,
    P6_6_DSI_DSI = 2,
    P6_6_DSI_GPIO = 3,
    P6_6_AMUXA = 4,
    P6_6_AMUXB = 5,
    P6_6_AMUXA_DSI = 6,
    P6_6_AMUXB_DSI = 7,
    P6_6_TCPWM0_LINE3 = 8,
    P6_6_TCPWM1_LINE11 = 9,
    P6_6_CSD_CSD_TX = 10,
    P6_6_CSD_CSD_TX_N = 11,
    P6_6_LCD_COM44 = 12,
    P6_6_LCD_SEG44 = 13,
    P6_6_SCB6_UART_RTS = 18,
    P6_6_SCB6_SPI_CLK = 20,
    P6_6_CPUSS_SWJ_SWDIO_TMS = 29,
    P6_6_SCB8_SPI_CLK = 30,
    P6_7_GPIO = 0,
    P6_7_GPIO_DSI = 1,
    P6_7_DSI_DSI = 2,
    P6_7_DSI_GPIO = 3,
    P6_7_AMUXA = 4,
    P6_7_AMUXB = 5,
    P6_7_AMUXA_DSI = 6,
    P6_7_AMUXB_DSI = 7,
    P6_7_TCPWM0_LINE_COMPL3 = 8,
    P6_7_TCPWM1_LINE_COMPL11 = 9,
    P6_7_CSD_CSD_TX = 10,
    P6_7_CSD_CSD_TX_N = 11,
    P6_7_LCD_COM45 = 12,
    P6_7_LCD_SEG45 = 13,
    P6_7_SCB6_UART_CTS = 18,
    P6_7_SCB6_SPI_SELECT0 = 20,
    P6_7_CPUSS_SWJ_SWCLK_TCLK = 29,
    P6_7_SCB8_SPI_SELECT0 = 30,
    P7_0_GPIO = 0,
    P7_0_GPIO_DSI = 1,
    P7_0_DSI_DSI = 2,
    P7_0_DSI_GPIO = 3,
    P7_0_AMUXA = 4,
    P7_0_AMUXB = 5,
    P7_0_AMUXA_DSI = 6,
    P7_0_AMUXB_DSI = 7,
    P7_0_TCPWM0_LINE4 = 8,
    P7_0_TCPWM1_LINE12 = 9,
    P7_0_CSD_CSD_TX = 10,
    P7_0_CSD_CSD_TX_N = 11,
    P7_0_LCD_COM46 = 12,
    P7_0_LCD_SEG46 = 13,
    P7_0_SCB4_UART_RX = 18,
    P7_0_SCB4_I2C_SCL = 19,
    P7_0_SCB4_SPI_MOSI = 20,
    P7_0_PERI_TR_IO_INPUT14 = 24,
    P7_0_CPUSS_TRACE_CLOCK = 26,
    P7_1_GPIO = 0,
    P7_1_GPIO_DSI = 1,
    P7_1_DSI_DSI = 2,
    P7_1_DSI_GPIO = 3,
    P7_1_AMUXA = 4,
    P7_1_AMUXB = 5,
    P7_1_AMUXA_DSI = 6,
    P7_1_AMUXB_DSI = 7,
    P7_1_TCPWM0_LINE_COMPL4 = 8,
    P7_1_TCPWM1_LINE_COMPL12 = 9,
    P7_1_CSD_CSD_TX = 10,
    P7_1_CSD_CSD_TX_N = 11,
    P7_1_LCD_COM47 = 12,
    P7_1_LCD_SEG47 = 13,
    P7_1_SCB4_UART_TX = 18,
    P7_1_SCB4_I2C_SDA = 19,
    P7_1_SCB4_SPI_MISO = 20,
    P7_1_PERI_TR_IO_INPUT15 = 24,
    P7_2_GPIO = 0,
    P7_2_GPIO_DSI = 1,
    P7_2_DSI_DSI = 2,
    P7_2_DSI_GPIO = 3,
    P7_2_AMUXA = 4,
    P7_2_AMUXB = 5,
    P7_2_AMUXA_DSI = 6,
    P7_2_AMUXB_DSI = 7,
    P7_2_TCPWM0_LINE5 = 8,
    P7_2_TCPWM1_LINE13 = 9,
    P7_2_CSD_CSD_TX = 10,
    P7_2_CSD_CSD_TX_N = 11,
    P7_2_LCD_COM48 = 12,
    P7_2_LCD_SEG48 = 13,
    P7_2_SCB4_UART_RTS = 18,
    P7_2_SCB4_SPI_CLK = 20,
    P7_3_GPIO = 0,
    P7_3_GPIO_DSI = 1,
    P7_3_DSI_DSI = 2,
    P7_3_DSI_GPIO = 3,
    P7_3_AMUXA = 4,
    P7_3_AMUXB = 5,
    P7_3_AMUXA_DSI = 6,
    P7_3_AMUXB_DSI = 7,
    P7_3_TCPWM0_LINE_COMPL5 = 8,
    P7_3_TCPWM1_LINE_COMPL13 = 9,
    P7_3_CSD_CSD_TX = 10,
    P7_3_CSD_CSD_TX_N = 11,
    P7_3_LCD_COM49 = 12,
    P7_3_LCD_SEG49 = 13,
    P7_3_SCB4_UART_CTS = 18,
    P7_3_SCB4_SPI_SELECT0 = 20,
    P7_4_GPIO = 0,
    P7_4_GPIO_DSI = 1,
    P7_4_DSI_DSI = 2,
    P7_4_DSI_GPIO = 3,
    P7_4_AMUXA = 4,
    P7_4_AMUXB = 5,
    P7_4_AMUXA_DSI = 6,
    P7_4_AMUXB_DSI = 7,
    P7_4_TCPWM0_LINE6 = 8,
    P7_4_TCPWM1_LINE14 = 9,
    P7_4_CSD_CSD_TX = 10,
    P7_4_CSD_CSD_TX_N = 11,
    P7_4_LCD_COM50 = 12,
    P7_4_LCD_SEG50 = 13,
    P7_4_SCB4_SPI_SELECT1 = 20,
    P7_4_BLESS_EXT_LNA_RX_CTL_OUT = 26,
    P7_4_CPUSS_TRACE_DATA3 = 27,
    P7_5_GPIO = 0,
    P7_5_GPIO_DSI = 1,
    P7_5_DSI_DSI = 2,
    P7_5_DSI_GPIO = 3,
    P7_5_AMUXA = 4,
    P7_5_AMUXB = 5,
    P7_5_AMUXA_DSI = 6,
    P7_5_AMUXB_DSI = 7,
    P7_5_TCPWM0_LINE_COMPL6 = 8,
    P7_5_TCPWM1_LINE_COMPL14 = 9,
    P7_5_CSD_CSD_TX = 10,
    P7_5_CSD_CSD_TX_N = 11,
    P7_5_LCD_COM51 = 12,
    P7_5_LCD_SEG51 = 13,
    P7_5_SCB4_SPI_SELECT2 = 20,
    P7_5_BLESS_EXT_PA_TX_CTL_OUT = 26,
    P7_5_CPUSS_TRACE_DATA2 = 27,
    P7_6_GPIO = 0,
    P7_6_GPIO_DSI = 1,
    P7_6_DSI_DSI = 2,
    P7_6_DSI_GPIO = 3,
    P7_6_AMUXA = 4,
    P7_6_AMUXB = 5,
    P7_6_AMUXA_DSI = 6,
    P7_6_AMUXB_DSI = 7,
    P7_6_TCPWM0_LINE7 = 8,
    P7_6_TCPWM1_LINE15 = 9,
    P7_6_CSD_CSD_TX = 10,
    P7_6_CSD_CSD_TX_N = 11,
    P7_6_LCD_COM52 = 12,
    P7_6_LCD_SEG52 = 13,
    P7_6_SCB4_SPI_SELECT3 = 20,
    P7_6_BLESS_EXT_PA_LNA_CHIP_EN_OUT = 26,
    P7_6_CPUSS_TRACE_DATA1 = 27,
    P7_7_GPIO = 0,
    P7_7_GPIO_DSI = 1,
    P7_7_DSI_DSI = 2,
    P7_7_DSI_GPIO = 3,
    P7_7_AMUXA = 4,
    P7_7_AMUXB = 5,
    P7_7_AMUXA_DSI = 6,
    P7_7_AMUXB_DSI = 7,
    P7_7_TCPWM0_LINE_COMPL7 = 8,
    P7_7_TCPWM1_LINE_COMPL15 = 9,
    P7_7_CSD_CSD_TX = 10,
    P7_7_CSD_CSD_TX_N = 11,
    P7_7_LCD_COM53 = 12,
    P7_7_LCD_SEG53 = 13,
    P7_7_SCB3_SPI_SELECT1 = 20,
    P7_7_CPUSS_CLK_FM_PUMP = 21,
    P7_7_CPUSS_TRACE_DATA0 = 27,
    P8_0_GPIO = 0,
    P8_0_GPIO_DSI = 1,
    P8_0_DSI_DSI = 2,
    P8_0_DSI_GPIO = 3,
    P8_0_AMUXA = 4,
    P8_0_AMUXB = 5,
    P8_0_AMUXA_DSI = 6,
    P8_0_AMUXB_DSI = 7,
    P8_0_TCPWM0_LINE0 = 8,
    P8_0_TCPWM1_LINE16 = 9,
    P8_0_CSD_CSD_TX = 10,
    P8_0_CSD_CSD_TX_N = 11,
    P8_0_LCD_COM54 = 12,
    P8_0_LCD_SEG54 = 13,
    P8_0_SCB4_UART_RX = 18,
    P8_0_SCB4_I2C_SCL = 19,
    P8_0_SCB4_SPI_MOSI = 20,
    P8_0_PERI_TR_IO_INPUT16 = 24,
    P8_1_GPIO = 0,
    P8_1_GPIO_DSI = 1,
    P8_1_DSI_DSI = 2,
    P8_1_DSI_GPIO = 3,
    P8_1_AMUXA = 4,
    P8_1_AMUXB = 5,
    P8_1_AMUXA_DSI = 6,
    P8_1_AMUXB_DSI = 7,
    P8_1_TCPWM0_LINE_COMPL0 = 8,
    P8_1_TCPWM1_LINE_COMPL16 = 9,
    P8_1_CSD_CSD_TX = 10,
    P8_1_CSD_CSD_TX_N = 11,
    P8_1_LCD_COM55 = 12,
    P8_1_LCD_SEG55 = 13,
    P8_1_SCB4_UART_TX = 18,
    P8_1_SCB4_I2C_SDA = 19,
    P8_1_SCB4_SPI_MISO = 20,
    P8_1_PERI_TR_IO_INPUT17 = 24,
    P8_2_GPIO = 0,
    P8_2_GPIO_DSI = 1,
    P8_2_DSI_DSI = 2,
    P8_2_DSI_GPIO = 3,
    P8_2_AMUXA = 4,
    P8_2_AMUXB = 5,
    P8_2_AMUXA_DSI = 6,
    P8_2_AMUXB_DSI = 7,
    P8_2_TCPWM0_LINE1 = 8,
    P8_2_TCPWM1_LINE17 = 9,
    P8_2_CSD_CSD_TX = 10,
    P8_2_CSD_CSD_TX_N = 11,
    P8_2_LCD_COM56 = 12,
    P8_2_LCD_SEG56 = 13,
    P8_2_LPCOMP_DSI_COMP0 = 15,
    P8_2_SCB4_UART_RTS = 18,
    P8_2_SCB4_SPI_CLK = 20,
    P8_3_GPIO = 0,
    P8_3_GPIO_DSI = 1,
    P8_3_DSI_DSI = 2,
    P8_3_DSI_GPIO = 3,
    P8_3_AMUXA = 4,
    P8_3_AMUXB = 5,
    P8_3_AMUXA_DSI = 6,
    P8_3_AMUXB_DSI = 7,
    P8_3_TCPWM0_LINE_COMPL1 = 8,
    P8_3_TCPWM1_LINE_COMPL17 = 9,
    P8_3_CSD_CSD_TX = 10,
    P8_3_CSD_CSD_TX_N = 11,
    P8_3_LCD_COM57 = 12,
    P8_3_LCD_SEG57 = 13,
    P8_3_LPCOMP_DSI_COMP1 = 15,
    P8_3_SCB4_UART_CTS = 18,
    P8_3_SCB4_SPI_SELECT0 = 20,
    P8_4_GPIO = 0,
    P8_4_GPIO_DSI = 1,
    P8_4_DSI_DSI = 2,
    P8_4_DSI_GPIO = 3,
    P8_4_AMUXA = 4,
    P8_4_AMUXB = 5,
    P8_4_AMUXA_DSI = 6,
    P8_4_AMUXB_DSI = 7,
    P8_4_TCPWM0_LINE2 = 8,
    P8_4_TCPWM1_LINE18 = 9,
    P8_4_CSD_CSD_TX = 10,
    P8_4_CSD_CSD_TX_N = 11,
    P8_4_LCD_COM58 = 12,
    P8_4_LCD_SEG58 = 13,
    P8_4_SCB4_SPI_SELECT1 = 20,
    P8_5_GPIO = 0,
    P8_5_GPIO_DSI = 1,
    P8_5_DSI_DSI = 2,
    P8_5_DSI_GPIO = 3,
    P8_5_AMUXA = 4,
    P8_5_AMUXB = 5,
    P8_5_AMUXA_DSI = 6,
    P8_5_AMUXB_DSI = 7,
    P8_5_TCPWM0_LINE_COMPL2 = 8,
    P8_5_TCPWM1_LINE_COMPL18 = 9,
    P8_5_CSD_CSD_TX = 10,
    P8_5_CSD_CSD_TX_N = 11,
    P8_5_LCD_COM59 = 12,
    P8_5_LCD_SEG59 = 13,
    P8_5_SCB4_SPI_SELECT2 = 20,
    P8_6_GPIO = 0,
    P8_6_GPIO_DSI = 1,
    P8_6_DSI_DSI = 2,
    P8_6_DSI_GPIO = 3,
    P8_6_AMUXA = 4,
    P8_6_AMUXB = 5,
    P8_6_AMUXA_DSI = 6,
    P8_6_AMUXB_DSI = 7,
    P8_6_TCPWM0_LINE3 = 8,
    P8_6_TCPWM1_LINE19 = 9,
    P8_6_CSD_CSD_TX = 10,
    P8_6_CSD_CSD_TX_N = 11,
    P8_6_LCD_COM60 = 12,
    P8_6_LCD_SEG60 = 13,
    P8_6_SCB4_SPI_SELECT3 = 20,
    P8_7_GPIO = 0,
    P8_7_GPIO_DSI = 1,
    P8_7_DSI_DSI = 2,
    P8_7_DSI_GPIO = 3,
    P8_7_AMUXA = 4,
    P8_7_AMUXB = 5,
    P8_7_AMUXA_DSI = 6,
    P8_7_AMUXB_DSI = 7,
    P8_7_TCPWM0_LINE_COMPL3 = 8,
    P8_7_TCPWM1_LINE_COMPL19 = 9,
    P8_7_CSD_CSD_TX = 10,
    P8_7_CSD_CSD_TX_N = 11,
    P8_7_LCD_COM61 = 12,
    P8_7_LCD_SEG61 = 13,
    P8_7_SCB3_SPI_SELECT2 = 20,
    P9_0_GPIO = 0,
    P9_0_GPIO_DSI = 1,
    P9_0_DSI_DSI = 2,
    P9_0_DSI_GPIO = 3,
    P9_0_AMUXA = 4,
    P9_0_AMUXB = 5,
    P9_0_AMUXA_DSI = 6,
    P9_0_AMUXB_DSI = 7,
    P9_0_TCPWM0_LINE4 = 8,
    P9_0_TCPWM1_LINE20 = 9,
    P9_0_CSD_CSD_TX = 10,
    P9_0_CSD_CSD_TX_N = 11,
    P9_0_LCD_COM0 = 12,
    P9_0_LCD_SEG0 = 13,
    P9_0_SCB2_UART_RX = 18,
    P9_0_SCB2_I2C_SCL = 19,
    P9_0_SCB2_SPI_MOSI = 20,
    P9_0_PERI_TR_IO_INPUT18 = 24,
    P9_0_CPUSS_TRACE_DATA3 = 27,
    P9_1_GPIO = 0,
    P9_1_GPIO_DSI = 1,
    P9_1_DSI_DSI = 2,
    P9_1_DSI_GPIO = 3,
    P9_1_AMUXA = 4,
    P9_1_AMUXB = 5,
    P9_1_AMUXA_DSI = 6,
    P9_1_AMUXB_DSI = 7,
    P9_1_TCPWM0_LINE_COMPL4 = 8,
    P9_1_TCPWM1_LINE_COMPL20 = 9,
    P9_1_CSD_CSD_TX = 10,
    P9_1_CSD_CSD_TX_N = 11,
    P9_1_LCD_COM1 = 12,
    P9_1_LCD_SEG1 = 13,
    P9_1_SCB2_UART_TX = 18,
    P9_1_SCB2_I2C_SDA = 19,
    P9_1_SCB2_SPI_MISO = 20,
    P9_1_PERI_TR_IO_INPUT19 = 24,
    P9_1_CPUSS_TRACE_DATA2 = 27,
    P9_1_SRSS_DDFT_PIN_IN0 = 31,
    P9_2_GPIO = 0,
    P9_2_GPIO_DSI = 1,
    P9_2_DSI_DSI = 2,
    P9_2_DSI_GPIO = 3,
    P9_2_AMUXA = 4,
    P9_2_AMUXB = 5,
    P9_2_AMUXA_DSI = 6,
    P9_2_AMUXB_DSI = 7,
    P9_2_TCPWM0_LINE5 = 8,
    P9_2_TCPWM1_LINE21 = 9,
    P9_2_CSD_CSD_TX = 10,
    P9_2_CSD_CSD_TX_N = 11,
    P9_2_LCD_COM2 = 12,
    P9_2_LCD_SEG2 = 13,
    P9_2_SCB2_UART_RTS = 18,
    P9_2_SCB2_SPI_CLK = 20,
    P9_2_PASS_DSI_CTB_CMP0 = 22,
    P9_2_CPUSS_TRACE_DATA1 = 27,
    P9_3_GPIO = 0,
    P9_3_GPIO_DSI = 1,
    P9_3_DSI_DSI = 2,
    P9_3_DSI_GPIO = 3,
    P9_3_AMUXA = 4,
    P9_3_AMUXB = 5,
    P9_3_AMUXA_DSI = 6,
    P9_3_AMUXB_DSI = 7,
    P9_3_TCPWM0_LINE_COMPL5 = 8,
    P9_3_TCPWM1_LINE_COMPL21 = 9,
    P9_3_CSD_CSD_TX = 10,
    P9_3_CSD_CSD_TX_N = 11,
    P9_3_LCD_COM3 = 12,
    P9_3_LCD_SEG3 = 13,
    P9_3_SCB2_UART_CTS = 18,
    P9_3_SCB2_SPI_SELECT0 = 20,
    P9_3_PASS_DSI_CTB_CMP1 = 22,
    P9_3_CPUSS_TRACE_DATA0 = 27,
    P9_3_SRSS_DDFT_PIN_IN1 = 31,
    P9_4_GPIO = 0,
    P9_4_GPIO_DSI = 1,
    P9_4_DSI_DSI = 2,
    P9_4_DSI_GPIO = 3,
    P9_4_AMUXA = 4,
    P9_4_AMUXB = 5,
    P9_4_AMUXA_DSI = 6,
    P9_4_AMUXB_DSI = 7,
    P9_4_TCPWM0_LINE7 = 8,
    P9_4_TCPWM1_LINE0 = 9,
    P9_4_CSD_CSD_TX = 10,
    P9_4_CSD_CSD_TX_N = 11,
    P9_4_LCD_COM4 = 12,
    P9_4_LCD_SEG4 = 13,
    P9_4_SCB2_SPI_SELECT1 = 20,
    P9_5_GPIO = 0,
    P9_5_GPIO_DSI = 1,
    P9_5_DSI_DSI = 2,
    P9_5_DSI_GPIO = 3,
    P9_5_AMUXA = 4,
    P9_5_AMUXB = 5,
    P9_5_AMUXA_DSI = 6,
    P9_5_AMUXB_DSI = 7,
    P9_5_TCPWM0_LINE_COMPL7 = 8,
    P9_5_TCPWM1_LINE_COMPL0 = 9,
    P9_5_CSD_CSD_TX = 10,
    P9_5_CSD_CSD_TX_N = 11,
    P9_5_LCD_COM5 = 12,
    P9_5_LCD_SEG5 = 13,
    P9_5_SCB2_SPI_SELECT2 = 20,
    P9_6_GPIO = 0,
    P9_6_GPIO_DSI = 1,
    P9_6_DSI_DSI = 2,
    P9_6_DSI_GPIO = 3,
    P9_6_AMUXA = 4,
    P9_6_AMUXB = 5,
    P9_6_AMUXA_DSI = 6,
    P9_6_AMUXB_DSI = 7,
    P9_6_TCPWM0_LINE0 = 8,
    P9_6_TCPWM1_LINE1 = 9,
    P9_6_CSD_CSD_TX = 10,
    P9_6_CSD_CSD_TX_N = 11,
    P9_6_LCD_COM6 = 12,
    P9_6_LCD_SEG6 = 13,
    P9_6_SCB2_SPI_SELECT3 = 20,
    P9_7_GPIO = 0,
    P9_7_GPIO_DSI = 1,
    P9_7_DSI_DSI = 2,
    P9_7_DSI_GPIO = 3,
    P9_7_AMUXA = 4,
    P9_7_AMUXB = 5,
    P9_7_AMUXA_DSI = 6,
    P9_7_AMUXB_DSI = 7,
    P9_7_TCPWM0_LINE_COMPL0 = 8,
    P9_7_TCPWM1_LINE_COMPL1 = 9,
    P9_7_CSD_CSD_TX = 10,
    P9_7_CSD_CSD_TX_N = 11,
    P9_7_LCD_COM7 = 12,
    P9_7_LCD_SEG7 = 13,
    P10_0_GPIO = 0,
    P10_0_GPIO_DSI = 1,
    P10_0_DSI_DSI = 2,
    P10_0_DSI_GPIO = 3,
    P10_0_AMUXA = 4,
    P10_0_AMUXB = 5,
    P10_0_AMUXA_DSI = 6,
    P10_0_AMUXB_DSI = 7,
    P10_0_TCPWM0_LINE6 = 8,
    P10_0_TCPWM1_LINE22 = 9,
    P10_0_CSD_CSD_TX = 10,
    P10_0_CSD_CSD_TX_N = 11,
    P10_0_LCD_COM8 = 12,
    P10_0_LCD_SEG8 = 13,
    P10_0_SCB1_UART_RX = 18,
    P10_0_SCB1_I2C_SCL = 19,
    P10_0_SCB1_SPI_MOSI = 20,
    P10_0_PERI_TR_IO_INPUT20 = 24,
    P10_0_CPUSS_TRACE_DATA3 = 27,
    P10_1_GPIO = 0,
    P10_1_GPIO_DSI = 1,
    P10_1_DSI_DSI = 2,
    P10_1_DSI_GPIO = 3,
    P10_1_AMUXA = 4,
    P10_1_AMUXB = 5,
    P10_1_AMUXA_DSI = 6,
    P10_1_AMUXB_DSI = 7,
    P10_1_TCPWM0_LINE_COMPL6 = 8,
    P10_1_TCPWM1_LINE_COMPL22 = 9,
    P10_1_CSD_CSD_TX = 10,
    P10_1_CSD_CSD_TX_N = 11,
    P10_1_LCD_COM9 = 12,
    P10_1_LCD_SEG9 = 13,
    P10_1_SCB1_UART_TX = 18,
    P10_1_SCB1_I2C_SDA = 19,
    P10_1_SCB1_SPI_MISO = 20,
    P10_1_PERI_TR_IO_INPUT21 = 24,
    P10_1_CPUSS_TRACE_DATA2 = 27,
    P10_2_GPIO = 0,
    P10_2_GPIO_DSI = 1,
    P10_2_DSI_DSI = 2,
    P10_2_DSI_GPIO = 3,
    P10_2_AMUXA = 4,
    P10_2_AMUXB = 5,
    P10_2_AMUXA_DSI = 6,
    P10_2_AMUXB_DSI = 7,
    P10_2_TCPWM0_LINE7 = 8,
    P10_2_TCPWM1_LINE23 = 9,
    P10_2_CSD_CSD_TX = 10,
    P10_2_CSD_CSD_TX_N = 11,
    P10_2_LCD_COM10 = 12,
    P10_2_LCD_SEG10 = 13,
    P10_2_SCB1_UART_RTS = 18,
    P10_2_SCB1_SPI_CLK = 20,
    P10_2_CPUSS_TRACE_DATA1 = 27,
    P10_3_GPIO = 0,
    P10_3_GPIO_DSI = 1,
    P10_3_DSI_DSI = 2,
    P10_3_DSI_GPIO = 3,
    P10_3_AMUXA = 4,
    P10_3_AMUXB = 5,
    P10_3_AMUXA_DSI = 6,
    P10_3_AMUXB_DSI = 7,
    P10_3_TCPWM0_LINE_COMPL7 = 8,
    P10_3_TCPWM1_LINE_COMPL23 = 9,
    P10_3_CSD_CSD_TX = 10,
    P10_3_CSD_CSD_TX_N = 11,
    P10_3_LCD_COM11 = 12,
    P10_3_LCD_SEG11 = 13,
    P10_3_SCB1_UART_CTS = 18,
    P10_3_SCB1_SPI_SELECT0 = 20,
    P10_3_CPUSS_TRACE_DATA0 = 27,
    P10_4_GPIO = 0,
    P10_4_GPIO_DSI = 1,
    P10_4_DSI_DSI = 2,
    P10_4_DSI_GPIO = 3,
    P10_4_AMUXA = 4,
    P10_4_AMUXB = 5,
    P10_4_AMUXA_DSI = 6,
    P10_4_AMUXB_DSI = 7,
    P10_4_TCPWM0_LINE0 = 8,
    P10_4_TCPWM1_LINE0 = 9,
    P10_4_CSD_CSD_TX = 10,
    P10_4_CSD_CSD_TX_N = 11,
    P10_4_LCD_COM12 = 12,
    P10_4_LCD_SEG12 = 13,
    P10_4_SCB1_SPI_SELECT1 = 20,
    P10_4_AUDIOSS_PDM_CLK = 21,
    P10_4_AUDIOSS0_PDM_CLK = 21,
    P10_5_GPIO = 0,
    P10_5_GPIO_DSI = 1,
    P10_5_DSI_DSI = 2,
    P10_5_DSI_GPIO = 3,
    P10_5_AMUXA = 4,
    P10_5_AMUXB = 5,
    P10_5_AMUXA_DSI = 6,
    P10_5_AMUXB_DSI = 7,
    P10_5_TCPWM0_LINE_COMPL0 = 8,
    P10_5_TCPWM1_LINE_COMPL0 = 9,
    P10_5_CSD_CSD_TX = 10,
    P10_5_CSD_CSD_TX_N = 11,
    P10_5_LCD_COM13 = 12,
    P10_5_LCD_SEG13 = 13,
    P10_5_SCB1_SPI_SELECT2 = 20,
    P10_5_AUDIOSS_PDM_DATA = 21,
    P10_5_AUDIOSS0_PDM_DATA = 21,
    P10_6_GPIO = 0,
    P10_6_GPIO_DSI = 1,
    P10_6_DSI_DSI = 2,
    P10_6_DSI_GPIO = 3,
    P10_6_AMUXA = 4,
    P10_6_AMUXB = 5,
    P10_6_AMUXA_DSI = 6,
    P10_6_AMUXB_DSI = 7,
    P10_6_TCPWM0_LINE1 = 8,
    P10_6_TCPWM1_LINE2 = 9,
    P10_6_CSD_CSD_TX = 10,
    P10_6_CSD_CSD_TX_N = 11,
    P10_6_LCD_COM14 = 12,
    P10_6_LCD_SEG14 = 13,
    P10_6_SCB1_SPI_SELECT3 = 20,
    P11_0_GPIO = 0,
    P11_0_GPIO_DSI = 1,
    P11_0_DSI_DSI = 2,
    P11_0_DSI_GPIO = 3,
    P11_0_AMUXA = 4,
    P11_0_AMUXB = 5,
    P11_0_AMUXA_DSI = 6,
    P11_0_AMUXB_DSI = 7,
    P11_0_TCPWM0_LINE1 = 8,
    P11_0_TCPWM1_LINE1 = 9,
    P11_0_CSD_CSD_TX = 10,
    P11_0_CSD_CSD_TX_N = 11,
    P11_0_LCD_COM16 = 12,
    P11_0_LCD_SEG16 = 13,
    P11_0_SMIF_SPI_SELECT2 = 17,
    P11_0_SCB5_UART_RX = 18,
    P11_0_SCB5_I2C_SCL = 19,
    P11_0_SCB5_SPI_MOSI = 20,
    P11_0_PERI_TR_IO_INPUT22 = 24,
    P11_1_GPIO = 0,
    P11_1_GPIO_DSI = 1,
    P11_1_DSI_DSI = 2,
    P11_1_DSI_GPIO = 3,
    P11_1_AMUXA = 4,
    P11_1_AMUXB = 5,
    P11_1_AMUXA_DSI = 6,
    P11_1_AMUXB_DSI = 7,
    P11_1_TCPWM0_LINE_COMPL1 = 8,
    P11_1_TCPWM1_LINE_COMPL1 = 9,
    P11_1_CSD_CSD_TX = 10,
    P11_1_CSD_CSD_TX_N = 11,
    P11_1_LCD_COM17 = 12,
    P11_1_LCD_SEG17 = 13,
    P11_1_SMIF_SPI_SELECT1 = 17,
    P11_1_SCB5_UART_TX = 18,
    P11_1_SCB5_I2C_SDA = 19,
    P11_1_SCB5_SPI_MISO = 20,
    P11_1_PERI_TR_IO_INPUT23 = 24,
    P11_2_GPIO = 0,
    P11_2_GPIO_DSI = 1,
    P11_2_DSI_DSI = 2,
    P11_2_DSI_GPIO = 3,
    P11_2_AMUXA = 4,
    P11_2_AMUXB = 5,
    P11_2_AMUXA_DSI = 6,
    P11_2_AMUXB_DSI = 7,
    P11_2_TCPWM0_LINE2 = 8,
    P11_2_TCPWM1_LINE2 = 9,
    P11_2_CSD_CSD_TX = 10,
    P11_2_CSD_CSD_TX_N = 11,
    P11_2_LCD_COM18 = 12,
    P11_2_LCD_SEG18 = 13,
    P11_2_SMIF_SPI_SELECT0 = 17,
    P11_2_SCB5_UART_RTS = 18,
    P11_2_SCB5_SPI_CLK = 20,
    P11_3_GPIO = 0,
    P11_3_GPIO_DSI = 1,
    P11_3_DSI_DSI = 2,
    P11_3_DSI_GPIO = 3,
    P11_3_AMUXA = 4,
    P11_3_AMUXB = 5,
    P11_3_AMUXA_DSI = 6,
    P11_3_AMUXB_DSI = 7,
    P11_3_TCPWM0_LINE_COMPL2 = 8,
    P11_3_TCPWM1_LINE_COMPL2 = 9,
    P11_3_CSD_CSD_TX = 10,
    P11_3_CSD_CSD_TX_N = 11,
    P11_3_LCD_COM19 = 12,
    P11_3_LCD_SEG19 = 13,
    P11_3_SMIF_SPI_DATA3 = 17,
    P11_3_SCB5_UART_CTS = 18,
    P11_3_SCB5_SPI_SELECT0 = 20,
    P11_3_PERI_TR_IO_OUTPUT0 = 25,
    P11_4_GPIO = 0,
    P11_4_GPIO_DSI = 1,
    P11_4_DSI_DSI = 2,
    P11_4_DSI_GPIO = 3,
    P11_4_AMUXA = 4,
    P11_4_AMUXB = 5,
    P11_4_AMUXA_DSI = 6,
    P11_4_AMUXB_DSI = 7,
    P11_4_TCPWM0_LINE3 = 8,
    P11_4_TCPWM1_LINE3 = 9,
    P11_4_CSD_CSD_TX = 10,
    P11_4_CSD_CSD_TX_N = 11,
    P11_4_LCD_COM20 = 12,
    P11_4_LCD_SEG20 = 13,
    P11_4_SMIF_SPI_DATA2 = 17,
    P11_4_SCB5_SPI_SELECT1 = 20,
    P11_4_PERI_TR_IO_OUTPUT1 = 25,
    P11_5_GPIO = 0,
    P11_5_GPIO_DSI = 1,
    P11_5_DSI_DSI = 2,
    P11_5_DSI_GPIO = 3,
    P11_5_AMUXA = 4,
    P11_5_AMUXB = 5,
    P11_5_AMUXA_DSI = 6,
    P11_5_AMUXB_DSI = 7,
    P11_5_TCPWM0_LINE_COMPL3 = 8,
    P11_5_TCPWM1_LINE_COMPL3 = 9,
    P11_5_CSD_CSD_TX = 10,
    P11_5_CSD_CSD_TX_N = 11,
    P11_5_LCD_COM21 = 12,
    P11_5_LCD_SEG21 = 13,
    P11_5_SMIF_SPI_DATA1 = 17,
    P11_5_SCB5_SPI_SELECT2 = 20,
    P11_6_GPIO = 0,
    P11_6_GPIO_DSI = 1,
    P11_6_DSI_DSI = 2,
    P11_6_DSI_GPIO = 3,
    P11_6_AMUXA = 4,
    P11_6_AMUXB = 5,
    P11_6_AMUXA_DSI = 6,
    P11_6_AMUXB_DSI = 7,
    P11_6_CSD_CSD_TX = 10,
    P11_6_CSD_CSD_TX_N = 11,
    P11_6_LCD_COM22 = 12,
    P11_6_LCD_SEG22 = 13,
    P11_6_SMIF_SPI_DATA0 = 17,
    P11_6_SCB5_SPI_SELECT3 = 20,
    P11_7_GPIO = 0,
    P11_7_GPIO_DSI = 1,
    P11_7_DSI_DSI = 2,
    P11_7_DSI_GPIO = 3,
    P11_7_AMUXA = 4,
    P11_7_AMUXB = 5,
    P11_7_AMUXA_DSI = 6,
    P11_7_AMUXB_DSI = 7,
    P11_7_SMIF_SPI_CLK = 17,
    P12_0_GPIO = 0,
    P12_0_GPIO_DSI = 1,
    P12_0_DSI_DSI = 2,
    P12_0_DSI_GPIO = 3,
    P12_0_AMUXA = 4,
    P12_0_AMUXB = 5,
    P12_0_AMUXA_DSI = 6,
    P12_0_AMUXB_DSI = 7,
    P12_0_TCPWM0_LINE4 = 8,
    P12_0_TCPWM1_LINE4 = 9,
    P12_0_CSD_CSD_TX = 10,
    P12_0_CSD_CSD_TX_N = 11,
    P12_0_LCD_COM23 = 12,
    P12_0_LCD_SEG23 = 13,
    P12_0_SMIF_SPI_DATA4 = 17,
    P12_0_SCB6_UART_RX = 18,
    P12_0_SCB6_I2C_SCL = 19,
    P12_0_SCB6_SPI_MOSI = 20,
    P12_0_PERI_TR_IO_INPUT24 = 24,
    P12_1_GPIO = 0,
    P12_1_GPIO_DSI = 1,
    P12_1_DSI_DSI = 2,
    P12_1_DSI_GPIO = 3,
    P12_1_AMUXA = 4,
    P12_1_AMUXB = 5,
    P12_1_AMUXA_DSI = 6,
    P12_1_AMUXB_DSI = 7,
    P12_1_TCPWM0_LINE_COMPL4 = 8,
    P12_1_TCPWM1_LINE_COMPL4 = 9,
    P12_1_CSD_CSD_TX = 10,
    P12_1_CSD_CSD_TX_N = 11,
    P12_1_LCD_COM24 = 12,
    P12_1_LCD_SEG24 = 13,
    P12_1_SMIF_SPI_DATA5 = 17,
    P12_1_SCB6_UART_TX = 18,
    P12_1_SCB6_I2C_SDA = 19,
    P12_1_SCB6_SPI_MISO = 20,
    P12_1_PERI_TR_IO_INPUT25 = 24,
    P12_2_GPIO = 0,
    P12_2_GPIO_DSI = 1,
    P12_2_DSI_DSI = 2,
    P12_2_DSI_GPIO = 3,
    P12_2_AMUXA = 4,
    P12_2_AMUXB = 5,
    P12_2_AMUXA_DSI = 6,
    P12_2_AMUXB_DSI = 7,
    P12_2_TCPWM0_LINE5 = 8,
    P12_2_TCPWM1_LINE5 = 9,
    P12_2_CSD_CSD_TX = 10,
    P12_2_CSD_CSD_TX_N = 11,
    P12_2_LCD_COM25 = 12,
    P12_2_LCD_SEG25 = 13,
    P12_2_SMIF_SPI_DATA6 = 17,
    P12_2_SCB6_UART_RTS = 18,
    P12_2_SCB6_SPI_CLK = 20,
    P12_3_GPIO = 0,
    P12_3_GPIO_DSI = 1,
    P12_3_DSI_DSI = 2,
    P12_3_DSI_GPIO = 3,
    P12_3_AMUXA = 4,
    P12_3_AMUXB = 5,
    P12_3_AMUXA_DSI = 6,
    P12_3_AMUXB_DSI = 7,
    P12_3_TCPWM0_LINE_COMPL5 = 8,
    P12_3_TCPWM1_LINE_COMPL5 = 9,
    P12_3_CSD_CSD_TX = 10,
    P12_3_CSD_CSD_TX_N = 11,
    P12_3_LCD_COM26 = 12,
    P12_3_LCD_SEG26 = 13,
    P12_3_SMIF_SPI_DATA7 = 17,
    P12_3_SCB6_UART_CTS = 18,
    P12_3_SCB6_SPI_SELECT0 = 20,
    P12_4_GPIO = 0,
    P12_4_GPIO_DSI = 1,
    P12_4_DSI_DSI = 2,
    P12_4_DSI_GPIO = 3,
    P12_4_AMUXA = 4,
    P12_4_AMUXB = 5,
    P12_4_AMUXA_DSI = 6,
    P12_4_AMUXB_DSI = 7,
    P12_4_TCPWM0_LINE6 = 8,
    P12_4_TCPWM1_LINE6 = 9,
    P12_4_CSD_CSD_TX = 10,
    P12_4_CSD_CSD_TX_N = 11,
    P12_4_LCD_COM27 = 12,
    P12_4_LCD_SEG27 = 13,
    P12_4_SMIF_SPI_SELECT3 = 17,
    P12_4_SCB6_SPI_SELECT1 = 20,
    P12_4_AUDIOSS_PDM_CLK = 21,
    P12_4_AUDIOSS0_PDM_CLK = 21,
    P12_5_GPIO = 0,
    P12_5_GPIO_DSI = 1,
    P12_5_DSI_DSI = 2,
    P12_5_DSI_GPIO = 3,
    P12_5_AMUXA = 4,
    P12_5_AMUXB = 5,
    P12_5_AMUXA_DSI = 6,
    P12_5_AMUXB_DSI = 7,
    P12_5_TCPWM0_LINE_COMPL6 = 8,
    P12_5_TCPWM1_LINE_COMPL6 = 9,
    P12_5_CSD_CSD_TX = 10,
    P12_5_CSD_CSD_TX_N = 11,
    P12_5_LCD_COM28 = 12,
    P12_5_LCD_SEG28 = 13,
    P12_5_SCB6_SPI_SELECT2 = 20,
    P12_5_AUDIOSS_PDM_DATA = 21,
    P12_5_AUDIOSS0_PDM_DATA = 21,
    P12_6_GPIO = 0,
    P12_6_GPIO_DSI = 1,
    P12_6_DSI_DSI = 2,
    P12_6_DSI_GPIO = 3,
    P12_6_AMUXA = 4,
    P12_6_AMUXB = 5,
    P12_6_AMUXA_DSI = 6,
    P12_6_AMUXB_DSI = 7,
    P12_6_TCPWM0_LINE7 = 8,
    P12_6_TCPWM1_LINE7 = 9,
    P12_6_CSD_CSD_TX = 10,
    P12_6_CSD_CSD_TX_N = 11,
    P12_6_LCD_COM29 = 12,
    P12_6_LCD_SEG29 = 13,
    P12_6_SCB6_SPI_SELECT3 = 20,
    P12_7_GPIO = 0,
    P12_7_GPIO_DSI = 1,
    P12_7_DSI_DSI = 2,
    P12_7_DSI_GPIO = 3,
    P12_7_AMUXA = 4,
    P12_7_AMUXB = 5,
    P12_7_AMUXA_DSI = 6,
    P12_7_AMUXB_DSI = 7,
    P12_7_TCPWM0_LINE_COMPL7 = 8,
    P12_7_TCPWM1_LINE_COMPL7 = 9,
    P12_7_CSD_CSD_TX = 10,
    P12_7_CSD_CSD_TX_N = 11,
    P12_7_LCD_COM30 = 12,
    P12_7_LCD_SEG30 = 13,
    P13_0_GPIO = 0,
    P13_0_GPIO_DSI = 1,
    P13_0_DSI_DSI = 2,
    P13_0_DSI_GPIO = 3,
    P13_0_AMUXA = 4,
    P13_0_AMUXB = 5,
    P13_0_AMUXA_DSI = 6,
    P13_0_AMUXB_DSI = 7,
    P13_0_TCPWM0_LINE0 = 8,
    P13_0_TCPWM1_LINE8 = 9,
    P13_0_CSD_CSD_TX = 10,
    P13_0_CSD_CSD_TX_N = 11,
    P13_0_LCD_COM31 = 12,
    P13_0_LCD_SEG31 = 13,
    P13_0_SCB6_UART_RX = 18,
    P13_0_SCB6_I2C_SCL = 19,
    P13_0_SCB6_SPI_MOSI = 20,
    P13_0_PERI_TR_IO_INPUT26 = 24,
    P13_1_GPIO = 0,
    P13_1_GPIO_DSI = 1,
    P13_1_DSI_DSI = 2,
    P13_1_DSI_GPIO = 3,
    P13_1_AMUXA = 4,
    P13_1_AMUXB = 5,
    P13_1_AMUXA_DSI = 6,
    P13_1_AMUXB_DSI = 7,
    P13_1_TCPWM0_LINE_COMPL0 = 8,
    P13_1_TCPWM1_LINE_COMPL8 = 9,
    P13_1_CSD_CSD_TX = 10,
    P13_1_CSD_CSD_TX_N = 11,
    P13_1_LCD_COM32 = 12,
    P13_1_LCD_SEG32 = 13,
    P13_1_SCB6_UART_TX = 18,
    P13_1_SCB6_I2C_SDA = 19,
    P13_1_SCB6_SPI_MISO = 20,
    P13_1_PERI_TR_IO_INPUT27 = 24,
    P13_6_GPIO = 0,
    P13_6_GPIO_DSI = 1,
    P13_6_DSI_DSI = 2,
    P13_6_DSI_GPIO = 3,
    P13_6_AMUXA = 4,
    P13_6_AMUXB = 5,
    P13_6_AMUXA_DSI = 6,
    P13_6_AMUXB_DSI = 7,
    P13_6_TCPWM0_LINE3 = 8,
    P13_6_TCPWM1_LINE11 = 9,
    P13_6_CSD_CSD_TX = 10,
    P13_6_CSD_CSD_TX_N = 11,
    P13_6_LCD_COM37 = 12,
    P13_6_LCD_SEG37 = 13,
    P13_6_SCB6_SPI_SELECT3 = 20,
    P13_7_GPIO = 0,
    P13_7_GPIO_DSI = 1,
    P13_7_DSI_DSI = 2,
    P13_7_DSI_GPIO = 3,
    P13_7_AMUXA = 4,
    P13_7_AMUXB = 5,
    P13_7_AMUXA_DSI = 6,
    P13_7_AMUXB_DSI = 7,
    P13_7_TCPWM0_LINE_COMPL3 = 8,
    P13_7_TCPWM1_LINE_COMPL11 = 9,
    P13_7_CSD_CSD_TX = 10,
    P13_7_CSD_CSD_TX_N = 11,
    P13_7_LCD_COM38 = 12,
    P13_7_LCD_SEG38 = 13
} en_hsiom_sel_t;
typedef struct {
   volatile const uint32_t IDENTITY;
   volatile const uint32_t CM4_STATUS;
  volatile uint32_t CM4_CLOCK_CTL;
  volatile uint32_t CM4_CTL;
   volatile const uint32_t RESERVED[60];
   volatile const uint32_t CM4_INT0_STATUS;
   volatile const uint32_t CM4_INT1_STATUS;
   volatile const uint32_t CM4_INT2_STATUS;
   volatile const uint32_t CM4_INT3_STATUS;
   volatile const uint32_t CM4_INT4_STATUS;
   volatile const uint32_t CM4_INT5_STATUS;
   volatile const uint32_t CM4_INT6_STATUS;
   volatile const uint32_t CM4_INT7_STATUS;
   volatile const uint32_t RESERVED1[56];
  volatile uint32_t CM4_VECTOR_TABLE_BASE;
   volatile const uint32_t RESERVED2[15];
  volatile uint32_t CM4_NMI_CTL[4];
   volatile const uint32_t RESERVED3[44];
  volatile uint32_t UDB_PWR_CTL;
  volatile uint32_t UDB_PWR_DELAY_CTL;
   volatile const uint32_t RESERVED4[830];
  volatile uint32_t CM0_CTL;
   volatile const uint32_t CM0_STATUS;
  volatile uint32_t CM0_CLOCK_CTL;
   volatile const uint32_t RESERVED5[61];
   volatile const uint32_t CM0_INT0_STATUS;
   volatile const uint32_t CM0_INT1_STATUS;
   volatile const uint32_t CM0_INT2_STATUS;
   volatile const uint32_t CM0_INT3_STATUS;
   volatile const uint32_t CM0_INT4_STATUS;
   volatile const uint32_t CM0_INT5_STATUS;
   volatile const uint32_t CM0_INT6_STATUS;
   volatile const uint32_t CM0_INT7_STATUS;
  volatile uint32_t CM0_VECTOR_TABLE_BASE;
   volatile const uint32_t RESERVED6[7];
  volatile uint32_t CM0_NMI_CTL[4];
   volatile const uint32_t RESERVED7[44];
  volatile uint32_t CM4_PWR_CTL;
  volatile uint32_t CM4_PWR_DELAY_CTL;
   volatile const uint32_t RESERVED8[62];
  volatile uint32_t RAM0_CTL0;
   volatile const uint32_t RAM0_STATUS;
   volatile const uint32_t RESERVED9[14];
  volatile uint32_t RAM0_PWR_MACRO_CTL[16];
  volatile uint32_t RAM1_CTL0;
   volatile const uint32_t RAM1_STATUS;
  volatile uint32_t RAM1_PWR_CTL;
   volatile const uint32_t RESERVED10[5];
  volatile uint32_t RAM2_CTL0;
   volatile const uint32_t RAM2_STATUS;
  volatile uint32_t RAM2_PWR_CTL;
   volatile const uint32_t RESERVED11[5];
  volatile uint32_t RAM_PWR_DELAY_CTL;
  volatile uint32_t ROM_CTL;
  volatile uint32_t ECC_CTL;
   volatile const uint32_t RESERVED12[13];
   volatile const uint32_t PRODUCT_ID;
   volatile const uint32_t RESERVED13[3];
   volatile const uint32_t DP_STATUS;
  volatile uint32_t AP_CTL;
   volatile const uint32_t RESERVED14[58];
  volatile uint32_t BUFF_CTL;
   volatile const uint32_t RESERVED15[63];
  volatile uint32_t SYSTICK_CTL;
   volatile const uint32_t RESERVED16[64];
   volatile const uint32_t MBIST_STAT;
   volatile const uint32_t RESERVED17[62];
  volatile uint32_t CAL_SUP_SET;
  volatile uint32_t CAL_SUP_CLR;
   volatile const uint32_t RESERVED18[510];
  volatile uint32_t CM0_PC_CTL;
   volatile const uint32_t RESERVED19[15];
  volatile uint32_t CM0_PC0_HANDLER;
  volatile uint32_t CM0_PC1_HANDLER;
  volatile uint32_t CM0_PC2_HANDLER;
  volatile uint32_t CM0_PC3_HANDLER;
   volatile const uint32_t RESERVED20[29];
  volatile uint32_t PROTECTION;
   volatile const uint32_t RESERVED21[14];
  volatile uint32_t TRIM_ROM_CTL;
  volatile uint32_t TRIM_RAM_CTL;
   volatile const uint32_t RESERVED22[6078];
  volatile uint32_t CM0_SYSTEM_INT_CTL[1023];
   volatile const uint32_t RESERVED23[1025];
  volatile uint32_t CM4_SYSTEM_INT_CTL[1023];
} CPUSS_V2_Type;
typedef struct {
  volatile uint32_t FM_CTL;
   volatile const uint32_t STATUS;
  volatile uint32_t FM_ADDR;
  volatile uint32_t BOOKMARK;
   volatile const uint32_t GEOMETRY;
   volatile const uint32_t GEOMETRY_SUPERVISORY;
  volatile uint32_t ANA_CTL0;
  volatile uint32_t ANA_CTL1;
   volatile const uint32_t RESERVED[2];
  volatile uint32_t WAIT_CTL;
   volatile const uint32_t RESERVED1[2];
  volatile uint32_t TIMER_CLK_CTL;
  volatile uint32_t TIMER_CTL;
   volatile uint32_t ACLK_CTL;
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
  volatile uint32_t CAL_CTL0;
  volatile uint32_t CAL_CTL1;
  volatile uint32_t CAL_CTL2;
  volatile uint32_t CAL_CTL3;
  volatile uint32_t CAL_CTL4;
  volatile uint32_t CAL_CTL5;
  volatile uint32_t CAL_CTL6;
  volatile uint32_t CAL_CTL7;
   volatile const uint32_t RESERVED2[4];
  volatile uint32_t RED_CTL01;
  volatile uint32_t RED_CTL23;
  volatile uint32_t RED_CTL45;
  volatile uint32_t RED_CTL67;
  volatile uint32_t RED_CTL_SM01;
   volatile const uint32_t RESERVED3;
  volatile uint32_t RGRANT_DELAY_PRG;
   volatile const uint32_t RESERVED4;
  volatile uint32_t PW_SEQ12;
  volatile uint32_t PW_SEQ23;
  volatile uint32_t RGRANT_SCALE_ERS;
  volatile uint32_t RGRANT_DELAY_ERS;
   volatile const uint32_t RESERVED5[467];
  volatile uint32_t FM_PL_WRDATA_ALL;
  volatile uint32_t FM_PL_DATA[256];
   volatile const uint32_t FM_MEM_DATA[256];
} FLASHC_FM_CTL_V2_Type;
typedef struct {
  volatile uint32_t FLASH_CTL;
  volatile uint32_t FLASH_PWR_CTL;
  volatile uint32_t FLASH_CMD;
   volatile const uint32_t RESERVED[165];
  volatile uint32_t ECC_CTL;
   volatile const uint32_t RESERVED1[3];
  volatile uint32_t FM_SRAM_ECC_CTL0;
  volatile uint32_t FM_SRAM_ECC_CTL1;
   volatile const uint32_t FM_SRAM_ECC_CTL2;
  volatile uint32_t FM_SRAM_ECC_CTL3;
   volatile const uint32_t RESERVED2[80];
  volatile uint32_t CM0_CA_CTL0;
  volatile uint32_t CM0_CA_CTL1;
  volatile uint32_t CM0_CA_CTL2;
   volatile const uint32_t RESERVED3[13];
   volatile const uint32_t CM0_CA_STATUS0;
   volatile const uint32_t CM0_CA_STATUS1;
   volatile const uint32_t CM0_CA_STATUS2;
   volatile const uint32_t RESERVED4[5];
  volatile uint32_t CM0_STATUS;
   volatile const uint32_t RESERVED5[7];
  volatile uint32_t CM4_CA_CTL0;
  volatile uint32_t CM4_CA_CTL1;
  volatile uint32_t CM4_CA_CTL2;
   volatile const uint32_t RESERVED6[13];
   volatile const uint32_t CM4_CA_STATUS0;
   volatile const uint32_t CM4_CA_STATUS1;
   volatile const uint32_t CM4_CA_STATUS2;
   volatile const uint32_t RESERVED7[5];
  volatile uint32_t CM4_STATUS;
   volatile const uint32_t RESERVED8[7];
  volatile uint32_t CRYPTO_BUFF_CTL;
   volatile const uint32_t RESERVED9[31];
  volatile uint32_t DW0_BUFF_CTL;
   volatile const uint32_t RESERVED10[31];
  volatile uint32_t DW1_BUFF_CTL;
   volatile const uint32_t RESERVED11[31];
  volatile uint32_t DMAC_BUFF_CTL;
   volatile const uint32_t RESERVED12[31];
  volatile uint32_t EXT_MS0_BUFF_CTL;
   volatile const uint32_t RESERVED13[31];
  volatile uint32_t EXT_MS1_BUFF_CTL;
   volatile const uint32_t RESERVED14[14879];
        FLASHC_FM_CTL_V2_Type FM_CTL;
} FLASHC_V2_Type;
typedef struct {
  volatile uint32_t OUT;
  volatile uint32_t OUT_CLR;
  volatile uint32_t OUT_SET;
  volatile uint32_t OUT_INV;
   volatile const uint32_t IN;
  volatile uint32_t INTR;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
  volatile uint32_t INTR_SET;
   volatile const uint32_t RESERVED[7];
  volatile uint32_t INTR_CFG;
  volatile uint32_t CFG;
  volatile uint32_t CFG_IN;
  volatile uint32_t CFG_OUT;
  volatile uint32_t CFG_SIO;
   volatile const uint32_t RESERVED1;
  volatile uint32_t CFG_IN_AUTOLVL;
   volatile const uint32_t RESERVED2[9];
} GPIO_PRT_V2_Type;
typedef struct {
        GPIO_PRT_V2_Type PRT[128];
   volatile const uint32_t INTR_CAUSE0;
   volatile const uint32_t INTR_CAUSE1;
   volatile const uint32_t INTR_CAUSE2;
   volatile const uint32_t INTR_CAUSE3;
   volatile const uint32_t VDD_ACTIVE;
  volatile uint32_t VDD_INTR;
  volatile uint32_t VDD_INTR_MASK;
   volatile const uint32_t VDD_INTR_MASKED;
  volatile uint32_t VDD_INTR_SET;
} GPIO_V2_Type;
typedef struct {
  volatile uint32_t PORT_SEL0;
  volatile uint32_t PORT_SEL1;
   volatile const uint32_t RESERVED[2];
} HSIOM_PRT_V2_Type;
typedef struct {
        HSIOM_PRT_V2_Type PRT[128];
   volatile const uint32_t RESERVED[1536];
  volatile uint32_t AMUX_SPLIT_CTL[64];
   volatile const uint32_t RESERVED1[64];
  volatile uint32_t MONITOR_CTL_0;
  volatile uint32_t MONITOR_CTL_1;
  volatile uint32_t MONITOR_CTL_2;
  volatile uint32_t MONITOR_CTL_3;
   volatile const uint32_t RESERVED2[12];
  volatile uint32_t ALT_JTAG_EN;
} HSIOM_V2_Type;
typedef struct {
  volatile uint32_t CLOCK_CTL;
   volatile const uint32_t RESERVED[3];
  volatile uint32_t SL_CTL;
   volatile const uint32_t RESERVED1[3];
} PERI_GR_V2_Type;
typedef struct {
  volatile uint32_t TR_CTL[256];
} PERI_TR_GR_V2_Type;
typedef struct {
  volatile uint32_t TR_CTL[256];
} PERI_TR_1TO1_GR_V2_Type;
typedef struct {
   volatile const uint32_t RESERVED[128];
  volatile uint32_t TIMEOUT_CTL;
   volatile const uint32_t RESERVED1[7];
  volatile uint32_t TR_CMD;
   volatile const uint32_t RESERVED2[119];
  volatile uint32_t DIV_CMD;
   volatile const uint32_t RESERVED3[511];
  volatile uint32_t CLOCK_CTL[256];
  volatile uint32_t DIV_8_CTL[256];
  volatile uint32_t DIV_16_CTL[256];
  volatile uint32_t DIV_16_5_CTL[256];
  volatile uint32_t DIV_24_5_CTL[255];
   volatile const uint32_t RESERVED4;
  volatile uint32_t ECC_CTL;
   volatile const uint32_t RESERVED5[2047];
        PERI_GR_V2_Type GR[16];
   volatile const uint32_t RESERVED6[3968];
        PERI_TR_GR_V2_Type TR_GR[16];
        PERI_TR_1TO1_GR_V2_Type TR_1TO1_GR[16];
} PERI_V2_Type;
typedef struct {
  volatile uint32_t SL_ADDR;
  volatile uint32_t SL_SIZE;
   volatile const uint32_t RESERVED[2];
  volatile uint32_t SL_ATT0;
  volatile uint32_t SL_ATT1;
  volatile uint32_t SL_ATT2;
  volatile uint32_t SL_ATT3;
   volatile const uint32_t MS_ADDR;
   volatile const uint32_t MS_SIZE;
   volatile const uint32_t RESERVED1[2];
  volatile uint32_t MS_ATT0;
  volatile uint32_t MS_ATT1;
  volatile uint32_t MS_ATT2;
  volatile uint32_t MS_ATT3;
} PERI_MS_PPU_PR_V2_Type;
typedef struct {
   volatile const uint32_t SL_ADDR;
   volatile const uint32_t SL_SIZE;
   volatile const uint32_t RESERVED[2];
  volatile uint32_t SL_ATT0;
  volatile uint32_t SL_ATT1;
  volatile uint32_t SL_ATT2;
  volatile uint32_t SL_ATT3;
   volatile const uint32_t MS_ADDR;
   volatile const uint32_t MS_SIZE;
   volatile const uint32_t RESERVED1[2];
  volatile uint32_t MS_ATT0;
  volatile uint32_t MS_ATT1;
  volatile uint32_t MS_ATT2;
  volatile uint32_t MS_ATT3;
} PERI_MS_PPU_FX_V2_Type;
typedef struct {
        PERI_MS_PPU_PR_V2_Type PPU_PR[32];
        PERI_MS_PPU_FX_V2_Type PPU_FX[992];
} PERI_MS_V2_Type;
typedef struct {
  volatile uint32_t ADDR0;
  volatile uint32_t ATT0;
   volatile const uint32_t RESERVED[6];
   volatile const uint32_t ADDR1;
  volatile uint32_t ATT1;
   volatile const uint32_t RESERVED1[6];
} PROT_SMPU_SMPU_STRUCT_V2_Type;
typedef struct {
  volatile uint32_t MS0_CTL;
  volatile uint32_t MS1_CTL;
  volatile uint32_t MS2_CTL;
  volatile uint32_t MS3_CTL;
  volatile uint32_t MS4_CTL;
  volatile uint32_t MS5_CTL;
  volatile uint32_t MS6_CTL;
  volatile uint32_t MS7_CTL;
  volatile uint32_t MS8_CTL;
  volatile uint32_t MS9_CTL;
  volatile uint32_t MS10_CTL;
  volatile uint32_t MS11_CTL;
  volatile uint32_t MS12_CTL;
  volatile uint32_t MS13_CTL;
  volatile uint32_t MS14_CTL;
  volatile uint32_t MS15_CTL;
   volatile const uint32_t RESERVED[2032];
        PROT_SMPU_SMPU_STRUCT_V2_Type SMPU_STRUCT[32];
   volatile const uint32_t RESERVED1[1536];
} PROT_SMPU_V2_Type;
typedef struct {
  volatile uint32_t ADDR;
  volatile uint32_t ATT;
   volatile const uint32_t RESERVED[6];
} PROT_MPU_MPU_STRUCT_V2_Type;
typedef struct {
  volatile uint32_t MS_CTL;
   volatile const uint32_t MS_CTL_READ_MIR[127];
        PROT_MPU_MPU_STRUCT_V2_Type MPU_STRUCT[16];
} PROT_MPU_V2_Type;
typedef struct {
        PROT_SMPU_V2_Type SMPU;
        PROT_MPU_V2_Type CYMPU[16];
} PROT_V2_Type;
typedef struct {
   volatile const uint32_t ACQUIRE;
   volatile uint32_t RELEASE;
   volatile uint32_t NOTIFY;
  volatile uint32_t DATA0;
  volatile uint32_t DATA1;
   volatile const uint32_t RESERVED[2];
   volatile const uint32_t LOCK_STATUS;
} IPC_STRUCT_V2_Type;
typedef struct {
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED[4];
} IPC_INTR_STRUCT_V2_Type;
typedef struct {
        IPC_STRUCT_V2_Type STRUCT[16];
   volatile const uint32_t RESERVED[896];
        IPC_INTR_STRUCT_V2_Type INTR_STRUCT[16];
} IPC_V2_Type;
typedef struct {
  volatile uint32_t CH_CTL;
   volatile const uint32_t CH_STATUS;
  volatile uint32_t CH_IDX;
  volatile uint32_t CH_CURR_PTR;
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
  volatile uint32_t SRAM_DATA0;
  volatile uint32_t SRAM_DATA1;
  volatile uint32_t TR_CMD;
   volatile const uint32_t RESERVED[5];
} DW_CH_STRUCT_V2_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t STATUS;
   volatile const uint32_t RESERVED[6];
   volatile const uint32_t ACT_DESCR_CTL;
   volatile const uint32_t ACT_DESCR_SRC;
   volatile const uint32_t ACT_DESCR_DST;
   volatile const uint32_t RESERVED1;
   volatile const uint32_t ACT_DESCR_X_CTL;
   volatile const uint32_t ACT_DESCR_Y_CTL;
   volatile const uint32_t ACT_DESCR_NEXT_PTR;
   volatile const uint32_t RESERVED2;
   volatile const uint32_t ACT_SRC;
   volatile const uint32_t ACT_DST;
   volatile const uint32_t RESERVED3[14];
  volatile uint32_t ECC_CTL;
   volatile const uint32_t RESERVED4[31];
  volatile uint32_t CRC_CTL;
   volatile const uint32_t RESERVED5[3];
  volatile uint32_t CRC_DATA_CTL;
   volatile const uint32_t RESERVED6[3];
  volatile uint32_t CRC_POL_CTL;
   volatile const uint32_t RESERVED7[3];
  volatile uint32_t CRC_LFSR_CTL;
   volatile const uint32_t RESERVED8[3];
  volatile uint32_t CRC_REM_CTL;
   volatile const uint32_t RESERVED9;
   volatile const uint32_t CRC_REM_RESULT;
   volatile const uint32_t RESERVED10[8109];
        DW_CH_STRUCT_V2_Type CH_STRUCT[512];
} DW_V2_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED[3];
   volatile const uint32_t IDX;
   volatile const uint32_t SRC;
   volatile const uint32_t DST;
   volatile const uint32_t RESERVED1;
  volatile uint32_t CURR;
   volatile const uint32_t RESERVED2;
  volatile uint32_t TR_CMD;
   volatile const uint32_t RESERVED3[5];
   volatile const uint32_t DESCR_STATUS;
   volatile const uint32_t RESERVED4[7];
   volatile const uint32_t DESCR_CTL;
   volatile const uint32_t DESCR_SRC;
   volatile const uint32_t DESCR_DST;
   volatile const uint32_t DESCR_X_SIZE;
   volatile const uint32_t DESCR_X_INCR;
   volatile const uint32_t DESCR_Y_SIZE;
   volatile const uint32_t DESCR_Y_INCR;
   volatile const uint32_t DESCR_NEXT;
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED5[28];
} DMAC_CH_V2_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED;
   volatile const uint32_t ACTIVE;
   volatile const uint32_t RESERVED1[1021];
        DMAC_CH_V2_Type CH[8];
} DMAC_V2_Type;
typedef struct {
   volatile const uint32_t ID;
  volatile uint32_t DIVIDER;
  volatile uint32_t CONTROL;
   volatile const uint32_t RESERVED[61];
  volatile uint32_t DATA0[8];
   volatile const uint32_t RESERVED1[56];
  volatile uint32_t DATA1[8];
   volatile const uint32_t RESERVED2[56];
  volatile uint32_t DATA2[8];
   volatile const uint32_t RESERVED3[56];
  volatile uint32_t DATA3[8];
} LCD_V2_Type;
typedef struct {
  volatile uint32_t CTL;
   volatile const uint32_t RESERVED[7];
} SDHC_WRAP_V1_Type;
typedef struct {
  volatile uint32_t SDMASA_R;
  volatile uint16_t BLOCKSIZE_R;
  volatile uint16_t BLOCKCOUNT_R;
  volatile uint32_t ARGUMENT_R;
  volatile uint16_t XFER_MODE_R;
  volatile uint16_t CMD_R;
   volatile const uint32_t RESP01_R;
   volatile const uint32_t RESP23_R;
   volatile const uint32_t RESP45_R;
   volatile const uint32_t RESP67_R;
  volatile uint32_t BUF_DATA_R;
   volatile const uint32_t PSTATE_REG;
  volatile uint8_t HOST_CTRL1_R;
  volatile uint8_t PWR_CTRL_R;
  volatile uint8_t BGAP_CTRL_R;
  volatile uint8_t WUP_CTRL_R;
  volatile uint16_t CLK_CTRL_R;
  volatile uint8_t TOUT_CTRL_R;
  volatile uint8_t SW_RST_R;
  volatile uint16_t NORMAL_INT_STAT_R;
  volatile uint16_t ERROR_INT_STAT_R;
  volatile uint16_t NORMAL_INT_STAT_EN_R;
  volatile uint16_t ERROR_INT_STAT_EN_R;
  volatile uint16_t NORMAL_INT_SIGNAL_EN_R;
  volatile uint16_t ERROR_INT_SIGNAL_EN_R;
   volatile const uint16_t AUTO_CMD_STAT_R;
  volatile uint16_t HOST_CTRL2_R;
   volatile const uint32_t CAPABILITIES1_R;
   volatile const uint32_t CAPABILITIES2_R;
   volatile const uint32_t CURR_CAPABILITIES1_R;
   volatile const uint32_t CURR_CAPABILITIES2_R;
   volatile uint16_t FORCE_AUTO_CMD_STAT_R;
  volatile uint16_t FORCE_ERROR_INT_STAT_R;
   volatile const uint8_t ADMA_ERR_STAT_R;
   volatile const uint8_t RESERVED[3];
  volatile uint32_t ADMA_SA_LOW_R;
   volatile const uint32_t RESERVED1[7];
  volatile uint32_t ADMA_ID_LOW_R;
   volatile const uint16_t RESERVED2[65];
   volatile const uint16_t HOST_CNTRL_VERS_R;
   volatile const uint32_t RESERVED3[32];
   volatile const uint32_t CQVER;
   volatile const uint32_t CQCAP;
  volatile uint32_t CQCFG;
  volatile uint32_t CQCTL;
  volatile uint32_t CQIS;
  volatile uint32_t CQISE;
  volatile uint32_t CQISGE;
  volatile uint32_t CQIC;
  volatile uint32_t CQTDLBA;
   volatile const uint32_t RESERVED4;
  volatile uint32_t CQTDBR;
  volatile uint32_t CQTCN;
   volatile const uint32_t CQDQS;
   volatile const uint32_t CQDPT;
  volatile uint32_t CQTCLR;
   volatile const uint32_t RESERVED5;
  volatile uint32_t CQSSC1;
  volatile uint32_t CQSSC2;
   volatile const uint32_t CQCRDCT;
   volatile const uint32_t RESERVED6;
  volatile uint32_t CQRMEM;
   volatile const uint32_t CQTERRI;
   volatile const uint32_t CQCRI;
   volatile const uint32_t CQCRA;
   volatile const uint32_t RESERVED7[200];
   volatile const uint32_t MSHC_VER_ID_R;
   volatile const uint32_t MSHC_VER_TYPE_R;
  volatile uint8_t MSHC_CTRL_R;
   volatile const uint8_t RESERVED8[7];
  volatile uint8_t MBIU_CTRL_R;
   volatile const uint8_t RESERVED9[27];
  volatile uint16_t EMMC_CTRL_R;
  volatile uint16_t BOOT_CTRL_R;
   volatile const uint32_t GP_IN_R;
  volatile uint32_t GP_OUT_R;
   volatile const uint32_t RESERVED10[690];
} SDHC_CORE_V1_Type;
typedef struct {
        SDHC_WRAP_V1_Type WRAP;
   volatile const uint32_t RESERVED[1016];
        SDHC_CORE_V1_Type CORE;
} SDHC_V1_Type;
typedef struct {
   volatile const uint32_t CREL;
   volatile const uint32_t ENDN;
   volatile const uint32_t RESERVED;
  volatile uint32_t DBTP;
  volatile uint32_t TEST;
  volatile uint32_t RWD;
  volatile uint32_t CCCR;
  volatile uint32_t NBTP;
  volatile uint32_t TSCC;
  volatile uint32_t TSCV;
  volatile uint32_t TOCC;
  volatile uint32_t TOCV;
   volatile const uint32_t RESERVED1[4];
   volatile const uint32_t ECR;
   volatile const uint32_t PSR;
  volatile uint32_t TDCR;
   volatile const uint32_t RESERVED2;
  volatile uint32_t IR;
  volatile uint32_t IE;
  volatile uint32_t ILS;
  volatile uint32_t ILE;
   volatile const uint32_t RESERVED3[8];
  volatile uint32_t GFC;
  volatile uint32_t SIDFC;
  volatile uint32_t XIDFC;
   volatile const uint32_t RESERVED4;
  volatile uint32_t XIDAM;
   volatile const uint32_t HPMS;
  volatile uint32_t NDAT1;
  volatile uint32_t NDAT2;
  volatile uint32_t RXF0C;
   volatile const uint32_t RXF0S;
  volatile uint32_t RXF0A;
  volatile uint32_t RXBC;
  volatile uint32_t RXF1C;
   volatile const uint32_t RXF1S;
  volatile uint32_t RXF1A;
  volatile uint32_t RXESC;
  volatile uint32_t TXBC;
   volatile const uint32_t TXFQS;
  volatile uint32_t TXESC;
   volatile const uint32_t TXBRP;
  volatile uint32_t TXBAR;
  volatile uint32_t TXBCR;
   volatile const uint32_t TXBTO;
   volatile const uint32_t TXBCF;
  volatile uint32_t TXBTIE;
  volatile uint32_t TXBCIE;
   volatile const uint32_t RESERVED5[2];
  volatile uint32_t TXEFC;
   volatile const uint32_t TXEFS;
  volatile uint32_t TXEFA;
   volatile const uint32_t RESERVED6;
  volatile uint32_t TTTMC;
  volatile uint32_t TTRMC;
  volatile uint32_t TTOCF;
  volatile uint32_t TTMLM;
  volatile uint32_t TURCF;
  volatile uint32_t TTOCN;
  volatile uint32_t TTGTP;
  volatile uint32_t TTTMK;
  volatile uint32_t TTIR;
  volatile uint32_t TTIE;
  volatile uint32_t TTILS;
   volatile const uint32_t TTOST;
   volatile const uint32_t TURNA;
   volatile const uint32_t TTLGT;
   volatile const uint32_t TTCTC;
   volatile const uint32_t TTCPT;
   volatile const uint32_t TTCSM;
   volatile const uint32_t RESERVED7[15];
} CANFD_CH_M_TTCAN_V1_Type;
typedef struct {
        CANFD_CH_M_TTCAN_V1_Type M_TTCAN;
  volatile uint32_t RXFTOP_CTL;
   volatile const uint32_t RESERVED[7];
   volatile const uint32_t RXFTOP0_STAT;
   volatile const uint32_t RESERVED1;
   volatile const uint32_t RXFTOP0_DATA;
   volatile const uint32_t RESERVED2;
   volatile const uint32_t RXFTOP1_STAT;
   volatile const uint32_t RESERVED3;
   volatile const uint32_t RXFTOP1_DATA;
   volatile const uint32_t RESERVED4[17];
} CANFD_CH_V1_Type;
typedef struct {
        CANFD_CH_V1_Type CH[8];
  volatile uint32_t CTL;
   volatile const uint32_t STATUS;
   volatile const uint32_t RESERVED[2];
   volatile const uint32_t INTR0_CAUSE;
   volatile const uint32_t INTR1_CAUSE;
   volatile const uint32_t RESERVED1[2];
  volatile uint32_t TS_CTL;
  volatile uint32_t TS_CNT;
   volatile const uint32_t RESERVED2[22];
  volatile uint32_t ECC_CTL;
  volatile uint32_t ECC_ERR_INJ;
} CANFD_V1_Type;
typedef struct {
  volatile uint32_t CTRL;
   volatile const uint32_t STATUS;
  volatile uint32_t COUNTER;
   volatile const uint32_t RESERVED;
  volatile uint32_t CC0;
  volatile uint32_t CC0_BUFF;
  volatile uint32_t CC1;
  volatile uint32_t CC1_BUFF;
  volatile uint32_t PERIOD;
  volatile uint32_t PERIOD_BUFF;
  volatile uint32_t LINE_SEL;
  volatile uint32_t LINE_SEL_BUFF;
  volatile uint32_t DT;
   volatile const uint32_t RESERVED1[3];
  volatile uint32_t TR_CMD;
  volatile uint32_t TR_IN_SEL0;
  volatile uint32_t TR_IN_SEL1;
  volatile uint32_t TR_IN_EDGE_SEL;
  volatile uint32_t TR_PWM_CTRL;
  volatile uint32_t TR_OUT_SEL;
   volatile const uint32_t RESERVED2[6];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
} TCPWM_GRP_CNT_V2_Type;
typedef struct {
        TCPWM_GRP_CNT_V2_Type CNT[256];
} TCPWM_GRP_V2_Type;
typedef struct {
        TCPWM_GRP_V2_Type GRP[4];
} TCPWM_V2_Type;
typedef struct {
  volatile uint32_t CTB_CTRL;
  volatile uint32_t OA_RES0_CTRL;
  volatile uint32_t OA_RES1_CTRL;
   volatile const uint32_t COMP_STAT;
   volatile const uint32_t RESERVED[4];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED1[20];
  volatile uint32_t OA0_SW;
  volatile uint32_t OA0_SW_CLEAR;
  volatile uint32_t OA1_SW;
  volatile uint32_t OA1_SW_CLEAR;
   volatile const uint32_t RESERVED2[4];
  volatile uint32_t CTD_SW;
  volatile uint32_t CTD_SW_CLEAR;
   volatile const uint32_t RESERVED3[6];
  volatile uint32_t CTB_SW_DS_CTRL;
  volatile uint32_t CTB_SW_SQ_CTRL;
   volatile const uint32_t CTB_SW_STATUS;
   volatile const uint32_t RESERVED4[909];
  volatile uint32_t OA0_OFFSET_TRIM;
  volatile uint32_t OA0_SLOPE_OFFSET_TRIM;
  volatile uint32_t OA0_COMP_TRIM;
  volatile uint32_t OA1_OFFSET_TRIM;
  volatile uint32_t OA1_SLOPE_OFFSET_TRIM;
  volatile uint32_t OA1_COMP_TRIM;
} CTBM_V2_Type;
typedef struct {
  volatile uint32_t CTDAC_CTRL;
   volatile const uint32_t RESERVED[7];
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED1[32];
  volatile uint32_t CTDAC_SW;
  volatile uint32_t CTDAC_SW_CLEAR;
   volatile const uint32_t RESERVED2[18];
  volatile uint32_t CTDAC_VAL;
  volatile uint32_t CTDAC_VAL_NXT;
} CTDAC_V2_Type;
typedef struct {
  volatile uint32_t CTRL;
  volatile uint32_t SAMPLE_CTRL;
   volatile const uint32_t RESERVED[2];
  volatile uint32_t SAMPLE_TIME01;
  volatile uint32_t SAMPLE_TIME23;
  volatile uint32_t RANGE_THRES;
  volatile uint32_t RANGE_COND;
  volatile uint32_t CHAN_EN;
  volatile uint32_t START_CTRL;
   volatile const uint32_t RESERVED1[22];
  volatile uint32_t CHAN_CONFIG[16];
   volatile const uint32_t RESERVED2[16];
   volatile const uint32_t CHAN_WORK[16];
   volatile const uint32_t RESERVED3[16];
   volatile const uint32_t CHAN_RESULT[16];
   volatile const uint32_t RESERVED4[16];
   volatile const uint32_t CHAN_WORK_UPDATED;
   volatile const uint32_t CHAN_RESULT_UPDATED;
   volatile const uint32_t CHAN_WORK_NEWVALUE;
   volatile const uint32_t CHAN_RESULT_NEWVALUE;
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
  volatile uint32_t SATURATE_INTR;
  volatile uint32_t SATURATE_INTR_SET;
  volatile uint32_t SATURATE_INTR_MASK;
   volatile const uint32_t SATURATE_INTR_MASKED;
  volatile uint32_t RANGE_INTR;
  volatile uint32_t RANGE_INTR_SET;
  volatile uint32_t RANGE_INTR_MASK;
   volatile const uint32_t RANGE_INTR_MASKED;
   volatile const uint32_t INTR_CAUSE;
   volatile const uint32_t RESERVED5[15];
  volatile uint32_t INJ_CHAN_CONFIG;
   volatile const uint32_t RESERVED6[3];
   volatile const uint32_t INJ_RESULT;
   volatile const uint32_t RESERVED7[3];
   volatile const uint32_t STATUS;
   volatile const uint32_t AVG_STAT;
   volatile const uint32_t RESERVED8[22];
  volatile uint32_t MUX_SWITCH0;
  volatile uint32_t MUX_SWITCH_CLEAR0;
   volatile const uint32_t RESERVED9[15];
  volatile uint32_t MUX_SWITCH_SQ_CTRL;
   volatile const uint32_t MUX_SWITCH_STATUS;
} SAR_V2_Type;
typedef struct {
  volatile uint32_t CTRL;
  volatile uint32_t CONFIG;
  volatile uint32_t PERIOD;
   volatile const uint32_t RESERVED[61];
} PASS_TIMER_V2_Type;
typedef struct {
  volatile uint32_t CTRL;
  volatile uint32_t CONFIG;
  volatile uint32_t ADFT;
   volatile const uint32_t RESERVED[61];
} PASS_LPOSC_V2_Type;
typedef struct {
  volatile uint32_t CTRL;
  volatile uint32_t CONFIG;
  volatile uint32_t CLEAR;
  volatile uint32_t LEVEL;
   volatile const uint32_t USED;
   volatile const uint32_t STATUS;
   volatile const uint32_t RD_DATA;
   volatile const uint32_t RESERVED;
  volatile uint32_t INTR;
  volatile uint32_t INTR_SET;
  volatile uint32_t INTR_MASK;
   volatile const uint32_t INTR_MASKED;
   volatile const uint32_t RESERVED1[52];
} PASS_FIFO_V2_Type;
typedef struct {
  volatile uint32_t AREF_CTRL;
   volatile const uint32_t RESERVED[63];
} PASS_AREFV2_V2_Type;
typedef struct {
   volatile const uint32_t INTR_CAUSE;
   volatile const uint32_t RESERVED[3];
  volatile uint32_t DPSLP_CLOCK_SEL;
  volatile uint32_t ANA_PWR_CFG;
   volatile const uint32_t RESERVED1[2];
  volatile uint32_t CTBM_CLOCK_SEL[2];
   volatile const uint32_t RESERVED2[2];
  volatile uint32_t SAR_DPSLP_CTRL[2];
   volatile const uint32_t RESERVED3[2];
  volatile uint32_t SAR_CLOCK_SEL[2];
   volatile const uint32_t RESERVED4[2];
   volatile const uint32_t SAR_TR_SCAN_CNT_STATUS[2];
   volatile const uint32_t RESERVED5[2];
  volatile uint32_t SAR_TR_SCAN_CNT;
  volatile uint32_t SAR_OVR_CTRL;
  volatile uint32_t SAR_SIMULT_CTRL;
  volatile uint32_t SAR_SIMULT_FW_START_CTRL;
  volatile uint32_t SAR_TR_OUT_CTRL;
   volatile const uint32_t RESERVED6[35];
        PASS_TIMER_V2_Type TIMER;
        PASS_LPOSC_V2_Type LPOSC;
        PASS_FIFO_V2_Type FIFO[2];
   volatile const uint32_t RESERVED7[576];
        PASS_AREFV2_V2_Type AREFV2;
  volatile uint32_t VREF_TRIM0;
  volatile uint32_t VREF_TRIM1;
  volatile uint32_t VREF_TRIM2;
  volatile uint32_t VREF_TRIM3;
  volatile uint32_t IZTAT_TRIM0;
  volatile uint32_t IZTAT_TRIM1;
  volatile uint32_t IPTAT_TRIM0;
  volatile uint32_t ICTAT_TRIM0;
} PASS_V2_Type;
typedef struct
{
    uint32_t cpussBase;
    uint32_t flashcBase;
    uint32_t periBase;
    uint32_t udbBase;
    uint32_t protBase;
    uint32_t hsiomBase;
    uint32_t gpioBase;
    uint32_t passBase;
    uint32_t ipcBase;
    uint32_t cryptoBase;
    uint32_t sar0Base;
    uint8_t cpussVersion;
    uint8_t cryptoVersion;
    uint8_t dwVersion;
    uint8_t ipcVersion;
    uint8_t periVersion;
    uint8_t srssVersion;
    uint8_t passVersion;
    uint8_t cpussIpcNr;
    uint8_t cpussIpcIrqNr;
    uint8_t cpussDw0ChNr;
    uint8_t cpussDw1ChNr;
    uint8_t cpussFlashPaSize;
    int16_t cpussIpc0Irq;
    int16_t cpussFmIrq;
    int16_t cpussNotConnectedIrq;
    uint8_t srssNumClkpath;
    uint8_t srssNumPll;
    uint8_t srssNumHfroot;
    uint8_t srssIsPiloPresent;
    uint8_t periClockNr;
    uint8_t smifDeviceNr;
    uint8_t passSarChannels;
    uint8_t epMonitorNr;
    uint8_t udbPresent;
    uint8_t sysPmSimoPresent;
    uint32_t protBusMasterMask;
    uint32_t cryptoMemSize;
    uint8_t flashRwwRequired;
    uint8_t flashPipeRequired;
    uint8_t flashWriteDelay;
    uint8_t flashProgramDelay;
    uint8_t flashEraseDelay;
    uint8_t flashCtlMainWs0Freq;
    uint8_t flashCtlMainWs1Freq;
    uint8_t flashCtlMainWs2Freq;
    uint8_t flashCtlMainWs3Freq;
    uint8_t flashCtlMainWs4Freq;
    uint8_t tcpwmCC1Present;
    uint8_t tcpwmAMCPresent;
    uint8_t tcpwmSMCPrecent;
    uint16_t dwChOffset;
    uint16_t dwChSize;
    uint8_t dwChCtlPrioPos;
    uint8_t dwChCtlPreemptablePos;
    uint8_t dwStatusChIdxPos;
    uint32_t dwStatusChIdxMsk;
    uint16_t periTrCmdOffset;
    uint16_t periTrCmdGrSelMsk;
    uint16_t periTrGrOffset;
    uint16_t periTrGrSize;
    uint8_t periDivCmdDivSelMsk;
    uint8_t periDivCmdTypeSelPos;
    uint8_t periDivCmdPaDivSelPos;
    uint8_t periDivCmdPaTypeSelPos;
    uint16_t periDiv8CtlOffset;
    uint16_t periDiv16CtlOffset;
    uint16_t periDiv16_5CtlOffset;
    uint16_t periDiv24_5CtlOffset;
    uint8_t gpioPrtIntrCfgOffset;
    uint8_t gpioPrtCfgOffset;
    uint8_t gpioPrtCfgInOffset;
    uint8_t gpioPrtCfgOutOffset;
    uint8_t gpioPrtCfgSioOffset;
    uint32_t cpussCm0ClockCtlOffset;
    uint32_t cpussCm4ClockCtlOffset;
    uint32_t cpussCm4StatusOffset;
    uint32_t cpussCm0StatusOffset;
    uint32_t cpussCm4PwrCtlOffset;
    uint32_t cpussTrimRamCtlOffset;
    uint32_t cpussTrimRomCtlOffset;
    uint32_t cpussSysTickCtlOffset;
    uint16_t cpussCm0NmiCtlOffset;
    uint16_t cpussCm4NmiCtlOffset;
    uint16_t cpussRomCtl;
    uint16_t cpussRam0Ctl0;
    uint16_t cpussRam1Ctl0;
    uint16_t cpussRam2Ctl0;
    uint16_t cpussRam0PwrCtl;
    uint16_t cpussRam1PwrCtl;
    uint16_t cpussRam2PwrCtl;
    uint16_t ipcStructSize;
    uint32_t ipcLockStatusOffset;
} cy_stc_device_t;
extern const cy_stc_device_t cy_deviceIpBlockCfgPSoC6_01;
extern const cy_stc_device_t cy_deviceIpBlockCfgPSoC6_02;
extern const cy_stc_device_t cy_deviceIpBlockCfgPSoC6_03;
extern const cy_stc_device_t cy_deviceIpBlockCfgPSoC6_04;
extern const cy_stc_device_t cy_deviceIpBlockCfgTVIIBE4M;
extern const cy_stc_device_t cy_deviceIpBlockCfgTVIIBE2M;
extern const cy_stc_device_t cy_deviceIpBlockCfgTVIIBE1M;
extern const cy_stc_device_t * cy_device;
void Cy_PDL_Init(const cy_stc_device_t * device);

typedef char cy_char8_t;
typedef float cy_float32_t;
typedef double cy_float64_t;
static inline void CY_HALT(void)
{
    __asm("    bkpt    1");
}

typedef enum
{
    CY_SYSLIB_SUCCESS = 0x00UL,
    CY_SYSLIB_BAD_PARAM = ((uint32_t)((uint32_t)((0x11U) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01UL,
    CY_SYSLIB_TIMEOUT = ((uint32_t)((uint32_t)((0x11U) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02UL,
    CY_SYSLIB_INVALID_STATE = ((uint32_t)((uint32_t)((0x11U) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x03UL,
    CY_SYSLIB_UNKNOWN = ((uint32_t)((uint32_t)((0x11U) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0xFFUL
} cy_en_syslib_status_t;
typedef enum
{
    CY_SYSLIB_LCS_VIRGIN = 0x000UL,
    CY_SYSLIB_LCS_SORT = 0x003UL,
    CY_SYSLIB_LCS_PROVISIONED = 0x00FUL,
    CY_SYSLIB_LCS_NORMAL_PROVISIONED = 0xC0FUL,
    CY_SYSLIB_LCS_NORMAL = 0xC03UL,
    CY_SYSLIB_LCS_SECURE = 0xC3FUL,
    CY_SYSLIB_LCS_NORMAL_NO_SECURE = 0xCC3UL,
    CY_SYSLIB_LCS_RMA = 0xF3FUL,
    CY_SYSLIB_LCS_CORRUPTED = 0xFFFFUL,
} cy_en_syslib_lcs_mode_t;
        typedef struct
        {
            uint32_t iaccViol : 1;
            uint32_t daccViol : 1;
            uint32_t reserved1 : 1;
            uint32_t mUnstkErr : 1;
            uint32_t mStkErr : 1;
            uint32_t mlspErr : 1;
            uint32_t reserved2 : 1;
            uint32_t mmarValid : 1;
            uint32_t iBusErr : 1;
            uint32_t precisErr : 1;
            uint32_t imprecisErr : 1;
            uint32_t unstkErr : 1;
            uint32_t stkErr : 1;
            uint32_t lspErr : 1;
            uint32_t reserved3 : 1;
            uint32_t bfarValid : 1;
            uint32_t undefInstr : 1;
            uint32_t invState : 1;
            uint32_t invPC : 1;
            uint32_t noCP : 1;
            uint32_t reserved4 : 4;
            uint32_t unaligned : 1;
            uint32_t divByZero : 1;
            uint32_t reserved5 : 6;
        } cy_stc_fault_cfsr_t;
        typedef struct
        {
            uint32_t reserved1 : 1;
            uint32_t vectTbl : 1;
            uint32_t reserved2 : 28;
            uint32_t forced : 1;
            uint32_t debugEvt : 1;
        } cy_stc_fault_hfsr_t;
        typedef struct
        {
            uint32_t memFaultAct : 1;
            uint32_t busFaultAct : 1;
            uint32_t reserved1 : 1;
            uint32_t usgFaultAct : 1;
            uint32_t reserved2 : 3;
            uint32_t svCallAct : 1;
            uint32_t monitorAct : 1;
            uint32_t reserved3 : 1;
            uint32_t pendSVAct : 1;
            uint32_t sysTickAct : 1;
            uint32_t usgFaultPended : 1;
            uint32_t memFaultPended : 1;
            uint32_t busFaultPended : 1;
            uint32_t svCallPended : 1;
            uint32_t memFaultEna : 1;
            uint32_t busFaultEna : 1;
            uint32_t usgFaultEna : 1;
            uint32_t reserved4 : 13;
        } cy_stc_fault_shcsr_t;
    typedef struct
    {
        uint32_t r0;
        uint32_t r1;
        uint32_t r2;
        uint32_t r3;
        uint32_t r12;
        uint32_t lr;
        uint32_t pc;
        uint32_t psr;
            union
            {
                uint32_t cfsrReg;
                cy_stc_fault_cfsr_t cfsrBits;
            } cfsr;
            union
            {
                uint32_t hfsrReg;
                cy_stc_fault_hfsr_t hfsrBits;
            } hfsr;
            union
            {
                uint32_t shcsrReg;
                cy_stc_fault_shcsr_t shcsrBits;
            } shcsr;
            uint32_t mmfar;
            uint32_t bfar;
    } cy_stc_fault_frame_t;
typedef void (* cy_israddress)(void);
typedef char char_t;
typedef float float32_t;
typedef double float64_t;
    extern __attribute__ ((section(".noinit"))) char_t cy_assertFileName[(24U) + 1];
    extern __attribute__ ((section(".noinit"))) uint32_t cy_assertLine;
    extern __attribute__ ((section(".noinit"))) cy_stc_fault_frame_t cy_faultFrame;
void Cy_SysLib_Delay(uint32_t milliseconds);
void Cy_SysLib_DelayUs(uint16_t microseconds);
void Cy_SysLib_Rtos_Delay(uint32_t milliseconds);
void Cy_SysLib_Rtos_DelayUs(uint16_t microseconds);
void Cy_SysLib_DelayCycles(uint32_t cycles);
__attribute__((__noreturn__)) void Cy_SysLib_Halt(uint32_t reason);
void Cy_SysLib_AssertFailed(const char_t * file, uint32_t line);
void Cy_SysLib_ClearFlashCacheAndBuffer(void);
uint64_t Cy_SysLib_GetUniqueId(void);
cy_en_syslib_status_t Cy_SysLib_ResetBackupDomain(void);
uint32_t Cy_SysLib_GetResetReason(void);
void Cy_SysLib_ClearResetReason(void);
static inline cy_en_syslib_status_t Cy_SysLib_GetResetStatus (void)
{
    return ((0UL == ((((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->RESET) & 0x80000000UL)) ? CY_SYSLIB_SUCCESS : CY_SYSLIB_INVALID_STATE);
}
static inline uint32_t Cy_SysLib_GetWcoTrim (void)
{
    return ((((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->TRIM) & 0x3FUL);
}
static inline void Cy_SysLib_SetWcoTrim (uint32_t wcoTrim)
{
    ( (void)(wcoTrim) );
    (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->TRIM) = wcoTrim & 0x3FUL;
}
    void Cy_SysLib_FaultHandler(uint32_t const *faultStackAddr);
    void Cy_SysLib_ProcessingFault(void);
void Cy_SysLib_SetWaitStates(_Bool ulpMode, uint32_t clkHfMHz);
uint32_t Cy_SysLib_EnterCriticalSection(void);
void Cy_SysLib_ExitCriticalSection(uint32_t savedIntrStatus);
uint8_t Cy_SysLib_GetDeviceRevision(void);
uint16_t Cy_SysLib_GetDevice(void);
typedef uint32_t cy_status;
typedef uint32_t cystatus;
typedef uint8_t uint8;
typedef uint16_t uint16;
typedef uint32_t uint32;
typedef int8_t int8;
typedef int16_t int16;
typedef int32_t int32;
typedef float float32;
typedef double float64;
typedef int64_t int64;
typedef uint64_t uint64;
typedef char char8;
typedef volatile uint8_t reg8;
typedef volatile uint16_t reg16;
typedef volatile uint32_t reg32;
typedef void (* cyisraddress)(void);

typedef enum
{
    CY_BLE_MXD_RADIO_CLK_DIV_1 = 0U,
    CY_BLE_MXD_RADIO_CLK_DIV_2 = 1U,
    CY_BLE_MXD_RADIO_CLK_DIV_4 = 2U,
    CY_BLE_MXD_RADIO_CLK_DIV_8 = 4U,
    CY_BLE_MXD_RADIO_CLK_DIV_16 = 8U
} cy_en_ble_mxd_radio_clk_div_t;
typedef enum
{
    CY_BLE_MXD_RADIO_CLK_BUF_AMP_16M_SMALL = 0U,
    CY_BLE_MXD_RADIO_CLK_BUF_AMP_16M_LARGE = 1U,
    CY_BLE_MXD_RADIO_CLK_BUF_AMP_32M_SMALL = 2U,
    CY_BLE_MXD_RADIO_CLK_BUF_AMP_32M_LARGE = 3U
} cy_en_ble_mxd_radio_clk_buf_amp_t;
typedef enum
{
    CY_BLE_BLESS_XTAL_CLK_DIV_1 = 0U,
    CY_BLE_BLESS_XTAL_CLK_DIV_2 = 1U,
    CY_BLE_BLESS_XTAL_CLK_DIV_4 = 2U,
    CY_BLE_BLESS_XTAL_CLK_DIV_8 = 3U
}cy_en_ble_bless_xtal_clk_div_config_llclk_div_t;
typedef enum
{
    CY_BLE_BLESS_ECO_FREQ_16MHZ,
    CY_BLE_BLESS_ECO_FREQ_32MHZ
} cy_en_ble_eco_freq_t;
typedef enum
{
    CY_BLE_SYS_ECO_CLK_DIV_1 = 0x00U,
    CY_BLE_SYS_ECO_CLK_DIV_2,
    CY_BLE_SYS_ECO_CLK_DIV_4,
    CY_BLE_SYS_ECO_CLK_DIV_8,
    CY_BLE_SYS_ECO_CLK_DIV_INVALID
} cy_en_ble_eco_sys_clk_div_t;
typedef enum
{
    CY_BLE_ECO_SUCCESS = 0x00UL,
    CY_BLE_ECO_BAD_PARAM = ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x05UL << 18U) | 0x0001UL,
    CY_BLE_ECO_RCB_CONTROL_LL = ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x05UL << 18U) | 0x0002UL,
    CY_BLE_ECO_ALREADY_STARTED = ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x05UL << 18U) | 0x0003UL,
    CY_BLE_ECO_HARDWARE_ERROR = ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x05UL << 18U) | 0x0004UL,
} cy_en_ble_eco_status_t;
typedef enum
{
    CY_BLE_ECO_VOLTAGE_REG_AUTO,
    CY_BLE_ECO_VOLTAGE_REG_BLESSLDO
} cy_en_ble_eco_voltage_reg_t;
typedef struct
{
    uint8_t ecoXtalStartUpTime;
    uint8_t loadCap;
    cy_en_ble_eco_freq_t ecoFreq;
    cy_en_ble_eco_sys_clk_div_t ecoSysDiv;
} cy_stc_ble_eco_config_t;
cy_en_ble_eco_status_t Cy_BLE_EcoConfigure(cy_en_ble_eco_freq_t freq,
                                    cy_en_ble_eco_sys_clk_div_t sysClkDiv,
                                                       uint32_t cLoad,
                                                       uint32_t xtalStartUpTime,
                                    cy_en_ble_eco_voltage_reg_t voltageReg);
void Cy_BLE_EcoReset(void);
static inline _Bool Cy_BLE_EcoIsEnabled(void);
static inline _Bool Cy_BLE_EcoIsEnabled(void)
{
    return ((((((BLE_V1_Type *) 0x403C0000UL)->BLESS.MT_CFG) & 0x1UL) != 0u) &&
            (((((BLE_V1_Type *) 0x403C0000UL)->BLESS.MT_STATUS) & 0x1UL) != 0u));
}
cy_en_ble_eco_status_t Cy_BLE_EcoStart(const cy_stc_ble_eco_config_t *config);
void Cy_BLE_EcoStop(void);
void Cy_BLE_HAL_Init(void);



extern const cy_israddress __Vectors[];
extern cy_israddress __ramVectors[];

typedef enum
{
    CY_SYSINT_SUCCESS = 0x0UL,
    CY_SYSINT_BAD_PARAM = ((uint32_t)((uint32_t)((0x15U) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x1UL,
} cy_en_sysint_status_t;
typedef enum
{
    CY_SYSINT_NMI1 = 1UL,
    CY_SYSINT_NMI2 = 2UL,
    CY_SYSINT_NMI3 = 3UL,
    CY_SYSINT_NMI4 = 4UL,
} cy_en_sysint_nmi_t;
typedef struct {
    IRQn_Type intrSrc;
    uint32_t intrPriority;
} cy_stc_sysint_t;
cy_en_sysint_status_t Cy_SysInt_Init(const cy_stc_sysint_t* config, cy_israddress userIsr);
cy_israddress Cy_SysInt_SetVector(IRQn_Type IRQn, cy_israddress userIsr);
cy_israddress Cy_SysInt_GetVector(IRQn_Type IRQn);

void Cy_SysInt_SetNmiSource(cy_en_sysint_nmi_t nmiNum, IRQn_Type intrSrc);
IRQn_Type Cy_SysInt_GetNmiSource(cy_en_sysint_nmi_t nmiNum);

void Cy_SysInt_SoftwareTrig(IRQn_Type IRQn);
typedef struct
{
    uint8_t *moduloPtr;
    uint32_t moduloLength;
    uint8_t *pubExpPtr;
    uint32_t pubExpLength;
    uint8_t *barretCoefPtr;
    uint8_t *inverseModuloPtr;
    uint8_t *rBarPtr;
} cy_stc_crypto_rsa_pub_key_t;
typedef void (*cy_crypto_callback_ptr_t)(void);
typedef struct
{
    uint32_t ipcChannel;
    uint32_t acquireNotifierChannel;
    uint32_t releaseNotifierChannel;
    cy_stc_sysint_t releaseNotifierConfig;
    cy_crypto_callback_ptr_t userCompleteCallback;
    cy_israddress userGetDataHandler;
    cy_israddress userErrorHandler;
    cy_stc_sysint_t acquireNotifierConfig;
    cy_stc_sysint_t cryptoErrorIntrConfig;
} cy_stc_crypto_config_t;
typedef struct
{
    uint32_t errorStatus0;
    uint32_t errorStatus1;
} cy_stc_crypto_hw_error_t;
typedef enum
{
    CY_CRYPTO_NO_LIBRARY = 0x00u,
    CY_CRYPTO_BASE_LIBRARY = 0x01u,
    CY_CRYPTO_EXTRA_LIBRARY = 0x02u,
    CY_CRYPTO_FULL_LIBRARY = 0x03u,
} cy_en_crypto_lib_info_t;
typedef enum
{
    CY_CRYPTO_KEY_AES_128 = 0x00u,
    CY_CRYPTO_KEY_AES_192 = 0x01u,
    CY_CRYPTO_KEY_AES_256 = 0x02u
} cy_en_crypto_aes_key_length_t;
typedef enum
{
    CY_CRYPTO_ENCRYPT = 0x00u,
    CY_CRYPTO_DECRYPT = 0x01u
} cy_en_crypto_dir_mode_t;
typedef enum
{
    CY_CRYPTO_MODE_SHA1 = 0x00u,
    CY_CRYPTO_MODE_SHA224 = 0x01u,
    CY_CRYPTO_MODE_SHA256 = 0x02u,
    CY_CRYPTO_MODE_SHA384 = 0x03u,
    CY_CRYPTO_MODE_SHA512 = 0x04u,
    CY_CRYPTO_MODE_SHA512_256 = 0x05u,
    CY_CRYPTO_MODE_SHA512_224 = 0x06u,
    CY_CRYPTO_MODE_SHA_NONE = 0x07u,
} cy_en_crypto_sha_mode_t;
typedef enum
{
    CY_CRYPTO_RSA_VERIFY_SUCCESS = 0x00u,
    CY_CRYPTO_RSA_VERIFY_FAIL = 0x01u
} cy_en_crypto_rsa_ver_result_t;
typedef enum
{
    CY_CRYPTO_SUCCESS = 0x00u,
    CY_CRYPTO_HW_ERROR = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01u,
    CY_CRYPTO_SIZE_NOT_X16 = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02u,
    CY_CRYPTO_DES_WEAK_KEY = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_WARNING << ((16U))) | 0x03u,
    CY_CRYPTO_COMM_FAIL = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x04u,
    CY_CRYPTO_SERVER_NOT_STARTED = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x06u,
    CY_CRYPTO_SERVER_BUSY = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_INFO << ((16U))) | 0x07u,
    CY_CRYPTO_NOT_INITIALIZED = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x08u,
    CY_CRYPTO_HW_NOT_ENABLED = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x09u,
    CY_CRYPTO_NOT_SUPPORTED = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x0Au,
    CY_CRYPTO_BAD_PARAMS = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x0Bu,
    CY_CRYPTO_TRNG_UNHEALTHY = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_WARNING << ((16U))) | 0x0Cu,
    CY_CRYPTO_MEMORY_ALLOC_FAIL = ((uint32_t)((uint32_t)((0x0Cu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x0Du
} cy_en_crypto_status_t;
typedef enum {
    CY_CRYPTO_ECC_ECP_NONE = 0,
    CY_CRYPTO_ECC_ECP_SECP192R1,
    CY_CRYPTO_ECC_ECP_SECP224R1,
    CY_CRYPTO_ECC_ECP_SECP256R1,
    CY_CRYPTO_ECC_ECP_SECP384R1,
    CY_CRYPTO_ECC_ECP_SECP521R1,
    CY_CRYPTO_ECC_ECP_CURVES_CNT
} cy_en_crypto_ecc_curve_id_t;
typedef enum
{
    CY_CRYPTO_INSTR_UNKNOWN = 0x00u,
    CY_CRYPTO_INSTR_ENABLE = 0x01u,
    CY_CRYPTO_INSTR_DISABLE = 0x02u,
    CY_CRYPTO_INSTR_PRNG_INIT = 0x03u,
    CY_CRYPTO_INSTR_PRNG = 0x04u,
    CY_CRYPTO_INSTR_TRNG_INIT = 0x05u,
    CY_CRYPTO_INSTR_TRNG = 0x06u,
    CY_CRYPTO_INSTR_AES_INIT = 0x07u,
    CY_CRYPTO_INSTR_AES_ECB = 0x08u,
    CY_CRYPTO_INSTR_AES_CBC = 0x09u,
    CY_CRYPTO_INSTR_AES_CFB = 0x0Au,
    CY_CRYPTO_INSTR_AES_CTR = 0x0Bu,
    CY_CRYPTO_INSTR_CMAC = 0x0Cu,
    CY_CRYPTO_INSTR_SHA = 0x0Du,
    CY_CRYPTO_INSTR_HMAC = 0x0Eu,
    CY_CRYPTO_INSTR_MEM_CPY = 0x0Fu,
    CY_CRYPTO_INSTR_MEM_SET = 0x10u,
    CY_CRYPTO_INSTR_MEM_CMP = 0x11u,
    CY_CRYPTO_INSTR_MEM_XOR = 0x12u,
    CY_CRYPTO_INSTR_CRC_INIT = 0x13u,
    CY_CRYPTO_INSTR_CRC = 0x14u,
    CY_CRYPTO_INSTR_DES = 0x15u,
    CY_CRYPTO_INSTR_3DES = 0x16u,
    CY_CRYPTO_INSTR_RSA_PROC = 0x17u,
    CY_CRYPTO_INSTR_RSA_COEF = 0x18u,
    CY_CRYPTO_INSTR_RSA_VER = 0x19u,
    CY_CRYPTO_INSTR_SRV_INFO = 0x55u,
    CY_CRYPTO_INSTR_MEMBUF_SET = 0x56u,
    CY_CRYPTO_INSTR_MEMBUF_ADDR = 0x57u,
    CY_CRYPTO_INSTR_MEMBUF_SIZE = 0x58u,
    CY_CRYPTO_INSTR_ECC_GET_DP = 0x59u,
    CY_CRYPTO_INSTR_ECC_ECP_MUL = 0x5Au,
    CY_CRYPTO_INSTR_ECP_GEN_PRIK = 0x5Bu,
    CY_CRYPTO_INSTR_ECP_GEN_PUBK = 0x5Cu,
    CY_CRYPTO_INSTR_ECDSA_SIGN = 0x5Du,
    CY_CRYPTO_INSTR_ECDSA_VER = 0x5Eu
} cy_en_crypto_comm_instr_t;
typedef struct
{
    uint32_t key[(uint32_t)(((32u)) / 4UL)];
    uint32_t keyInv[(uint32_t)(((32u)) / 4UL)];
    uint32_t block0[(uint32_t)((16u) / 4UL)];
    uint32_t block1[(uint32_t)((16u) / 4UL)];
    uint32_t block2[(uint32_t)((16u) / 4UL)];
    uint8_t unProcessedData[(16u)];
    uint8_t iv[(16u)];
} cy_stc_crypto_aes_buffers_t;
typedef struct
{
    cy_en_crypto_aes_key_length_t keyLength;
    cy_stc_crypto_aes_buffers_t *buffers;
    uint32_t blockIdx;
    uint32_t unProcessedBytes;
    uint16_t ivSize;
    cy_en_crypto_dir_mode_t dirMode;
} cy_stc_crypto_aes_state_t;
typedef struct
{
    cy_stc_crypto_aes_buffers_t aesCbcMacBuffer;
    cy_stc_crypto_aes_buffers_t aesCtrBuffer;
    __attribute__((aligned(4))) uint8_t temp_buffer[(16u)];
    __attribute__((aligned(4))) uint8_t ctr[(16u)];
    __attribute__((aligned(4))) uint8_t y[(16u)];
} cy_stc_crypto_aes_ccm_buffers_t;
typedef struct
{
    cy_en_crypto_dir_mode_t dirMode;
    cy_stc_crypto_aes_state_t aesCbcMacState;
    cy_stc_crypto_aes_state_t aesCtrState;
    uint8_t *temp;
    uint8_t *ctr;
    uint8_t *y;
    uint32_t L;
    uint32_t textLength;
    uint32_t aadLength;
    uint8_t tagLength;
    uint32_t aadLengthProcessed;
    _Bool isAadProcessed;
    _Bool isIvSet;
    _Bool isLengthSet;
} cy_stc_crypto_aes_ccm_state_t;
typedef struct
{
    uint32_t mode;
    uint32_t modeHw;
    uint8_t *block;
    uint32_t blockSize;
    uint8_t *hash;
    uint32_t hashSize;
    uint8_t *roundMem;
    uint32_t roundMemSize;
    uint64_t messageSize;
    uint32_t digestSize;
    uint32_t blockIdx;
    uint8_t const *initialHash;
} cy_stc_crypto_sha_state_t;
typedef struct
{
    uint8_t *ipad;
    uint8_t *opad;
    uint8_t *m0Key;
    void* sha_buffer;
    cy_stc_crypto_sha_state_t hashState;
} cy_stc_crypto_hmac_state_t;
typedef struct {
    void *x;
    void *y;
} cy_stc_crypto_ecc_point;
typedef enum cy_en_crypto_ecc_key_type {
   PK_PUBLIC = 0u,
   PK_PRIVATE = 1u
} cy_en_crypto_ecc_key_type_t;
typedef struct {
    cy_en_crypto_ecc_key_type_t type;
    cy_en_crypto_ecc_curve_id_t curveID;
    cy_stc_crypto_ecc_point pubkey;
    void *k;
} cy_stc_crypto_ecc_key;
typedef struct
{
    uint32_t ipcChannel;
    uint32_t acquireNotifierChannel;
    cy_israddress getDataHandlerPtr;
    cy_israddress errorHandlerPtr;
    cy_stc_sysint_t acquireNotifierConfig;
    cy_stc_sysint_t cryptoErrorIntrConfig;
    _Bool isHwErrorOccured;
    cy_stc_crypto_hw_error_t hwErrorStatus;
} cy_stc_crypto_server_context_t;
typedef struct
{
    cy_en_crypto_comm_instr_t instr;
    cy_en_crypto_status_t resp;
    cy_stc_crypto_hw_error_t hwErrorStatus;
    uint32_t ipcChannel;
    uint32_t acquireNotifierChannel;
    uint32_t releaseNotifierChannel;
    cy_crypto_callback_ptr_t userCompleteCallback;
    cy_stc_sysint_t releaseNotifierConfig;
    void *xdata;
} cy_stc_crypto_context_t;
typedef struct
{
    cy_en_crypto_dir_mode_t dirMode;
    uint32_t *key;
    uint32_t *dst;
    uint32_t *src;
} cy_stc_crypto_context_des_t;
typedef struct
{
    cy_stc_crypto_aes_state_t aesState;
    cy_en_crypto_dir_mode_t dirMode;
    cy_en_crypto_aes_key_length_t keyLength;
    uint32_t *key;
    uint32_t srcSize;
    uint32_t *srcOffset;
    uint32_t *ivPtr;
    uint32_t *streamBlock;
    uint32_t *dst;
    uint32_t *src;
} cy_stc_crypto_context_aes_t;
typedef struct
{
    uint32_t *message;
    uint32_t messageSize;
    uint32_t *dst;
    cy_en_crypto_sha_mode_t mode;
    uint32_t *key;
    uint32_t keyLength;
} cy_stc_crypto_context_sha_t;
typedef struct
{
    uint32_t lfsr32InitState;
    uint32_t lfsr31InitState;
    uint32_t lfsr29InitState;
    uint32_t max;
    uint32_t *prngNum;
} cy_stc_crypto_context_prng_t;
typedef enum
{
    CY_CRYPTO_TR_SRC_RO11 = 0,
    CY_CRYPTO_TR_SRC_RO15,
    CY_CRYPTO_TR_SRC_GARO15,
    CY_CRYPTO_TR_SRC_GARO31,
    CY_CRYPTO_TR_SRC_FIRO15,
    CY_CRYPTO_TR_SRC_FIRO31
} cy_en_crypto_trng_ro_sel_t;
typedef enum
{
    CY_CRYPTO_TRMON_BS_DAS = 0,
    CY_CRYPTO_TRMON_BS_RED,
    CY_CRYPTO_TRMON_BS_TR,
    CY_CRYPTO_TRMON_BS_UNDEF
} cy_en_crypto_trng_bs_sel_t;
typedef struct
{
    uint8_t sampleClockDiv;
    uint8_t reducedClockDiv;
    uint8_t initDelay;
    _Bool vnCorrectorEnable;
    _Bool stopOnAPDetect;
    _Bool stopOnRCDetect;
    _Bool ro11Enable;
    _Bool ro15Enable;
    _Bool garo15Enable;
    _Bool garo31Enable;
    _Bool firo15Enable;
    _Bool firo31Enable;
    uint32_t garo31Poly;
    uint32_t firo31Poly;
    cy_en_crypto_trng_bs_sel_t monBitStreamSelect;
    uint8_t monCutoffCount8;
    uint16_t monCutoffCount16;
    uint16_t monWindowSize;
} cy_stc_crypto_trng_config_t;
typedef struct
{
    uint32_t GAROPol;
    uint32_t FIROPol;
    uint32_t max;
    uint32_t *trngNum;
} cy_stc_crypto_context_trng_t;
typedef struct
{
    void const *src0;
    void const *src1;
    void *dst;
    uint32_t dataSize;
    uint32_t data;
} cy_stc_crypto_context_str_t;
typedef struct
{
    void* data;
    uint32_t dataSize;
    uint32_t *crc;
    uint32_t polynomial;
    uint32_t lfsrInitState;
    uint32_t dataReverse;
    uint32_t dataXor;
    uint32_t remReverse;
    uint32_t remXor;
} cy_stc_crypto_context_crc_t;
typedef struct
{
    cy_stc_crypto_rsa_pub_key_t const *key;
    uint32_t const *message;
    uint32_t messageSize;
    uint32_t *result;
} cy_stc_crypto_context_rsa_t;
typedef struct
{
    cy_en_crypto_rsa_ver_result_t *verResult;
    cy_en_crypto_sha_mode_t digestType;
    uint32_t const *hash;
    uint32_t const *decryptedSignature;
    uint32_t decryptedSignatureLength;
} cy_stc_crypto_context_rsa_ver_t;
typedef struct
{
    cy_en_crypto_ecc_curve_id_t curveID;
    const cy_stc_crypto_ecc_key *key;
    uint32_t datalen;
    const uint8_t *src0;
    const uint8_t *src1;
    const uint8_t *src2;
    uint8_t *dst0;
    uint8_t *dst1;
} cy_stc_crypto_context_ecc_t;
typedef enum
{
    CY_CRYPTO_CCM_TAG_VALID = 0x05555555u,
    CY_CRYPTO_CCM_TAG_INVALID = 0x0AAAAAAAu,
} cy_en_crypto_aesccm_tag_verify_result_t;
cy_en_crypto_status_t Cy_Crypto_GetLibraryInfo(cy_en_crypto_lib_info_t *cryptoInfo);
cy_en_crypto_status_t Cy_Crypto_Init(cy_stc_crypto_config_t const *config, cy_stc_crypto_context_t *context);
cy_en_crypto_status_t Cy_Crypto_DeInit(void);
cy_en_crypto_status_t Cy_Crypto_Enable(void);
cy_en_crypto_status_t Cy_Crypto_Disable(void);
cy_en_crypto_status_t Cy_Crypto_Sync(_Bool isBlocking);
cy_en_crypto_status_t Cy_Crypto_GetErrorStatus(cy_stc_crypto_hw_error_t *hwErrorCause);
cy_en_crypto_status_t Cy_Crypto_Prng_Init(uint32_t lfsr32InitState,
                                          uint32_t lfsr31InitState,
                                          uint32_t lfsr29InitState,
                                          cy_stc_crypto_context_prng_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Prng_Generate(uint32_t max,
                                              uint32_t *randomNum,
                                              cy_stc_crypto_context_prng_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Aes_Init(uint32_t *key,
                                         cy_en_crypto_aes_key_length_t keyLength,
                                         cy_stc_crypto_context_aes_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Aes_Ecb_Run(cy_en_crypto_dir_mode_t dirMode,
                                            uint32_t *dstBlock,
                                            uint32_t *srcBlock,
                                            cy_stc_crypto_context_aes_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Aes_Cbc_Run(cy_en_crypto_dir_mode_t dirMode,
                                            uint32_t srcSize,
                                            uint32_t *ivPtr,
                                            uint32_t *dst,
                                            uint32_t *src,
                                            cy_stc_crypto_context_aes_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Aes_Cfb_Run(cy_en_crypto_dir_mode_t dirMode,
                                            uint32_t srcSize,
                                            uint32_t *ivPtr,
                                            uint32_t *dst,
                                            uint32_t *src,
                                            cy_stc_crypto_context_aes_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Aes_Ctr_Run(cy_en_crypto_dir_mode_t dirMode,
                                            uint32_t srcSize,
                                            uint32_t *srcOffset,
                                            uint32_t nonceCounter[(16u) / 8u],
                                            uint32_t streamBlock[(16u) / 8u],
                                            uint32_t *dst,
                                            uint32_t *src,
                                            cy_stc_crypto_context_aes_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Aes_Cmac_Run(uint32_t *src,
                                             uint32_t srcSize,
                                             uint32_t *key,
                                             cy_en_crypto_aes_key_length_t keyLength,
                                             uint32_t *cmacPtr,
                                             cy_stc_crypto_context_aes_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Sha_Run(uint32_t *message,
                                        uint32_t messageSize,
                                        uint32_t *digest,
                                        cy_en_crypto_sha_mode_t mode,
                                        cy_stc_crypto_context_sha_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Hmac_Run(uint32_t *hmac,
                                         uint32_t *message,
                                         uint32_t messageSize,
                                         uint32_t *key,
                                         uint32_t keyLength,
                                         cy_en_crypto_sha_mode_t mode,
                                         cy_stc_crypto_context_sha_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Str_MemCpy(void *dst,
                                           void const *src,
                                           uint16_t size,
                                           cy_stc_crypto_context_str_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Str_MemSet(void *dst,
                                           uint8_t data,
                                           uint16_t size,
                                           cy_stc_crypto_context_str_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Str_MemCmp(void const *src0,
                                           void const *src1,
                                           uint16_t size,
                                           uint32_t *resultPtr,
                                           cy_stc_crypto_context_str_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Str_MemXor(void const *src0,
                                           void const *src1,
                                           void *dst,
                                           uint16_t size,
                                           cy_stc_crypto_context_str_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Crc_Init(uint32_t polynomial,
                                         uint8_t dataReverse,
                                         uint8_t dataXor,
                                         uint8_t remReverse,
                                         uint32_t remXor,
                                         cy_stc_crypto_context_crc_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Crc_Run(void *data,
                                        uint16_t dataSize,
                                        uint32_t *crc,
                                        uint32_t lfsrInitState,
                                        cy_stc_crypto_context_crc_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Trng_Generate(uint32_t GAROPol,
                                              uint32_t FIROPol,
                                              uint32_t max,
                                              uint32_t *randomNum,
                                              cy_stc_crypto_context_trng_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Des_Run(cy_en_crypto_dir_mode_t dirMode,
                                        uint32_t *key,
                                        uint32_t *dstBlock,
                                        uint32_t *srcBlock,
                                        cy_stc_crypto_context_des_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Tdes_Run(cy_en_crypto_dir_mode_t dirMode,
                                         uint32_t *key,
                                         uint32_t *dstBlock,
                                         uint32_t *srcBlock,
                                         cy_stc_crypto_context_des_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_GetMemBufAddress(uint32_t **membufAddress,
                                           cy_stc_crypto_context_str_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_GetMemBufSize(uint32_t *membufSize,
                                           cy_stc_crypto_context_str_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_SetMemBufAddress(uint32_t const *newMembufAddress,
                                           uint32_t newMembufSize,
                                           cy_stc_crypto_context_str_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Rsa_Proc(cy_stc_crypto_rsa_pub_key_t const *pubKey,
                                         uint32_t const *message,
                                         uint32_t messageSize,
                                         uint32_t *processedMessage,
                                         cy_stc_crypto_context_rsa_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Rsa_CalcCoefs(cy_stc_crypto_rsa_pub_key_t const *pubKey,
                                         cy_stc_crypto_context_rsa_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_Rsa_Verify(cy_en_crypto_rsa_ver_result_t *verResult,
                                           cy_en_crypto_sha_mode_t digestType,
                                           uint32_t const *digest,
                                           uint32_t const *decryptedSignature,
                                           uint32_t decryptedSignatureLength,
                                           cy_stc_crypto_context_rsa_ver_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_ECDSA_SignHash(const uint8_t *hash,
                                        uint32_t hashlen,
                                        uint8_t *sig,
                                        const cy_stc_crypto_ecc_key *key,
                                        const uint8_t *messageKey,
                                        cy_stc_crypto_context_ecc_t *cfContext);
cy_en_crypto_status_t Cy_Crypto_ECDSA_VerifyHash(const uint8_t *sig,
                                        const uint8_t *hash,
                                        uint32_t hashlen,
                                        uint8_t *stat,
                                        const cy_stc_crypto_ecc_key *key,
                                        cy_stc_crypto_context_ecc_t *cfContext);
void Cy_Crypto_InvertEndianness(void *inArrPtr, uint32_t byteSize);
void Cy_Crypto_Core_V1_Aes_ProcessBlock(CRYPTO_Type *base,
                            cy_stc_crypto_aes_state_t const *aesState,
                            cy_en_crypto_dir_mode_t dirMode,
                            uint32_t *dstBlock,
                            uint32_t const *srcBlock);
void Cy_Crypto_Core_V1_Aes_Xor(CRYPTO_Type *base,
                            cy_stc_crypto_aes_state_t const *aesState,
                            uint32_t *dstBlock,
                            uint32_t const *src0Block,
                            uint32_t const *src1Block);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Aes_Free(CRYPTO_Type *base, cy_stc_crypto_aes_state_t *aesState);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Aes_Init(CRYPTO_Type *base,
                                                 uint8_t const *key,
                                                 cy_en_crypto_aes_key_length_t keyLength,
                                                 cy_stc_crypto_aes_state_t *aesState,
                                                 cy_stc_crypto_aes_buffers_t *aesBuffers);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Aes_Ecb(CRYPTO_Type *base,
                                                cy_en_crypto_dir_mode_t dirMode,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Aes_Cbc(CRYPTO_Type *base,
                                                cy_en_crypto_dir_mode_t dirMode,
                                                uint32_t srcSize,
                                                uint8_t *ivPtr,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Aes_Cfb(CRYPTO_Type *base,
                                                cy_en_crypto_dir_mode_t dirMode,
                                                uint32_t srcSize,
                                                uint8_t *ivPtr,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Aes_Ctr(CRYPTO_Type *base,
                                                uint32_t srcSize,
                                                uint32_t *srcOffset,
                                                uint8_t *ivPtr,
                                                uint8_t *streamBlock,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState);

typedef enum
{
    CY_CRYPTO_CTL_ENABLED_DISABLED = 0u,
    CY_CRYPTO_CTL_ENABLED_ENABLED = 1u,
} cy_en_crypto_hw_enable_t;
void Cy_Crypto_Core_ClearVuRegisters(CRYPTO_Type *base);
void Cy_Crypto_Core_Vu_RunInstr(CRYPTO_Type *base, _Bool blockingMode, uint32_t instr, uint32_t params);
cy_en_crypto_status_t Cy_Crypto_Core_Enable(CRYPTO_Type *base);
cy_en_crypto_status_t Cy_Crypto_Core_Disable(CRYPTO_Type *base);
cy_en_crypto_status_t Cy_Crypto_Core_Cleanup(CRYPTO_Type *base);
cy_en_crypto_status_t Cy_Crypto_Core_Shutdown(CRYPTO_Type *base);
cy_en_crypto_status_t Cy_Crypto_Core_GetLibInfo(cy_en_crypto_lib_info_t *libInfo);
cy_en_crypto_status_t Cy_Crypto_Core_SetVuMemoryAddress(CRYPTO_Type *base, uint32_t const *vuMemoryAddr, uint32_t vuMemorySize);
static inline uint32_t * Cy_Crypto_Core_GetVuMemoryAddress(CRYPTO_Type *base);
uint32_t Cy_Crypto_Core_GetVuMemorySize(CRYPTO_Type *base);
void Cy_Crypto_Core_InvertEndianness(void *inArrPtr, uint32_t byteSize);
static inline _Bool Cy_Crypto_Core_IsEnabled(CRYPTO_Type *base)
{
    return (1uL == (uint32_t)(((uint32_t)((((CRYPTO_Type*)(base))->CTL)) & 0x80000000UL) >> 31UL));
}
static inline uint8_t Cy_Crypto_Core_GetFIFODepth(CRYPTO_Type *base)
{
    (void)base;
    return ((8u));
}
static inline uint8_t Cy_Crypto_Core_GetFIFOUsed(CRYPTO_Type *base)
{
    return((uint8_t)(((uint32_t)((((CRYPTO_V1_Type*)(base))->INSTR_FF_STATUS)) & 0xFUL) >> 0UL));
}
static inline void Cy_Crypto_Core_WaitForInstrFifoAvailable(CRYPTO_Type *base, uint32_t instr)
{
    while((uint32_t)((((uint32_t)((((CRYPTO_V1_Type*)(base))->INSTR_FF_STATUS)) & 0xFUL) >> 0UL)) >= ((8u) - instr))
    {
    }
}
static inline void Cy_Crypto_Core_WaitForFifoAvailable(CRYPTO_Type *base)
{
    while(((((uint32_t)((((CRYPTO_V1_Type*)(base))->INSTR_FF_STATUS)) & 0x10000UL) >> 16UL)) == 0u)
    {
    }
}
static inline void Cy_Crypto_Core_WaitForReady(CRYPTO_Type *base)
{
    while((((CRYPTO_V1_Type*)(base))->STATUS) != 0u)
    {
    }
}
static inline void Cy_Crypto_Core_Vu_WaitForComplete(CRYPTO_Type *base)
{
    if ((1U == 1u))
    {
        while (0uL != (((uint32_t)((((CRYPTO_V1_Type*)(base))->STATUS)) & 0x80UL) >> 7UL))
        {
        }
    }
    else
    {
    }
}
static inline void Cy_Crypto_Core_SetInterruptMask(CRYPTO_Type *base, uint32_t interrupts)
{
    (((CRYPTO_V1_Type*)(base))->INTR_MASK) = interrupts;
}
static inline uint32_t Cy_Crypto_Core_GetInterruptMask(CRYPTO_Type const *base)
{
    return ((((CRYPTO_V1_Type*)(base))->INTR_MASK));
}
static inline uint32_t Cy_Crypto_Core_GetInterruptStatusMasked(CRYPTO_Type const *base)
{
    return ((((CRYPTO_V1_Type*)(base))->INTR_MASKED));
}
static inline uint32_t Cy_Crypto_Core_GetInterruptStatus(CRYPTO_Type *base)
{
    return ((((CRYPTO_V1_Type*)(base))->INTR));
}
static inline void Cy_Crypto_Core_SetInterrupt(CRYPTO_Type *base, uint32_t interrupts)
{
    (((CRYPTO_V1_Type*)(base))->INTR_SET) = interrupts;
}
static inline void Cy_Crypto_Core_ClearInterrupt(CRYPTO_Type *base, uint32_t interrupts)
{
    (((CRYPTO_V1_Type*)(base))->INTR) = interrupts;
    (void) (((CRYPTO_V1_Type*)(base))->INTR);
}
static inline uint32_t * Cy_Crypto_Core_GetVuMemoryAddress(CRYPTO_Type *base)
{
    return (uint32_t *)(((CRYPTO_V1_Type*)(base))->VU_CTL1);
}

typedef cy_en_crypto_status_t (*cy_crypto_aes_init_func_t)(CRYPTO_Type *base,
                                                 uint8_t const *key,
                                                 cy_en_crypto_aes_key_length_t keyLength,
                                                 cy_stc_crypto_aes_state_t *aesState,
                                                 cy_stc_crypto_aes_buffers_t *aesBuffers);
typedef cy_en_crypto_status_t (*cy_crypto_aes_ecb_func_t)(CRYPTO_Type *base,
                                                cy_en_crypto_dir_mode_t dirMode,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState);
typedef cy_en_crypto_status_t (*cy_crypto_aes_cbc_func_t)(CRYPTO_Type *base,
                                                cy_en_crypto_dir_mode_t dirMode,
                                                uint32_t srcSize,
                                                uint8_t *ivPtr,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState);
typedef cy_en_crypto_status_t (*cy_crypto_aes_cfb_func_t)(CRYPTO_Type *base,
                                                cy_en_crypto_dir_mode_t dirMode,
                                                uint32_t srcSize,
                                                uint8_t *ivPtr,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState);
typedef cy_en_crypto_status_t (*cy_crypto_aes_ctr_func_t)(CRYPTO_Type *base,
                                                uint32_t srcSize,
                                                uint32_t *srcOffset,
                                                uint8_t *ivPtr,
                                                uint8_t *streamBlock,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState);
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Init(CRYPTO_Type *base,
                                                 uint8_t const *key,
                                                 cy_en_crypto_aes_key_length_t keyLength,
                                                 cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    cy_stc_crypto_aes_buffers_t *aesBuffers = (cy_stc_crypto_aes_buffers_t *)((void *)Cy_Crypto_Core_GetVuMemoryAddress(base));
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Aes_Init(base, key, keyLength, aesState, aesBuffers);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_InitContext(CRYPTO_Type *base,
                                                 uint8_t const *key,
                                                 cy_en_crypto_aes_key_length_t keyLength,
                                                 cy_stc_crypto_aes_state_t *aesState,
                                                 cy_stc_crypto_aes_buffers_t *aesBuffers)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Aes_Init(base, key, keyLength, aesState, aesBuffers);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Free(CRYPTO_Type *base,
                                                 cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Aes_Free(base, aesState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ecb(CRYPTO_Type *base,
                                                cy_en_crypto_dir_mode_t dirMode,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Aes_Ecb(base, dirMode, dst, src, aesState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ecb_Setup(CRYPTO_Type *base,
                                            cy_en_crypto_dir_mode_t dirMode,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)dirMode;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ecb_Update(CRYPTO_Type *base,
                                            uint32_t srcSize,
                                            uint8_t *dst,
                                            uint8_t const *src,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)srcSize;
        (void)dst;
        (void)src;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ecb_Finish(CRYPTO_Type *base, cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Cbc(CRYPTO_Type *base,
                                                cy_en_crypto_dir_mode_t dirMode,
                                                uint32_t srcSize,
                                                uint8_t *ivPtr,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Aes_Cbc(base, dirMode, srcSize, ivPtr, dst, src, aesState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Cbc_Setup(CRYPTO_Type *base,
                                            cy_en_crypto_dir_mode_t dirMode,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)dirMode;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Cbc_Set_IV(CRYPTO_Type *base,
                                            uint8_t const * iv,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)iv;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Cbc_Update(CRYPTO_Type *base,
                                            uint32_t srcSize,
                                            uint8_t *dst,
                                            uint8_t const *src,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)srcSize;
        (void)dst;
        (void)src;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Cbc_Finish(CRYPTO_Type *base, cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_CbcMac_Setup(CRYPTO_Type *base, cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_CbcMac_Update(CRYPTO_Type *base,
                                            uint32_t srcSize,
                                            uint8_t const *src,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)srcSize;
        (void)src;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_CbcMac_Finish(CRYPTO_Type *base, uint8_t *mac, cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)mac;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Cfb(CRYPTO_Type *base,
                                                cy_en_crypto_dir_mode_t dirMode,
                                                uint32_t srcSize,
                                                uint8_t *ivPtr,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Aes_Cfb(base, dirMode, srcSize, ivPtr, dst, src, aesState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Cfb_Setup(CRYPTO_Type *base,
                                            cy_en_crypto_dir_mode_t dirMode,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)dirMode;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Cfb_Set_IV(CRYPTO_Type *base,
                                            uint8_t const * iv,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)iv;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Cfb_Update(CRYPTO_Type *base,
                                             uint32_t srcSize,
                                             uint8_t *dst,
                                             uint8_t const *src,
                                             cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)srcSize;
        (void)dst;
        (void)src;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Cfb_Finish(CRYPTO_Type *base, cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ctr(CRYPTO_Type *base,
                                                uint32_t srcSize,
                                                uint32_t *srcOffset,
                                                uint8_t *ivPtr,
                                                uint8_t *streamBlock,
                                                uint8_t *dst,
                                                uint8_t const *src,
                                                cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Aes_Ctr(base, srcSize, srcOffset, ivPtr, streamBlock, dst, src, aesState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ctr_Setup(CRYPTO_Type *base,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ctr_Set_IV(CRYPTO_Type *base,
                                            const uint8_t *iv,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)iv;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ctr_Update(CRYPTO_Type *base,
                                            uint32_t srcSize,
                                            uint8_t *dst,
                                            uint8_t const *src,
                                            cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)srcSize;
        (void)dst;
        (void)src;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ctr_Finish(CRYPTO_Type *base, cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)aesState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ccm_Init(CRYPTO_Type *base,
                                            cy_stc_crypto_aes_ccm_buffers_t * aesCcmBuffer, cy_stc_crypto_aes_ccm_state_t *aesCcmState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)aesCcmBuffer;
        (void)aesCcmState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ccm_SetKey(CRYPTO_Type *base,
                                            uint8_t const *key, cy_en_crypto_aes_key_length_t keyLength,
                                            cy_stc_crypto_aes_ccm_state_t *aesCcmState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)key;
        (void)keyLength;
        (void)aesCcmState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ccm_Set_Length(CRYPTO_Type *base,
                                            uint32_t aadSize, uint32_t textSize, uint32_t tagLength,
                                            cy_stc_crypto_aes_ccm_state_t *aesCcmState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)aadSize;
        (void)textSize;
        (void)tagLength;
        (void)aesCcmState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ccm_Start(CRYPTO_Type *base,
                                            cy_en_crypto_dir_mode_t dirMode,
                                             uint32_t ivSize, uint8_t const * iv,
                                            cy_stc_crypto_aes_ccm_state_t *aesCcmState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)dirMode;
        (void)ivSize;
        (void)iv;
        (void)aesCcmState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ccm_Update_Aad(CRYPTO_Type *base,
                                            uint32_t aadSize,
                                            uint8_t const *aad,
                                            cy_stc_crypto_aes_ccm_state_t *aesCcmState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)aadSize;
        (void)aad;
        (void)aesCcmState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ccm_Update(CRYPTO_Type *base,
                                            uint32_t srcSize,
                                            uint8_t *dst,
                                            uint8_t const *src,
                                            cy_stc_crypto_aes_ccm_state_t *aesCcmState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)srcSize;
        (void)dst;
        (void)src;
        (void)aesCcmState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ccm_Finish(CRYPTO_Type *base, uint8_t *tag, cy_stc_crypto_aes_ccm_state_t *aesCcmState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)tag;
        (void)aesCcmState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ccm_Encrypt_Tag(CRYPTO_Type *base,
                                            uint32_t ivSize, uint8_t const * iv,
                                            uint32_t aadSize, uint8_t const *aad,
                                            uint32_t srcSize, uint8_t *cipherTxt, uint8_t const *plainTxt,
                                            uint32_t tagSize, uint8_t *tag,
                                            cy_stc_crypto_aes_ccm_state_t *aesCcmState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)ivSize;
        (void)iv;
        (void)aadSize;
        (void)aad;
        (void)srcSize;
        (void)cipherTxt;
        (void)plainTxt;
        (void)tagSize;
        (void)tag;
        (void)aesCcmState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ccm_Decrypt(CRYPTO_Type *base,
                                            uint32_t ivSize, uint8_t const * iv,
                                            uint32_t aadSize, uint8_t const *aad,
                                            uint32_t srcSize, uint8_t *plainTxt, uint8_t const *cipherTxt,
                                            uint32_t tagSize, uint8_t const *tag, cy_en_crypto_aesccm_tag_verify_result_t *isValid,
                                            cy_stc_crypto_aes_ccm_state_t *aesCcmState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)ivSize;
        (void)iv;
        (void)aadSize;
        (void)aad;
        (void)srcSize;
        (void)cipherTxt;
        (void)plainTxt;
        (void)tagSize;
        (void)tag;
        (void)isValid;
        (void)aesCcmState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Aes_Ccm_Free(CRYPTO_Type *base, cy_stc_crypto_aes_ccm_state_t *aesCcmState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)aesCcmState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
cy_en_crypto_status_t Cy_Crypto_Core_V1_Crc_Init(CRYPTO_Type *base,
                                        uint32_t polynomial,
                                        uint32_t dataReverse,
                                        uint32_t dataXor,
                                        uint32_t remReverse,
                                        uint32_t remXor);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Crc(CRYPTO_Type *base,
                                        uint32_t *crc,
                                        void const *data,
                                        uint32_t dataSize,
                                        uint32_t lfsrInitState);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Crc_CalcInit(CRYPTO_Type *base,
                                        uint32_t width,
                                        uint32_t polynomial,
                                        uint32_t dataReverse,
                                        uint32_t dataXor,
                                        uint32_t remReverse,
                                        uint32_t remXor,
                                        uint32_t lfsrInitState);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Crc_CalcStart(CRYPTO_Type *base, uint32_t width, uint32_t lfsrInitState);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Crc_CalcPartial(CRYPTO_Type *base, void const *data, uint32_t dataSize);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Crc_CalcFinish(CRYPTO_Type *base, uint32_t width, uint32_t *crc);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Crc_Calc(CRYPTO_Type *base,
                                        uint32_t width,
                                        uint32_t *crc,
                                        void const *data,
                                        uint32_t dataSize);
typedef cy_en_crypto_status_t (*cy_crypto_crc_init_func_t)(CRYPTO_Type *base,
                                        uint32_t polynomial,
                                        uint32_t dataReverse,
                                        uint32_t dataXor,
                                        uint32_t remReverse,
                                        uint32_t remXor);
typedef cy_en_crypto_status_t (*cy_crypto_crc_func_t)(CRYPTO_Type *base,
                                        uint32_t *crc,
                                        void const *data,
                                        uint32_t dataSize,
                                        uint32_t lfsrInitState);
static inline cy_en_crypto_status_t Cy_Crypto_Core_Crc_Init(CRYPTO_Type *base,
                                        uint32_t polynomial,
                                        uint32_t dataReverse,
                                        uint32_t dataXor,
                                        uint32_t remReverse,
                                        uint32_t remXor)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Crc_Init(base, polynomial, dataReverse, dataXor, remReverse, remXor);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Crc(CRYPTO_Type *base,
                                        uint32_t *crc,
                                        void const *data,
                                        uint32_t dataSize,
                                        uint32_t lfsrInitState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Crc(base, crc, data, dataSize, lfsrInitState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Crc_CalcInit(CRYPTO_Type *base,
                                        uint32_t width,
                                        uint32_t polynomial,
                                        uint32_t dataReverse,
                                        uint32_t dataXor,
                                        uint32_t remReverse,
                                        uint32_t remXor,
                                        uint32_t lfsrInitState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Crc_CalcInit(base, width, polynomial, dataReverse, dataXor,
                                                 remReverse, remXor, lfsrInitState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Crc_CalcStart(CRYPTO_Type *base,
                                                                   uint32_t width, uint32_t lfsrInitState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Crc_CalcStart(base, width, lfsrInitState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Crc_CalcPartial(CRYPTO_Type *base,
                                                                     void const *data, uint32_t dataSize)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Crc_CalcPartial(base, data, dataSize);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Crc_CalcFinish(CRYPTO_Type *base, uint32_t width, uint32_t *crc)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Crc_CalcFinish(base, width, crc);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Crc_Calc(CRYPTO_Type *base,
                                                              uint32_t width, uint32_t *crc,
                                                              void const *data, uint32_t dataSize)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Crc_Calc(base, width, crc, data, dataSize);
    }
    else
    {
    }
    return tmpResult;
}
typedef struct
{
    uint32_t *block;
    uint32_t *k;
    uint32_t *temp;
} cy_stc_crypto_v1_cmac_state_t;
typedef struct
{
    uint32_t k[(uint32_t)((16u) / 4UL)];
    uint32_t block0[(uint32_t)((16u) / 4UL)];
    uint32_t block1[(uint32_t)((16u) / 4UL)];
    cy_stc_crypto_v1_cmac_state_t cmacState;
} cy_stc_crypto_v1_cmac_buffers_t;
void Cy_Crypto_Core_V1_Cmac_Init(cy_stc_crypto_v1_cmac_state_t *cmacState,
                              uint32_t *temp,
                              uint32_t *block,
                              uint32_t *k);
void Cy_Crypto_Core_V1_Cmac_Start(CRYPTO_Type *base,
                                cy_stc_crypto_aes_state_t *aesState,
                                cy_stc_crypto_v1_cmac_state_t *cmacState);
void Cy_Crypto_Core_V1_Cmac_Update(CRYPTO_Type *base, cy_stc_crypto_aes_state_t *aesState,
                                cy_stc_crypto_v1_cmac_state_t *cmacState,
                                uint8_t const *message,
                                uint32_t messageSize);
void Cy_Crypto_Core_V1_Cmac_Finish(CRYPTO_Type *base,
                                cy_stc_crypto_aes_state_t *aesState,
                                cy_stc_crypto_v1_cmac_state_t *cmacState,
                                uint8_t* cmac);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Cmac(CRYPTO_Type *base,
                                          uint8_t const *message,
                                          uint32_t messageSize,
                                          uint8_t const *key,
                                          cy_en_crypto_aes_key_length_t keyLength,
                                          uint8_t *cmac,
                                          cy_stc_crypto_aes_state_t *aesState);
typedef cy_en_crypto_status_t (*cy_crypto_cmac_func_t)(CRYPTO_Type *base,
                                          uint8_t const *src,
                                          uint32_t srcSize,
                                          uint8_t const *key,
                                          cy_en_crypto_aes_key_length_t keyLength,
                                          uint8_t *dst,
                                          cy_stc_crypto_aes_state_t *aesState);
static inline cy_en_crypto_status_t Cy_Crypto_Core_Cmac(CRYPTO_Type *base,
                                          uint8_t const *message,
                                          uint32_t messageSize,
                                          uint8_t const *key,
                                          cy_en_crypto_aes_key_length_t keyLength,
                                          uint8_t *cmac,
                                          cy_stc_crypto_aes_state_t *aesState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Cmac(base, message, messageSize, key, keyLength, cmac, aesState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Cmac_Init(CRYPTO_Type *base, void* cmacState, void *buffer)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)cmacState;
        (void)buffer;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Cmac_Start(CRYPTO_Type *base, void *cmacState,
                                                                uint8_t const *aesKey, cy_en_crypto_aes_key_length_t keyLength)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)cmacState;
        (void)aesKey;
        (void)keyLength;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Cmac_Update(CRYPTO_Type *base,
                                                                void *cmacState,
                                                                uint8_t const *message,
                                                                uint32_t messageSize)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)cmacState;
        (void)message;
        (void)messageSize;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Cmac_Finish(CRYPTO_Type *base, void *cmacState, uint8_t* cmac)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)cmacState;
        (void)cmac;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Cmac_Free(CRYPTO_Type *base,
                                void *cmacState
                                )
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        (void)base;
        (void)cmacState;
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    return tmpResult;
}
cy_en_crypto_status_t Cy_Crypto_Core_V1_Des(CRYPTO_Type *base,
                                        cy_en_crypto_dir_mode_t dirMode,
                                        uint8_t const *key,
                                        uint8_t *dst,
                                        uint8_t const *src);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Tdes(CRYPTO_Type *base,
                                        cy_en_crypto_dir_mode_t dirMode,
                                        uint8_t const *key,
                                        uint8_t *dst,
                                        uint8_t const *src);
typedef cy_en_crypto_status_t (*cy_crypto_des_func_t)(CRYPTO_Type *base,
                                        cy_en_crypto_dir_mode_t dirMode,
                                        uint8_t const *key,
                                        uint8_t *dst,
                                        uint8_t const *src);
static inline cy_en_crypto_status_t Cy_Crypto_Core_Des(CRYPTO_Type *base,
                                        cy_en_crypto_dir_mode_t dirMode,
                                        uint8_t const *key,
                                        uint8_t *dst,
                                        uint8_t const *src)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Des(base, dirMode, key, dst, src);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Tdes(CRYPTO_Type *base,
                                        cy_en_crypto_dir_mode_t dirMode,
                                        uint8_t const *key,
                                        uint8_t *dst,
                                        uint8_t const *src)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Tdes(base, dirMode, key, dst, src);
    }
    else
    {
    }
    return tmpResult;
}

typedef enum cy_en_red_mul_algs {
    CY_CRYPTO_NIST_P_CURVE_SPECIFIC_RED_ALG = 0,
    CY_CRYPTO_NIST_P_SHIFT_MUL_RED_ALG,
    CY_CRYPTO_NIST_P_BARRETT_RED_ALG
} cy_en_crypto_ecc_red_mul_algs_t;
typedef struct {
    cy_en_crypto_ecc_curve_id_t id;
    uint32_t size;
    const char_t *name;
    cy_en_crypto_ecc_red_mul_algs_t algo;
    const uint8_t *prime;
    const uint8_t *barrett_p;
    const uint8_t *order;
    const uint8_t *barrett_o;
    const uint8_t *Gx;
    const uint8_t *Gy;
} cy_stc_crypto_ecc_dp_type;
cy_stc_crypto_ecc_dp_type *Cy_Crypto_Core_ECC_GetCurveParams(cy_en_crypto_ecc_curve_id_t curveId);
typedef int (*cy_func_get_random_data_t)(void *rndInfo, uint8_t *rndData, size_t rndSize);
cy_en_crypto_status_t Cy_Crypto_Core_ECC_MakePrivateKey(CRYPTO_Type *base,
        cy_en_crypto_ecc_curve_id_t curveID, uint8_t *key,
        cy_func_get_random_data_t GetRandomDataFunc, void *randomDataInfo);
cy_en_crypto_status_t Cy_Crypto_Core_ECC_MakePublicKey(CRYPTO_Type *base,
        cy_en_crypto_ecc_curve_id_t curveID,
        const uint8_t *privateKey, cy_stc_crypto_ecc_key *publicKey);
cy_en_crypto_status_t Cy_Crypto_Core_ECC_MakeKeyPair(CRYPTO_Type *base,
        cy_en_crypto_ecc_curve_id_t curveID,
        cy_stc_crypto_ecc_key *key,
        cy_func_get_random_data_t GetRandomDataFunc, void *randomDataInfo);
cy_en_crypto_status_t Cy_Crypto_Core_ECC_SignHash(CRYPTO_Type *base,
                                    const uint8_t *hash,
                                    uint32_t hashlen,
                                    uint8_t *sig,
                                    const cy_stc_crypto_ecc_key *key,
                                    const uint8_t *messageKey);
cy_en_crypto_status_t Cy_Crypto_Core_ECC_VerifyHash(CRYPTO_Type *base,
                                    const uint8_t *sig,
                                    const uint8_t *hash,
                                    uint32_t hashlen,
                                    uint8_t *stat,
                                    const cy_stc_crypto_ecc_key *key);

void Cy_Crypto_Core_EC_NistP_SetMode(uint32_t bitsize);
void Cy_Crypto_Core_EC_NistP_SetRedAlg(cy_en_crypto_ecc_red_mul_algs_t alg);
cy_en_crypto_status_t Cy_Crypto_Core_EC_NistP_PointMultiplication(CRYPTO_Type *base,
    cy_en_crypto_ecc_curve_id_t curveID,
    const uint8_t *ecpGX,
    const uint8_t *ecpGY,
    const uint8_t *ecpD,
    uint8_t *ecpQX,
    uint8_t *ecpQY);
cy_en_crypto_status_t Cy_Crypto_Core_EC_MulMod( CRYPTO_Type *base, uint32_t z, uint32_t a, uint32_t b, uint32_t size);
cy_en_crypto_status_t Cy_Crypto_Core_EC_DivMod( CRYPTO_Type *base, uint32_t z, uint32_t a, uint32_t b, uint32_t size);
cy_en_crypto_status_t Cy_Crypto_Core_EC_SquareMod( CRYPTO_Type *base, uint32_t z, uint32_t a, uint32_t size);
cy_en_crypto_status_t Cy_Crypto_Core_EC_Bar_MulRed(CRYPTO_Type *base, uint32_t z, uint32_t x, uint32_t size);
void Cy_Crypto_Core_EC_AddMod( CRYPTO_Type *base, uint32_t z, uint32_t a, uint32_t b);
void Cy_Crypto_Core_EC_SubMod( CRYPTO_Type *base, uint32_t z, uint32_t a, uint32_t b);
void Cy_Crypto_Core_EC_HalfMod( CRYPTO_Type *base, uint32_t z, uint32_t a);
cy_en_crypto_status_t Cy_Crypto_Core_JacobianEcAdd(CRYPTO_Type *base, uint32_t s_x, uint32_t s_y, uint32_t s_z, uint32_t t_x, uint32_t t_y, uint32_t size);
cy_en_crypto_status_t Cy_Crypto_Core_JacobianEcDouble(CRYPTO_Type *base, uint32_t s_x, uint32_t s_y, uint32_t s_z, uint32_t size);
cy_en_crypto_status_t Cy_Crypto_Core_JacobianEcScalarMul(CRYPTO_Type *base, uint32_t s_x, uint32_t s_y, uint32_t d, uint32_t size);
void Cy_Crypto_Core_JacobianTransform(CRYPTO_Type *base, uint32_t s_x, uint32_t s_y, uint32_t s_z);
cy_en_crypto_status_t Cy_Crypto_Core_JacobianInvTransform(CRYPTO_Type *base, uint32_t s_x, uint32_t s_y, uint32_t s_z, uint32_t size);
cy_en_crypto_status_t Cy_Crypto_Core_EC_NistP_PointMul(CRYPTO_Type *base, uint32_t p_x, uint32_t p_y, uint32_t p_d, uint32_t p_order, uint32_t bitsize);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Hmac(CRYPTO_Type *base,
                                          uint8_t *hmac,
                                          uint8_t const *message,
                                          uint32_t messageSize,
                                          uint8_t const *key,
                                          uint32_t keyLength,
                                          cy_en_crypto_sha_mode_t mode);
typedef cy_en_crypto_status_t (*cy_crypto_hmac_func_t)(CRYPTO_Type *base,
                                          uint8_t *hmac,
                                          uint8_t const *message,
                                          uint32_t messageSize,
                                          uint8_t const *key,
                                          uint32_t keyLength,
                                          cy_en_crypto_sha_mode_t mode);
static inline cy_en_crypto_status_t Cy_Crypto_Core_Hmac(CRYPTO_Type *base,
                                          uint8_t *hmac,
                                          uint8_t const *message,
                                          uint32_t messageSize,
                                          uint8_t const *key,
                                          uint32_t keyLength,
                                          cy_en_crypto_sha_mode_t mode)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Hmac(base, hmac, message, messageSize, key, keyLength, mode);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Hmac_Init(CRYPTO_Type *base, cy_stc_crypto_hmac_state_t *hmacState, cy_en_crypto_sha_mode_t mode, void *hmacBuffer)
{
    cy_en_crypto_status_t tmpResult;
    if ((1U == 1u))
    {
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    (void)base;
    (void)hmacState;
    (void)mode;
    (void)hmacBuffer;
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Hmac_Start(CRYPTO_Type *base, cy_stc_crypto_hmac_state_t *hmacState,
                                        uint8_t const *key,
                                        uint32_t keyLength
                                        )
{
    cy_en_crypto_status_t tmpResult;
    if ((1U == 1u))
    {
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    (void)base;
    (void)hmacState;
    (void)key;
    (void)keyLength;
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Hmac_Update(CRYPTO_Type *base, cy_stc_crypto_hmac_state_t *hmacState,
                                   uint8_t const *message,
                                   uint32_t messageSize
                                   )
{
    cy_en_crypto_status_t tmpResult;
    if ((1U == 1u))
    {
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    (void)base;
    (void)hmacState;
    (void)message;
    (void)messageSize;
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Hmac_Finish(CRYPTO_Type *base, cy_stc_crypto_hmac_state_t *hmacState,
                                                    uint8_t *hmac)
{
    cy_en_crypto_status_t tmpResult;
    if ((1U == 1u))
    {
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    (void)base;
    (void)hmac;
    (void)hmacState;
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Hmac_Free(CRYPTO_Type *base, cy_stc_crypto_hmac_state_t *hmacState)
{
    cy_en_crypto_status_t tmpResult;
    if ((1U == 1u))
    {
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    }
    else
    {
    }
    (void)base;
    (void)hmacState;
    return tmpResult;
}
cy_en_crypto_status_t Cy_Crypto_Core_V1_Prng_Init(CRYPTO_Type *base,
                                                  uint32_t lfsr32InitState,
                                                  uint32_t lfsr31InitState,
                                                  uint32_t lfsr29InitState);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Prng(CRYPTO_Type *base,
                                             uint32_t max,
                                             uint32_t *randomNum);
typedef cy_en_crypto_status_t (*cy_crypto_prng_init_func_t)(CRYPTO_Type *base,
                                                  uint32_t lfsr32InitState,
                                                  uint32_t lfsr31InitState,
                                                  uint32_t lfsr29InitState);
typedef cy_en_crypto_status_t (*cy_crypto_prng_func_t)(CRYPTO_Type *base,
                                             uint32_t max,
                                             uint32_t *randomNum);
static inline cy_en_crypto_status_t Cy_Crypto_Core_Prng_Init(CRYPTO_Type *base,
                                                  uint32_t lfsr32InitState,
                                                  uint32_t lfsr31InitState,
                                                  uint32_t lfsr29InitState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Prng_Init(base, lfsr32InitState, lfsr31InitState, lfsr29InitState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Prng(CRYPTO_Type *base,
                                             uint32_t max,
                                             uint32_t *randomNum)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Prng(base, max, randomNum);
    }
    else
    {
    }
    return tmpResult;
}
void Cy_Crypto_Core_V1_MemCpy(CRYPTO_Type *base,
                               void* dst, void const *src, uint16_t size);
void Cy_Crypto_Core_V1_MemSet(CRYPTO_Type *base,
                               void* dst, uint8_t data, uint16_t size);
uint32_t Cy_Crypto_Core_V1_MemCmp(CRYPTO_Type *base,
                               void const *src0, void const *src1, uint16_t size);
void Cy_Crypto_Core_V1_MemXor(CRYPTO_Type *base, void* dst,
                               void const *src0, void const *src1, uint16_t size);
typedef void (*cy_crypto_memcpy_func_t)(CRYPTO_Type *base,
                               void* dst, void const *src, uint16_t size);
typedef void (*cy_crypto_memset_func_t)(CRYPTO_Type *base,
                               void* dst, uint8_t data, uint16_t size);
typedef uint32_t (*cy_crypto_memcmp_func_t)(CRYPTO_Type *base,
                               void const *src0, void const *src1, uint16_t size);
typedef void (*cy_crypto_memxor_func_t)(CRYPTO_Type *base, void* dst,
                               void const *src0, void const *src1, uint16_t size);
static inline void Cy_Crypto_Core_MemCpy(CRYPTO_Type *base, void* dst, void const *src, uint16_t size)
{
    if ((1U == 1u))
    {
        Cy_Crypto_Core_V1_MemCpy(base, dst, src, size);
    }
    else
    {
    }
}
static inline void Cy_Crypto_Core_MemSet(CRYPTO_Type *base, void* dst, uint8_t data, uint16_t size)
{
    if ((1U == 1u))
    {
        Cy_Crypto_Core_V1_MemSet(base, dst, data, size);
    }
    else
    {
    }
}
static inline uint32_t Cy_Crypto_Core_MemCmp(CRYPTO_Type *base, void const *src0, void const *src1, uint16_t size)
{
    uint32_t tmpResult = 1u;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_MemCmp(base, src0, src1, size);
    }
    else
    {
    }
    return (tmpResult);
}
static inline void Cy_Crypto_Core_MemXor(CRYPTO_Type *base, void* dst,
                                           void const *src0, void const *src1, uint16_t size)
{
    if ((1U == 1u))
    {
        Cy_Crypto_Core_V1_MemXor(base, dst, src0, src1, size);
    }
    else
    {
    }
}
typedef cy_en_crypto_status_t (*cy_crypto_rsa_proc_func_t)(CRYPTO_Type *base,
                                              cy_stc_crypto_rsa_pub_key_t const *key,
                                              uint8_t const *message,
                                              uint32_t messageSize,
                                              uint8_t *processedMessage);
typedef cy_en_crypto_status_t (*cy_crypto_rsa_coef_func_t)(CRYPTO_Type *base,
                                              cy_stc_crypto_rsa_pub_key_t const *key);
cy_en_crypto_status_t Cy_Crypto_Core_Rsa_Proc(CRYPTO_Type *base,
                                              cy_stc_crypto_rsa_pub_key_t const *key,
                                              uint8_t const *message,
                                              uint32_t messageSize,
                                              uint8_t *processedMessage);
cy_en_crypto_status_t Cy_Crypto_Core_Rsa_Coef(CRYPTO_Type *base,
                                              cy_stc_crypto_rsa_pub_key_t const *key);
typedef cy_en_crypto_status_t (*cy_crypto_rsa_ver_func_t)(CRYPTO_Type *base,
                                              cy_en_crypto_rsa_ver_result_t *verResult,
                                              cy_en_crypto_sha_mode_t digestType,
                                              uint8_t const *digest,
                                              uint8_t const *decryptedSignature,
                                              uint32_t decryptedSignatureLength);
cy_en_crypto_status_t Cy_Crypto_Core_Rsa_Verify(CRYPTO_Type *base,
                            cy_en_crypto_rsa_ver_result_t *verResult,
                            cy_en_crypto_sha_mode_t digestType,
                            uint8_t const *digest,
                            uint8_t const *decryptedSignature,
                            uint32_t decryptedSignatureLength);
cy_en_crypto_status_t Cy_Crypto_Core_Rsa_Verify_Ext(CRYPTO_Type *base,
                            cy_en_crypto_rsa_ver_result_t *verResult,
                            cy_en_crypto_sha_mode_t digestType,
                            uint8_t const *digest,
                            uint32_t digestLength,
                            uint8_t const *decryptedSignature,
                            uint32_t decryptedSignatureLength);
cy_en_crypto_status_t Cy_Crypto_Core_Rsa_Sign(CRYPTO_Type *base,
                            cy_en_crypto_sha_mode_t digestType,
                            uint8_t const *digest,
                            uint32_t digestLength,
                            uint8_t *signature,
                            uint32_t signatureLength);
typedef struct
{
    uint32_t block[(64u) / 4u];
    uint32_t hash[(20u) / 4u];
    uint32_t roundMem[(320uL) / 4u];
} cy_stc_crypto_v1_sha1_buffers_t;
typedef struct
{
    uint32_t block[(64u) / 4u];
    uint32_t hash[(32u) / 4u];
    uint32_t roundMem[(256uL) / 4u];
} cy_stc_crypto_v1_sha256_buffers_t;
typedef struct
{
    uint32_t block[(128u) / 4u];
    uint32_t hash[(64u) / 4u];
    uint32_t roundMem[(640uL) / 4u];
} cy_stc_crypto_v1_sha512_buffers_t;
typedef struct
{
    uint32_t block[((200u)) / 4u];
    uint32_t hash[((200u)) / 4u];
    uint32_t roundMem[((640uL)) / 4u];
} cy_stc_crypto_v1_sha_buffers_t;
void Cy_Crypto_Core_V1_Sha_ProcessBlock(CRYPTO_Type *base,
                                cy_stc_crypto_sha_state_t *hashState,
                                uint8_t const *block);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Sha_Init(CRYPTO_Type *base,
                                cy_stc_crypto_sha_state_t *hashState,
                                cy_en_crypto_sha_mode_t mode,
                                void *shaBuffers);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Sha_Start(CRYPTO_Type *base,
                                cy_stc_crypto_sha_state_t *hashState);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Sha_Update(CRYPTO_Type *base,
                                cy_stc_crypto_sha_state_t *hashState,
                                uint8_t const *message,
                                uint32_t messageSize);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Sha_Finish(CRYPTO_Type *base,
                                cy_stc_crypto_sha_state_t *hashState,
                                uint8_t *digest);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Sha_Free(CRYPTO_Type *base,
                                cy_stc_crypto_sha_state_t *hashState);
cy_en_crypto_status_t Cy_Crypto_Core_V1_Sha(CRYPTO_Type *base,
                                uint8_t const *message,
                                uint32_t messageSize,
                                uint8_t *digest,
                                cy_en_crypto_sha_mode_t mode);
typedef cy_en_crypto_status_t (*cy_crypto_sha_func_t)(CRYPTO_Type *base,
                                         uint8_t const *message,
                                         uint32_t messageSize,
                                         uint8_t *digest,
                                         cy_en_crypto_sha_mode_t mode);
static inline cy_en_crypto_status_t Cy_Crypto_Core_Sha(CRYPTO_Type *base,
                                uint8_t const *message,
                                uint32_t messageSize,
                                uint8_t *digest,
                                cy_en_crypto_sha_mode_t mode)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Sha(base, message, messageSize, digest, mode);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Sha_Init(CRYPTO_Type *base,
                             cy_stc_crypto_sha_state_t *shaHashState,
                             cy_en_crypto_sha_mode_t mode,
                             void *shaBuffers)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Sha_Init(base, shaHashState, mode, shaBuffers);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Sha_Start(CRYPTO_Type *base, cy_stc_crypto_sha_state_t *hashState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Sha_Start(base, hashState);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Sha_Update(CRYPTO_Type *base,
                               cy_stc_crypto_sha_state_t *hashState,
                               uint8_t const *message,
                               uint32_t messageSize)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Sha_Update(base, hashState, message, messageSize);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Sha_Finish(CRYPTO_Type *base,
                               cy_stc_crypto_sha_state_t *hashState,
                               uint8_t *digest)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Sha_Finish(base, hashState, digest);
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Sha_Free(CRYPTO_Type *base, cy_stc_crypto_sha_state_t *hashState)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = Cy_Crypto_Core_V1_Sha_Free(base, hashState);
    }
    else
    {
    }
    return tmpResult;
}

typedef cy_en_crypto_status_t (*cy_crypto_trng_func_t)(CRYPTO_Type *base,
                                             uint32_t GAROPol,
                                             uint32_t FIROPol,
                                             uint32_t max,
                                             uint32_t *randomNum);
void Cy_Crypto_Core_Trng_Init(CRYPTO_Type *base, cy_stc_crypto_trng_config_t *config);
void Cy_Crypto_Core_Trng_DeInit(CRYPTO_Type *base);
cy_en_crypto_status_t Cy_Crypto_Core_Trng_Start(CRYPTO_Type *base, uint32_t dataSize);
cy_en_crypto_status_t Cy_Crypto_Core_Trng_ReadData(CRYPTO_Type *base, uint32_t *randomData);
cy_en_crypto_status_t Cy_Crypto_Core_Trng(CRYPTO_Type *base,
                                             uint32_t GAROPol,
                                             uint32_t FIROPol,
                                             uint32_t max,
                                             uint32_t *randomNum);
static inline cy_en_crypto_status_t Cy_Crypto_Core_Trng_Ext(CRYPTO_Type *base,
                                             uint32_t max,
                                             uint32_t *randomNum)
{
    return Cy_Crypto_Core_Trng(base, (0x04c11db7), (0x04c11db7), max, randomNum);
}
extern const cy_stc_crypto_trng_config_t cy_trngDefaultConfig;
static inline _Bool Cy_Crypto_Core_Trng_IsInitialized(CRYPTO_Type *base);
static inline uint8_t Cy_Crypto_Core_Trng_GetRoStatus(CRYPTO_Type *base, cy_en_crypto_trng_ro_sel_t roSelector);
static inline void Cy_Crypto_Core_Trng_SetRoStatus(CRYPTO_Type *base,
                                                     cy_en_crypto_trng_ro_sel_t roSelector, uint8_t roStatus);
static inline _Bool Cy_Crypto_Core_Trng_IsRoEnabled(CRYPTO_Type *base, cy_en_crypto_trng_ro_sel_t roSelector);
static inline _Bool Cy_Crypto_Core_Trng_AnyRoEnabled(CRYPTO_Type *base);
static inline uint32_t Cy_Crypto_Core_Trng_GetData(CRYPTO_Type *base);
static inline void Cy_Crypto_Core_Trng_SetData(CRYPTO_Type *base, uint32_t randomData);
static inline void Cy_Crypto_Core_Trng_SetGaroPoly(CRYPTO_Type *base, uint32_t poly);
static inline void Cy_Crypto_Core_Trng_SetFiroPoly(CRYPTO_Type *base, uint32_t poly);
static inline uint32_t Cy_Crypto_Core_Trng_GetGaroPoly(CRYPTO_Type *base);
static inline uint32_t Cy_Crypto_Core_Trng_GetFiroPoly(CRYPTO_Type *base);
static inline uint8_t Cy_Crypto_Core_Trng_MonGetHealthStatus(CRYPTO_Type *base);
static inline uint8_t Cy_Crypto_Core_Trng_MonGetRcRepCount(CRYPTO_Type *base);
static inline uint16_t Cy_Crypto_Core_Trng_MonGetApOccCount(CRYPTO_Type *base);
static inline uint16_t Cy_Crypto_Core_Trng_MonGetApWindowIndex(CRYPTO_Type *base);
static inline uint8_t Cy_Crypto_Core_Trng_MonGetRcCurrentBit(CRYPTO_Type *base);
static inline uint8_t Cy_Crypto_Core_Trng_MonGetApCurrentBit(CRYPTO_Type *base);
static inline cy_en_crypto_status_t Cy_Crypto_Core_Trng_MonSetBSSelector(CRYPTO_Type *base, cy_en_crypto_trng_bs_sel_t bitStreamSelector);
static inline cy_en_crypto_trng_bs_sel_t Cy_Crypto_Core_Trng_MonGetBSSelector(CRYPTO_Type *base);
static inline void Cy_Crypto_Core_Trng_MonEnableApTest(CRYPTO_Type *base);
static inline void Cy_Crypto_Core_Trng_MonDisableApTest(CRYPTO_Type *base);
static inline void Cy_Crypto_Core_Trng_MonEnableRcTest(CRYPTO_Type *base);
static inline void Cy_Crypto_Core_Trng_MonDisableRcTest(CRYPTO_Type *base);
static inline void Cy_Crypto_Core_Trng_MonSetRcCC8(CRYPTO_Type *base, uint8_t ccCount);
static inline uint8_t Cy_Crypto_Core_Trng_MonGetRcCC8(CRYPTO_Type *base);
static inline void Cy_Crypto_Core_Trng_MonSetApCC16(CRYPTO_Type *base, uint16_t ccCount);
static inline uint16_t Cy_Crypto_Core_Trng_MonGetApCC16(CRYPTO_Type *base);
static inline void Cy_Crypto_Core_Trng_MonSetApWinSize(CRYPTO_Type *base, uint16_t windowSize);
static inline uint16_t Cy_Crypto_Core_Trng_MonGetApWinSize(CRYPTO_Type *base);
static inline void Cy_Crypto_Core_Trng_WaitForReady(CRYPTO_Type *base);
static inline void Cy_Crypto_Core_Trng_WaitForComplete(CRYPTO_Type *base);
static inline _Bool Cy_Crypto_Core_Trng_IsReady(CRYPTO_Type *base)
{
    _Bool status = 0;
    if ((1U == 1u))
    {
        status = (0uL == ((((CRYPTO_V1_Type*)(base))->STATUS) & 0x40UL));
    }
    else
    {
    }
    return status;
}
static inline _Bool Cy_Crypto_Core_Trng_IsRandomComplete(CRYPTO_Type *base)
{
    uint32_t status;
    status = Cy_Crypto_Core_GetInterruptStatus(base) & (0x8UL | 0x80000UL | 0x100000UL);
    return (status != 0UL);
}
static inline _Bool Cy_Crypto_Core_Trng_IsInitialized(CRYPTO_Type *base)
{
    return ((Cy_Crypto_Core_GetInterruptStatus(base) & 0x4UL) != 0U);
}
static inline void Cy_Crypto_Core_Trng_WaitForComplete(CRYPTO_Type *base)
{
    uint32_t status;
    do
    {
        status = Cy_Crypto_Core_GetInterruptStatus(base) & (0x8UL |
                                                            0x80000UL |
                                                            0x100000UL);
    }
    while (status == 0U);
}
static inline void Cy_Crypto_Core_Trng_WaitForReady(CRYPTO_Type *base)
{
    if ((1U == 1u))
    {
        while (0uL != ((((CRYPTO_V1_Type*)(base))->STATUS) & 0x40UL))
        {
        }
    }
    else
    {
    }
}
static inline uint8_t Cy_Crypto_Core_Trng_GetRoStatus(CRYPTO_Type *base, cy_en_crypto_trng_ro_sel_t roSelector)
{
    do{}while(0);
    return ((((CRYPTO_Type*)(base))->TR_CTL1) & (uint32_t)(1U << ((uint32_t)roSelector))) != 0U ? 1U : 0U;
}
static inline void Cy_Crypto_Core_Trng_SetRoStatus(CRYPTO_Type *base,
                                                        cy_en_crypto_trng_ro_sel_t roSelector, uint8_t roStatus)
{
    do{}while(0);
    uint32_t roMask = 1U << (uint32_t)roSelector;
    uint32_t roData = ((((CRYPTO_Type*)(base))->TR_CTL1) & ~roMask) | (((uint32_t)roStatus != 0U) ? roMask : 0U);
    (((CRYPTO_Type*)(base))->TR_CTL1) = roData;
}
static inline _Bool Cy_Crypto_Core_Trng_IsRoEnabled(CRYPTO_Type *base, cy_en_crypto_trng_ro_sel_t roSelector)
{
    return (Cy_Crypto_Core_Trng_GetRoStatus(base, roSelector) != 0U);
}
static inline _Bool Cy_Crypto_Core_Trng_AnyRoEnabled(CRYPTO_Type *base)
{
    return (((((CRYPTO_Type*)(base))->TR_CTL1) & (uint32_t)(0x1UL | 0x2UL | 0x4UL | 0x8UL | 0x10UL | 0x20UL)) != 0U);
}
static inline uint32_t Cy_Crypto_Core_Trng_GetData(CRYPTO_Type *base)
{
    return (((CRYPTO_V1_Type*)(base))->TR_RESULT);
}
static inline void Cy_Crypto_Core_Trng_SetData(CRYPTO_Type *base, uint32_t randomData)
{
    (((CRYPTO_V1_Type*)(base))->TR_RESULT) = randomData;
}
static inline void Cy_Crypto_Core_Trng_SetGaroPoly(CRYPTO_Type *base, uint32_t poly)
{
    (((CRYPTO_Type*)(base))->TR_GARO_CTL) = poly & 0x7FFFFFFFUL;
}
static inline void Cy_Crypto_Core_Trng_SetFiroPoly(CRYPTO_Type *base, uint32_t poly)
{
    (((CRYPTO_Type*)(base))->TR_FIRO_CTL) = poly & 0x7FFFFFFFUL;
}
static inline uint32_t Cy_Crypto_Core_Trng_GetGaroPoly(CRYPTO_Type *base)
{
    return (((CRYPTO_Type*)(base))->TR_GARO_CTL);
}
static inline uint32_t Cy_Crypto_Core_Trng_GetFiroPoly(CRYPTO_Type *base)
{
    return (((CRYPTO_Type*)(base))->TR_FIRO_CTL);
}
static inline uint8_t Cy_Crypto_Core_Trng_MonGetHealthStatus(CRYPTO_Type *base)
{
    return (uint8_t)(((((CRYPTO_V1_Type*)(base))->INTR) & (0x80000UL | 0x100000UL)) >> 19UL);
}
static inline void Cy_Crypto_Core_Trng_MonClearHealthStatus(CRYPTO_Type *base)
{
    Cy_Crypto_Core_ClearInterrupt(base, 0x80000UL | 0x100000UL);
}
static inline uint8_t Cy_Crypto_Core_Trng_MonGetRcRepCount(CRYPTO_Type *base)
{
    return ((uint8_t)(((uint32_t)((((CRYPTO_Type*)(base))->TR_MON_RC_STATUS1)) & 0xFFUL) >> 0UL));
}
static inline uint16_t Cy_Crypto_Core_Trng_MonGetApOccCount(CRYPTO_Type *base)
{
    return ((uint16_t)(((uint32_t)((((CRYPTO_Type*)(base))->TR_MON_AP_STATUS1)) & 0xFFFFUL) >> 0UL));
}
static inline uint16_t Cy_Crypto_Core_Trng_MonGetApWindowIndex(CRYPTO_Type *base)
{
    return ((uint16_t)(((uint32_t)((((CRYPTO_Type*)(base))->TR_MON_AP_STATUS1)) & 0xFFFF0000UL) >> 16UL));
}
static inline uint8_t Cy_Crypto_Core_Trng_MonGetRcCurrentBit(CRYPTO_Type *base)
{
    return ((uint8_t)(((uint32_t)((((CRYPTO_Type*)(base))->TR_MON_RC_STATUS0)) & 0x1UL) >> 0UL));
}
static inline uint8_t Cy_Crypto_Core_Trng_MonGetApCurrentBit(CRYPTO_Type *base)
{
    return ((uint8_t)(((uint32_t)((((CRYPTO_Type*)(base))->TR_MON_AP_STATUS0)) & 0x1UL) >> 0UL));
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Trng_MonSetBSSelector(CRYPTO_Type *base,
                                                                           cy_en_crypto_trng_bs_sel_t bitStreamSelector)
{
    cy_en_crypto_status_t status = CY_CRYPTO_SUCCESS;
    do { if(!((((bitStreamSelector) == CY_CRYPTO_TRMON_BS_DAS) || ((bitStreamSelector) == CY_CRYPTO_TRMON_BS_RED) || ((bitStreamSelector) == CY_CRYPTO_TRMON_BS_TR)))) { CY_HALT(); } } while (0);
    (((((CRYPTO_Type*)(base))->TR_MON_CTL)) = (((((((CRYPTO_Type*)(base))->TR_MON_CTL))) & ((uint32_t)(~(0x3UL)))) | ((((uint32_t)((bitStreamSelector)) << 0UL) & 0x3UL))));
    return status;
}
static inline cy_en_crypto_trng_bs_sel_t Cy_Crypto_Core_Trng_MonGetBSSelector(CRYPTO_Type *base)
{
    do{}while(0);
    return ((cy_en_crypto_trng_bs_sel_t)(((uint32_t)((((CRYPTO_Type*)(base))->TR_MON_CTL)) & 0x3UL) >> 0UL));
}
static inline void Cy_Crypto_Core_Trng_MonEnableApTest(CRYPTO_Type *base)
{
    (((((CRYPTO_Type*)(base))->TR_MON_CMD)) = (((((((CRYPTO_Type*)(base))->TR_MON_CMD))) & ((uint32_t)(~(0x1UL)))) | ((((uint32_t)((1U)) << 0UL) & 0x1UL))));
}
static inline void Cy_Crypto_Core_Trng_MonDisableApTest(CRYPTO_Type *base)
{
    (((((CRYPTO_Type*)(base))->TR_MON_CMD)) = (((((((CRYPTO_Type*)(base))->TR_MON_CMD))) & ((uint32_t)(~(0x1UL)))) | ((((uint32_t)((0U)) << 0UL) & 0x1UL))));
}
static inline void Cy_Crypto_Core_Trng_MonEnableRcTest(CRYPTO_Type *base)
{
    (((((CRYPTO_Type*)(base))->TR_MON_CMD)) = (((((((CRYPTO_Type*)(base))->TR_MON_CMD))) & ((uint32_t)(~(0x2UL)))) | ((((uint32_t)((1U)) << 1UL) & 0x2UL))));
}
static inline void Cy_Crypto_Core_Trng_MonDisableRcTest(CRYPTO_Type *base)
{
    (((((CRYPTO_Type*)(base))->TR_MON_CMD)) = (((((((CRYPTO_Type*)(base))->TR_MON_CMD))) & ((uint32_t)(~(0x2UL)))) | ((((uint32_t)((0U)) << 1UL) & 0x2UL))));
}
static inline void Cy_Crypto_Core_Trng_MonSetRcCC8(CRYPTO_Type *base, uint8_t ccCount)
{
    (((CRYPTO_Type*)(base))->TR_MON_RC_CTL) = (uint32_t)(((uint32_t)(ccCount) << 0UL) & 0xFFUL);
}
static inline uint8_t Cy_Crypto_Core_Trng_MonGetRcCC8(CRYPTO_Type *base)
{
    return ((uint8_t)(((uint32_t)((((CRYPTO_Type*)(base))->TR_MON_RC_CTL)) & 0xFFUL) >> 0UL));
}
static inline void Cy_Crypto_Core_Trng_MonSetApCC16(CRYPTO_Type *base, uint16_t ccCount)
{
    (((((CRYPTO_Type*)(base))->TR_MON_AP_CTL)) = (((((((CRYPTO_Type*)(base))->TR_MON_AP_CTL))) & ((uint32_t)(~(0xFFFFUL)))) | ((((uint32_t)((ccCount)) << 0UL) & 0xFFFFUL))));
}
static inline uint16_t Cy_Crypto_Core_Trng_MonGetApCC16(CRYPTO_Type *base)
{
    return ((uint16_t)(((uint32_t)((((CRYPTO_Type*)(base))->TR_MON_AP_CTL)) & 0xFFFFUL) >> 0UL));
}
static inline void Cy_Crypto_Core_Trng_MonSetApWinSize(CRYPTO_Type *base, uint16_t windowSize)
{
    (((((CRYPTO_Type*)(base))->TR_MON_AP_CTL)) = (((((((CRYPTO_Type*)(base))->TR_MON_AP_CTL))) & ((uint32_t)(~(0xFFFF0000UL)))) | ((((uint32_t)((windowSize)) << 16UL) & 0xFFFF0000UL))));
}
static inline uint16_t Cy_Crypto_Core_Trng_MonGetApWinSize(CRYPTO_Type *base)
{
    return ((uint16_t)(((uint32_t)((((CRYPTO_Type*)(base))->TR_MON_AP_CTL)) & 0xFFFF0000UL) >> 16UL));
}


static inline void CY_CRYPTO_VU_SAVE_REG (CRYPTO_Type *base, uint32_t rsrc, uint32_t *data);
static inline void CY_CRYPTO_VU_RESTORE_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t data);
static inline void CY_CRYPTO_VU_SET_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t data, uint32_t size);
static inline void CY_CRYPTO_VU_COND_MOV_REG_TO_STATUS (CRYPTO_Type *base, uint32_t cc, uint32_t rsrc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x04u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rsrc));
}
static inline void CY_CRYPTO_VU_MOV_REG_TO_STATUS (CRYPTO_Type *base, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_MOV_REG_TO_STATUS (base, (0x00u), rsrc);
}
static inline void CY_CRYPTO_VU_COND_MOV_STATUS_TO_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x05u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)));
}
static inline void CY_CRYPTO_VU_MOV_STATUS_TO_REG (CRYPTO_Type *base, uint32_t rdst)
{
    CY_CRYPTO_VU_COND_MOV_STATUS_TO_REG (base, (0x00u), rdst);
}
static inline void CY_CRYPTO_VU_COND_MOV_IMM_TO_STATUS (CRYPTO_Type *base, uint32_t cc, uint32_t imm4)
{
    if ((1U == 1u))
    {
        uint32_t tmpReg = (14u);
        uint32_t tmpData;
        CY_CRYPTO_VU_SAVE_REG(base, tmpReg, &tmpData);
        CY_CRYPTO_VU_SET_REG(base, tmpReg, imm4, 4u);
        CY_CRYPTO_VU_COND_MOV_REG_TO_STATUS(base, cc, tmpReg);
        do { ; } while (0uL != (((uint32_t)((((CRYPTO_V1_Type*)(base))->STATUS)) & 0x80UL) >> 7UL));
        CY_CRYPTO_VU_RESTORE_REG(base, tmpReg, tmpData);
    }
    else
    {
            Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x0Fu),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)imm4 << (0u)));
    }
}
static inline void CY_CRYPTO_VU_MOV_IMM_TO_STATUS (CRYPTO_Type *base, uint32_t imm4)
{
    CY_CRYPTO_VU_COND_MOV_IMM_TO_STATUS (base, (0x00u), imm4);
}
static inline void CY_CRYPTO_VU_SET_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t data, uint32_t size)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                            (uint32_t)(0x80u),
                           ((uint32_t)rdst << (26u)) |
                           ((uint32_t)data << (((1U == 1u)) ? (12u) : (13u))) |
                           (((uint32_t)size - 1u) << (0u)));
}
static inline void CY_CRYPTO_VU_COND_LD_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                            (uint32_t)(0x00u),
                           ((uint32_t)cc << (20u)) |
                           ((uint32_t)rdst << (12u)) |
                           ((uint32_t)rsrc << (0u)));
}
static inline void CY_CRYPTO_VU_LD_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_LD_REG(base, (0x00u), rdst, rsrc);
}
static inline void CY_CRYPTO_VU_COND_ST_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                            (uint32_t)(0x01u),
                           ((uint32_t)cc << (20u)) |
                           ((uint32_t)rdst << (12u)) |
                           ((uint32_t)rsrc << (0u)));
}
static inline void CY_CRYPTO_VU_ST_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_ST_REG (base, (0x00u), rdst, rsrc);
}
static inline void CY_CRYPTO_VU_COND_MOV_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x04u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc << (0u)));
}
static inline void CY_CRYPTO_VU_MOV_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_MOV_REG (base, (0x00u), rdst, rsrc);
}
static inline void CY_CRYPTO_VU_COND_SWAP_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x03u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_SWAP_REG (CRYPTO_Type *base, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_SWAP_REG (base, (0x00u), rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_ADD_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x06u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_ADD_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_ADD_REG (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_SUB_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x07u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_SUB_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_SUB_REG (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_OR_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x08u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_OR_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_OR_REG (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_AND_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x09u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_AND_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_AND_REG (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_XOR_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x0Au),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_XOR_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_XOR_REG (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_NOR_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x0Bu),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_NOR_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_NOR_REG (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_NAND_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x0Cu),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_NAND_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_NAND_REG (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_MIN_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x0Du),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_MIN_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_MIN_REG (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_MAX_REG (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x0Eu),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_MAX_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_MAX_REG (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_PUSH_REG (CRYPTO_Type *base, uint32_t cc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                    (uint32_t)(0x10u),
                                   ((uint32_t)cc << (20u)));
}
static inline void CY_CRYPTO_VU_PUSH_REG (CRYPTO_Type *base)
{
    CY_CRYPTO_VU_COND_PUSH_REG (base, (0x00u));
}
static inline void CY_CRYPTO_VU_COND_POP_REG (CRYPTO_Type *base, uint32_t cc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                    (uint32_t)(0x11u),
                                   ((uint32_t)cc << (20u)));
}
static inline void CY_CRYPTO_VU_POP_REG (CRYPTO_Type *base)
{
    CY_CRYPTO_VU_COND_POP_REG (base, (0x00u));
}
static inline cy_en_crypto_status_t CY_CRYPTO_VU_COND_ALLOC_MEM (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t size)
{
    if((uint32_t)(((((((CRYPTO_V1_Type*)(base))->RF_DATA[(15u)])) >> 16U) & 0x00003fffUL) * 4u) < (uint32_t)(((uint32_t)(size) + 7U) >> 3U) )
    {
        return CY_CRYPTO_MEMORY_ALLOC_FAIL;
    }
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
          (uint32_t)(0x12u),
         ((uint32_t)cc << (20u)) |
         ((uint32_t)rdst << (((1U == 1u)) ? (12u) : (16u))) |
        (((uint32_t)size - 1u) << (0u)));
    return CY_CRYPTO_SUCCESS;
}
static inline cy_en_crypto_status_t CY_CRYPTO_VU_ALLOC_MEM (CRYPTO_Type *base, uint32_t rdst, uint32_t size)
{
    return CY_CRYPTO_VU_COND_ALLOC_MEM (base, (0x00u), rdst, size);
}
static inline void CY_CRYPTO_VU_COND_FREE_MEM (CRYPTO_Type *base, uint32_t cc, uint32_t reg_mask)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x13u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)reg_mask));
}
static inline void CY_CRYPTO_VU_FREE_MEM (CRYPTO_Type *base, uint32_t reg_mask)
{
    CY_CRYPTO_VU_COND_FREE_MEM (base, (0x00u), reg_mask);
}
static inline void CY_CRYPTO_VU_COND_LSL (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    if (((1U == 1u)) && (0u == (((CRYPTO_V1_Type*)(base))->RF_DATA[(rsrc0)])))
    {
        CY_CRYPTO_VU_COND_XOR_REG(base, cc, rdst, rsrc1, rsrc0);
    }
    else
    {
        Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                        (uint32_t)(0x20u),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (12u)) |
                                        ((uint32_t)rsrc1 << (4u)) |
                                        ((uint32_t)rsrc0 << (0u)));
    }
}
static inline void CY_CRYPTO_VU_LSL (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_LSL (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_LSL1 (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1)
{
    if ((1U == 1u))
    {
        Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x21u),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (12u)) |
                                        ((uint32_t)rsrc1 << (4u)));
    }
    else
    {
        Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x21u),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (12u)) |
                                        ((uint32_t)rsrc1 << (4u)) |
                                        ((uint32_t)(15u) << (0u)));
    }
}
static inline void CY_CRYPTO_VU_LSL1 (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1)
{
    CY_CRYPTO_VU_COND_LSL1 (base, (0x00u), rdst, rsrc1);
}
static inline void CY_CRYPTO_VU_COND_LSL1_WITH_CARRY (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1)
{
    if ((1U == 1u))
    {
        Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x22u),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (12u)) |
                                        ((uint32_t)rsrc1 << (4u)));
    }
    else
    {
        Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x22u),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (12u)) |
                                        ((uint32_t)rsrc1 << (4u)) |
                                        ((uint32_t)(15u) << (0u)));
    }
}
static inline void CY_CRYPTO_VU_LSL1_WITH_CARRY (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1)
{
    CY_CRYPTO_VU_COND_LSL1_WITH_CARRY (base, (0x00u), rdst, rsrc1);
}
static inline void CY_CRYPTO_VU_COND_LSR (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    if (((1U == 1u)) && (0u == (((CRYPTO_V1_Type*)(base))->RF_DATA[(rsrc0)])))
    {
        CY_CRYPTO_VU_COND_XOR_REG(base, cc, rdst, rsrc1, rsrc0);
    }
    else
    {
         Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(((1U == 1u)) ? (0x24u) : (0x23u)),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
    }
}
static inline void CY_CRYPTO_VU_LSR (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_LSR (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_LSR1 (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1)
{
    if ((1U == 1u))
    {
        Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x25u),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (12u)) |
                                        ((uint32_t)rsrc1 << (4u)));
    }
    else
    {
        Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x24u),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (12u)) |
                                        ((uint32_t)rsrc1 << (4u)) |
                                        ((uint32_t)(15u) << (0u)));
    }
}
static inline void CY_CRYPTO_VU_LSR1 (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1)
{
    CY_CRYPTO_VU_COND_LSR1(base, (0x00u), rdst, rsrc1);
}
static inline void CY_CRYPTO_VU_COND_LSR1_WITH_CARRY (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1)
{
    if ((1U == 1u))
    {
        Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x26u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)));
    }
    else
    {
        Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x25u),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (12u)) |
                                        ((uint32_t)rsrc1 << (4u)) |
                                        ((uint32_t)(15u) << (0u)));
    }
}
static inline void CY_CRYPTO_VU_LSR1_WITH_CARRY (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1)
{
    CY_CRYPTO_VU_COND_LSR1_WITH_CARRY (base, (0x00u), rdst, rsrc1);
}
static inline void CY_CRYPTO_VU_COND_CLSAME (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(((1U == 1u)) ? (0x28u) : (0x26u)),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_CLSAME (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_CLSAME (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_CTSAME (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(((1U == 1u)) ? (0x29u) : (0x27u)),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_CTSAME (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_CTSAME (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_SET_BIT (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(((1U == 1u)) ? (0x2Cu) : (0x28u)),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc << (0u)));
 }
static inline void CY_CRYPTO_VU_SET_BIT (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_SET_BIT (base, (0x00u), rdst, rsrc);
}
static inline void CY_CRYPTO_VU_COND_CLR_BIT (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(((1U == 1u)) ? (0x2Du) : (0x29u)),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc << (0u)));
}
static inline void CY_CRYPTO_VU_CLR_BIT (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_CLR_BIT (base, (0x00u), rdst, rsrc);
}
static inline void CY_CRYPTO_VU_COND_INV_BIT (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(((1U == 1u)) ? (0x2Eu) : (0x2Au)),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc << (0u)));
}
static inline void CY_CRYPTO_VU_INV_BIT (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_INV_BIT (base, (0x00u), rdst, rsrc);
}
static inline void CY_CRYPTO_VU_COND_GET_BIT (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(((1U == 1u)) ? (0x2Fu) : (0x2Bu)),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_GET_BIT (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_GET_BIT (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_SET_BIT_IMM (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t imm13)
{
    if ((1U == 1u))
    {
        uint32_t tmpReg = (rdst != (14u)) ? (14u) : (13u);
        uint32_t tmpData;
        CY_CRYPTO_VU_SAVE_REG(base, tmpReg, &tmpData);
        CY_CRYPTO_VU_SET_REG(base, tmpReg, imm13, 13u);
        CY_CRYPTO_VU_COND_SET_BIT(base, cc, rdst, tmpReg);
        do { ; } while (0uL != (((uint32_t)((((CRYPTO_V1_Type*)(base))->STATUS)) & 0x80UL) >> 7UL));
        CY_CRYPTO_VU_RESTORE_REG(base, tmpReg, tmpData);
    }
    else
    {
            Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x2Cu),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (16u)) |
                                        ((uint32_t)imm13 << (0u)));
    }
}
static inline void CY_CRYPTO_VU_SET_BIT_IMM (CRYPTO_Type *base, uint32_t rdst, uint32_t imm13)
{
    CY_CRYPTO_VU_COND_SET_BIT_IMM(base, (0x00u), rdst, imm13);
}
static inline void CY_CRYPTO_VU_COND_CLR_BIT_IMM (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t imm13)
{
    if ((1U == 1u))
    {
        uint32_t tmpReg = (rdst != (14u)) ? (14u) : (13u);
        uint32_t tmpData;
        CY_CRYPTO_VU_SAVE_REG(base, tmpReg, &tmpData);
        CY_CRYPTO_VU_SET_REG(base, tmpReg, imm13, 13u);
        CY_CRYPTO_VU_COND_CLR_BIT(base, cc, rdst, tmpReg);
        do { ; } while (0uL != (((uint32_t)((((CRYPTO_V1_Type*)(base))->STATUS)) & 0x80UL) >> 7UL));
        CY_CRYPTO_VU_RESTORE_REG(base, tmpReg, tmpData);
    }
    else
    {
            Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x2Du),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (16u)) |
                                        ((uint32_t)imm13 << (0u)));
    }
}
static inline void CY_CRYPTO_VU_CLR_BIT_IMM (CRYPTO_Type *base, uint32_t rdst, uint32_t imm13)
{
    CY_CRYPTO_VU_COND_CLR_BIT_IMM(base, (0x00u), rdst, imm13);
}
static inline void CY_CRYPTO_VU_COND_INV_BIT_IMM (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t imm13)
{
    if ((1U == 1u))
    {
        uint32_t tmpReg = (rdst != (14u)) ? (14u) : (13u);
        uint32_t tmpData;
        CY_CRYPTO_VU_SAVE_REG(base, tmpReg, &tmpData);
        CY_CRYPTO_VU_SET_REG(base, tmpReg, imm13, 13u);
        CY_CRYPTO_VU_COND_INV_BIT(base, cc, rdst, tmpReg);
        do { ; } while (0uL != (((uint32_t)((((CRYPTO_V1_Type*)(base))->STATUS)) & 0x80UL) >> 7UL));
        CY_CRYPTO_VU_RESTORE_REG(base, tmpReg, tmpData);
    }
    else
    {
            Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                         (uint32_t)(0x2Eu),
                                        ((uint32_t)cc << (20u)) |
                                        ((uint32_t)rdst << (16u)) |
                                        ((uint32_t)imm13 << (0u)));
    }
}
static inline void CY_CRYPTO_VU_INV_BIT_IMM (CRYPTO_Type *base, uint32_t rdst, uint32_t imm13)
{
    CY_CRYPTO_VU_COND_INV_BIT_IMM(base, (0x00u), rdst, imm13);
}
static inline void CY_CRYPTO_VU_COND_TST (CRYPTO_Type *base, uint32_t cc, uint32_t rsrc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x3fu),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rsrc << (0u)));
}
static inline void CY_CRYPTO_VU_TST (CRYPTO_Type *base, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_TST (base, (0x00u), rsrc);
}
static inline void CY_CRYPTO_VU_COND_MOV (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x30u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc << (0u)));
}
static inline void CY_CRYPTO_VU_MOV (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_MOV (base, (0x00u), rdst, rsrc);
}
static inline void CY_CRYPTO_VU_COND_XSQUARE (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x31u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc << (0u)));
}
static inline void CY_CRYPTO_VU_XSQUARE (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_XSQUARE (base, (0x00u), rdst, rsrc);
}
static inline void CY_CRYPTO_VU_COND_XMUL (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x32u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_XMUL (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_XMUL (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_UMUL (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x33u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_UMUL (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_UMUL (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_USQUARE (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc)
{
    if ((1U == 1u))
    {
        CY_CRYPTO_VU_COND_UMUL(base, cc, rdst, rsrc, rsrc);
    }
    else
    {
            Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x2Fu),
                                        ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc << (0u)));
    }
}
static inline void CY_CRYPTO_VU_USQUARE (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc)
{
    CY_CRYPTO_VU_COND_USQUARE(base, (0x00u), rdst, rsrc);
}
static inline void CY_CRYPTO_VU_COND_SET_TO_ZERO (CRYPTO_Type *base, uint32_t cc, uint32_t rdst)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x34u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)));
}
static inline void CY_CRYPTO_VU_SET_TO_ZERO (CRYPTO_Type *base, uint32_t rdst)
{
    CY_CRYPTO_VU_COND_SET_TO_ZERO (base, (0x00u), rdst);
}
static inline void CY_CRYPTO_VU_COND_SET_TO_ONE (CRYPTO_Type *base, uint32_t cc, uint32_t rdst)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x35u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)));
}
static inline void CY_CRYPTO_VU_SET_TO_ONE (CRYPTO_Type *base, uint32_t rdst)
{
    CY_CRYPTO_VU_COND_SET_TO_ONE (base, (0x00u), rdst);
}
static inline void CY_CRYPTO_VU_COND_ADD (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x36u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_ADD (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_ADD (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_SUB (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0), (uint32_t)(0x37u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_SUB (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_SUB (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_OR (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x38u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_OR (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_OR (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_AND (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x39u),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_AND (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_AND (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_XOR (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0), (uint32_t)(0x3Au),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_XOR (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_XOR (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_NOR (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x3Bu),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_NOR (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_NOR (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_NAND (CRYPTO_Type *base, uint32_t cc, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x3Cu),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rdst << (12u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_NAND (CRYPTO_Type *base, uint32_t rdst, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_NAND (base, (0x00u), rdst, rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_CMP_SUB (CRYPTO_Type *base, uint32_t cc, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x3Du),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_CMP_SUB (CRYPTO_Type *base, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_CMP_SUB (base, (0x00u), rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_COND_CMP_DEGREE (CRYPTO_Type *base, uint32_t cc, uint32_t rsrc1, uint32_t rsrc0)
{
    Cy_Crypto_Core_Vu_RunInstr(base, (0),
                                     (uint32_t)(0x3Eu),
                                    ((uint32_t)cc << (20u)) |
                                    ((uint32_t)rsrc1 << (4u)) |
                                    ((uint32_t)rsrc0 << (0u)));
}
static inline void CY_CRYPTO_VU_CMP_DEGREE (CRYPTO_Type *base, uint32_t rsrc1, uint32_t rsrc0)
{
    CY_CRYPTO_VU_COND_CMP_DEGREE (base, (0x00u), rsrc1, rsrc0);
}
static inline void CY_CRYPTO_VU_SAVE_REG (CRYPTO_Type *base, uint32_t rsrc, uint32_t *data)
{
    *data = (((CRYPTO_V1_Type*)(base))->RF_DATA[(rsrc)]);
}
static inline void CY_CRYPTO_VU_RESTORE_REG (CRYPTO_Type *base, uint32_t rdst, uint32_t data)
{
    CY_CRYPTO_VU_SET_REG(base, rdst, (((data) >> 16U) & 0x00003fffUL), ((data) & 0x00000fffUL) + 1u);
}

typedef unsigned int wint_t;
typedef long __blkcnt_t;
typedef long __blksize_t;
typedef __uint64_t __fsblkcnt_t;
typedef __uint32_t __fsfilcnt_t;
typedef long _off_t;
typedef int __pid_t;
typedef short __dev_t;
typedef unsigned short __uid_t;
typedef unsigned short __gid_t;
typedef __uint32_t __id_t;
typedef unsigned short __ino_t;
typedef __uint32_t __mode_t;
__extension__ typedef long long _off64_t;
typedef _off_t __off_t;
typedef _off64_t __loff_t;
typedef long __key_t;
typedef long _fpos_t;
typedef unsigned int __size_t;
typedef signed int _ssize_t;
typedef _ssize_t __ssize_t;
typedef struct
{
  int __count;
  union
  {
    wint_t __wch;
    unsigned char __wchb[4];
  } __value;
} _mbstate_t;
typedef void *_iconv_t;
typedef unsigned long __clock_t;
typedef __int_least64_t __time_t;
typedef unsigned long __clockid_t;
typedef long __daddr_t;
typedef unsigned long __timer_t;
typedef __uint8_t __sa_family_t;
typedef __uint32_t __socklen_t;
typedef int __nl_item;
typedef unsigned short __nlink_t;
typedef long __suseconds_t;
typedef unsigned long __useconds_t;
typedef __builtin_va_list __va_list;
typedef unsigned long __ULong;
struct __lock;
typedef struct __lock * _LOCK_T;
extern void __retarget_lock_init(_LOCK_T *lock);
extern void __retarget_lock_init_recursive(_LOCK_T *lock);
extern void __retarget_lock_close(_LOCK_T lock);
extern void __retarget_lock_close_recursive(_LOCK_T lock);
extern void __retarget_lock_acquire(_LOCK_T lock);
extern void __retarget_lock_acquire_recursive(_LOCK_T lock);
extern int __retarget_lock_try_acquire(_LOCK_T lock);
extern int __retarget_lock_try_acquire_recursive(_LOCK_T lock);
extern void __retarget_lock_release(_LOCK_T lock);
extern void __retarget_lock_release_recursive(_LOCK_T lock);
typedef _LOCK_T _flock_t;
struct _reent;
struct __locale_t;
struct _Bigint
{
  struct _Bigint *_next;
  int _k, _maxwds, _sign, _wds;
  __ULong _x[1];
};
struct __tm
{
  int __tm_sec;
  int __tm_min;
  int __tm_hour;
  int __tm_mday;
  int __tm_mon;
  int __tm_year;
  int __tm_wday;
  int __tm_yday;
  int __tm_isdst;
};
struct _on_exit_args {
 void * _fnargs[32];
 void * _dso_handle[32];
 __ULong _fntypes;
 __ULong _is_cxa;
};
struct _atexit {
 struct _atexit *_next;
 int _ind;
 void (*_fns[32])(void);
        struct _on_exit_args _on_exit_args;
};
struct __sbuf {
 unsigned char *_base;
 int _size;
};
struct __sFILE {
  unsigned char *_p;
  int _r;
  int _w;
  short _flags;
  short _file;
  struct __sbuf _bf;
  int _lbfsize;
  void * _cookie;
  int (*_read) (struct _reent *, void *,
        char *, int);
  int (*_write) (struct _reent *, void *,
         const char *,
         int);
  _fpos_t (*_seek) (struct _reent *, void *, _fpos_t, int);
  int (*_close) (struct _reent *, void *);
  struct __sbuf _ub;
  unsigned char *_up;
  int _ur;
  unsigned char _ubuf[3];
  unsigned char _nbuf[1];
  struct __sbuf _lb;
  int _blksize;
  _off_t _offset;
  struct _reent *_data;
  _flock_t _lock;
  _mbstate_t _mbstate;
  int _flags2;
};
typedef struct __sFILE __FILE;
extern __FILE __sf[3];
struct _glue
{
  struct _glue *_next;
  int _niobs;
  __FILE *_iobs;
};
extern struct _glue __sglue;
struct _rand48 {
  unsigned short _seed[3];
  unsigned short _mult[3];
  unsigned short _add;
};
struct _reent
{
  int _errno;
  __FILE *_stdin, *_stdout, *_stderr;
  int _inc;
  char _emergency[25];
  struct __locale_t *_locale;
  void (*__cleanup) (struct _reent *);
  struct _Bigint *_result;
  int _result_k;
  struct _Bigint *_p5s;
  struct _Bigint **_freelist;
  int _cvtlen;
  char *_cvtbuf;
  union
    {
      struct
        {
          char * _strtok_last;
          char _asctime_buf[26];
          struct __tm _localtime_buf;
          int _gamma_signgam;
          __extension__ unsigned long long _rand_next;
          struct _rand48 _r48;
          _mbstate_t _mblen_state;
          _mbstate_t _mbtowc_state;
          _mbstate_t _wctomb_state;
          char _l64a_buf[8];
          char _signal_buf[24];
          int _getdate_err;
          _mbstate_t _mbrlen_state;
          _mbstate_t _mbrtowc_state;
          _mbstate_t _mbsrtowcs_state;
          _mbstate_t _wcrtomb_state;
          _mbstate_t _wcsrtombs_state;
   int _h_errno;
   char _getlocalename_l_buf[32 ];
        } _reent;
    } _new;
  void (**_sig_func)(int);
};
extern struct _reent *_impure_ptr ;
extern struct _reent _impure_data ;
extern struct _atexit *__atexit;
extern struct _atexit __atexit0;
extern void (*__stdio_exit_handler) (void);
void _reclaim_reent (struct _reent *);
extern int _fwalk_sglue (struct _reent *, int (*)(struct _reent *, __FILE *),
    struct _glue *);
struct __locale_t;
typedef struct __locale_t *locale_t;

int bcmp(const void *, const void *, size_t) __attribute__((__pure__));
void bcopy(const void *, void *, size_t);
void bzero(void *, size_t);
void explicit_bzero(void *, size_t);
int ffs(int) __attribute__((__const__));
int ffsl(long) __attribute__((__const__));
int ffsll(long long) __attribute__((__const__));
int fls(int) __attribute__((__const__));
int flsl(long) __attribute__((__const__));
int flsll(long long) __attribute__((__const__));
char *index(const char *, int) __attribute__((__pure__));
char *rindex(const char *, int) __attribute__((__pure__));
int strcasecmp(const char *, const char *) __attribute__((__pure__));
int strncasecmp(const char *, const char *, size_t) __attribute__((__pure__));
int strcasecmp_l (const char *, const char *, locale_t);
int strncasecmp_l (const char *, const char *, size_t, locale_t);


void * memchr (const void *, int, size_t);
int memcmp (const void *, const void *, size_t);
void * memcpy (void *restrict, const void *restrict, size_t);
void * memmove (void *, const void *, size_t);
void * memset (void *, int, size_t);
char *strcat (char *restrict, const char *restrict);
char *strchr (const char *, int);
int strcmp (const char *, const char *);
int strcoll (const char *, const char *);
char *strcpy (char *restrict, const char *restrict);
size_t strcspn (const char *, const char *);
char *strerror (int);
size_t strlen (const char *);
char *strncat (char *restrict, const char *restrict, size_t);
int strncmp (const char *, const char *, size_t);
char *strncpy (char *restrict, const char *restrict, size_t);
char *strpbrk (const char *, const char *);
char *strrchr (const char *, int);
size_t strspn (const char *, const char *);
char *strstr (const char *, const char *);
char *strtok (char *restrict, const char *restrict);
size_t strxfrm (char *restrict, const char *restrict, size_t);
int strcoll_l (const char *, const char *, locale_t);
char *strerror_l (int, locale_t);
size_t strxfrm_l (char *restrict, const char *restrict, size_t, locale_t);
char *strtok_r (char *restrict, const char *restrict, char **restrict);
int timingsafe_bcmp (const void *, const void *, size_t);
int timingsafe_memcmp (const void *, const void *, size_t);
void * memccpy (void *restrict, const void *restrict, int, size_t);
char *stpcpy (char *restrict, const char *restrict);
char *stpncpy (char *restrict, const char *restrict, size_t);
char *strdup (const char *) __attribute__((__malloc__)) __attribute__((__warn_unused_result__));
char *_strdup_r (struct _reent *, const char *);
char *strndup (const char *, size_t) __attribute__((__malloc__)) __attribute__((__warn_unused_result__));
char *_strndup_r (struct _reent *, const char *, size_t);
int strerror_r (int, char *, size_t)
             __asm__ ("" "__xpg_strerror_r")
  ;
char * _strerror_r (struct _reent *, int, int, int *);
size_t strlcat (char *, const char *, size_t);
size_t strlcpy (char *, const char *, size_t);
size_t strnlen (const char *, size_t);
char *strsep (char **, const char *);
char *strnstr(const char *, const char *, size_t) __attribute__((__pure__));
char *strlwr (char *);
char *strupr (char *);
char *strsignal (int __signo);

void Cy_Crypto_Core_Vu_SetMemValue(CRYPTO_Type *base, uint32_t dstReg, uint8_t const *src, uint32_t size);
void Cy_Crypto_Core_Vu_GetMemValue(CRYPTO_Type *base, uint8_t *dst, uint32_t srcReg, uint32_t size);
_Bool Cy_Crypto_Core_Vu_IsRegZero(CRYPTO_Type *base, uint32_t srcReg);
_Bool Cy_Crypto_Core_Vu_IsRegEqual(CRYPTO_Type *base, uint32_t srcReg0, uint32_t srcReg1);
_Bool Cy_Crypto_Core_Vu_IsRegLess(CRYPTO_Type *base, uint32_t srcReg0, uint32_t srcReg1);
static inline uint32_t Cy_Crypto_Core_Vu_RegRead(CRYPTO_Type *base, uint32_t srcReg)
{
    return ((uint32_t)(((uint32_t)((((CRYPTO_V1_Type*)(base))->RF_DATA[(srcReg)])) & 0xFFFFFFFFUL) >> 0UL));
}
static inline uint16_t Cy_Crypto_Core_Vu_RegSizeRead(CRYPTO_Type *base, uint32_t srcReg)
{
    return ((uint16_t)((((uint32_t)((((CRYPTO_V1_Type*)(base))->RF_DATA[(srcReg)])) & 0xFFFFFFFFUL) >> 0UL) & (0x00001fffuL)));
}
static inline uint16_t Cy_Crypto_Core_Vu_RegBitSizeRead(CRYPTO_Type *base, uint32_t srcReg)
{
    return ((uint16_t)((((uint32_t)((((CRYPTO_V1_Type*)(base))->RF_DATA[(srcReg)])) & 0xFFFFFFFFUL) >> 0UL) & (0x00001fffuL)) + 1u);
}
static inline uint16_t Cy_Crypto_Core_Vu_RegByteSizeRead(CRYPTO_Type *base, uint32_t srcReg)
{
    return ((uint16_t)(((((uint32_t)((((CRYPTO_V1_Type*)(base))->RF_DATA[(srcReg)])) & 0xFFFFFFFFUL) >> 0UL) & (0x00001fffuL)) + 1u) >> 3u);
}
static inline uint16_t Cy_Crypto_Core_Vu_RegWordSizeRead(CRYPTO_Type *base, uint32_t srcReg)
{
    return ((uint16_t)(((((uint32_t)((((CRYPTO_V1_Type*)(base))->RF_DATA[(srcReg)])) & 0xFFFFFFFFUL) >> 0UL) & (0x00001fffuL)) + 1u) >> 5u);
}
static inline uint16_t Cy_Crypto_Core_Vu_RegDataPtrRead(CRYPTO_Type *base, uint32_t srcReg)
{
    return (uint16_t)(((((uint32_t)((((CRYPTO_V1_Type*)(base))->RF_DATA[(srcReg)])) & 0xFFFFFFFFUL) >> 0UL) >> (16u))
                                & (0x00003fffuL));
}
static inline uint32_t * Cy_Crypto_Core_Vu_RegMemPointer(CRYPTO_Type *base, uint32_t srcReg)
{
    return (uint32_t *)((uint32_t)(((CRYPTO_V1_Type*)(base))->VU_CTL1) + (4u * (uint32_t)Cy_Crypto_Core_Vu_RegDataPtrRead(base, srcReg)));
}
static inline uint32_t Cy_Crypto_Core_Vu_StatusRead(CRYPTO_Type *base)
{
    Cy_Crypto_Core_Vu_WaitForComplete(base);
    return((uint32_t)(((CRYPTO_V1_Type*)(base))->VU_STATUS));
}
void Cy_Crypto_Core_VU_RegInvertEndianness(CRYPTO_Type *base, uint32_t srcReg);
static inline cy_en_crypto_status_t Cy_Crypto_Core_Hkdf_Extract(CRYPTO_Type *base, cy_en_crypto_sha_mode_t mode,
                                          uint8_t const *salt,
                                          uint32_t saltLength,
                                          uint8_t const *ikm,
                                          uint32_t ikmLength,
                                          uint8_t *prk)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
        (void)base;
        (void)mode;
        (void)salt;
        (void)saltLength;
        (void)ikm;
        (void)ikmLength;
        (void)prk;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Hkdf_Expand(CRYPTO_Type *base, cy_en_crypto_sha_mode_t mode,
                                          uint8_t const *prk,
                                          uint32_t prkLength,
                                          uint8_t const *info,
                                          uint32_t infoLength,
                                          uint8_t *okm,
                                          uint32_t okmLength)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
        (void)base;
        (void)mode;
        (void)prk;
        (void)prkLength;
        (void)info;
        (void)infoLength;
        (void)okm;
        (void)okmLength;
    }
    else
    {
    }
    return tmpResult;
}
static inline cy_en_crypto_status_t Cy_Crypto_Core_Hkdf(CRYPTO_Type *base, cy_en_crypto_sha_mode_t mode,
                                          uint8_t const *salt,
                                          uint32_t saltLength,
                                          uint8_t const *ikm,
                                          uint32_t ikmLength,
                                          uint8_t const *info,
                                          uint32_t infoLength,
                                          uint8_t *okm,
                                          uint32_t okmLength)
{
    cy_en_crypto_status_t tmpResult = CY_CRYPTO_NOT_SUPPORTED;
    if ((1U == 1u))
    {
        tmpResult = CY_CRYPTO_NOT_SUPPORTED;
        (void)base;
        (void)mode;
        (void)salt;
        (void)saltLength;
        (void)ikm;
        (void)ikmLength;
        (void)info;
        (void)infoLength;
        (void)okm;
        (void)okmLength;
    }
    else
    {
    }
    return tmpResult;
}
cy_en_crypto_status_t Cy_Crypto_Server_Start(cy_stc_crypto_config_t const *config,
                                             cy_stc_crypto_server_context_t *context);
cy_en_crypto_status_t Cy_Crypto_Server_Stop(void);
void Cy_Crypto_Server_Process(void);
void Cy_Crypto_Server_GetDataHandler(void);
void Cy_Crypto_Server_ErrorHandler(void);
typedef enum
{
    CY_CSD_SUCCESS = 0x00U,
    CY_CSD_BAD_PARAM = (((uint32_t)((uint32_t)((0x41U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01U,
    CY_CSD_BUSY = (((uint32_t)((uint32_t)((0x41U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02U,
    CY_CSD_LOCKED = (((uint32_t)((uint32_t)((0x41U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x03U
} cy_en_csd_status_t;
typedef enum
{
    CY_CSD_NONE_KEY = 0U,
    CY_CSD_USER_DEFINED_KEY = 1U,
    CY_CSD_CAPSENSE_KEY = 2U,
    CY_CSD_ADC_KEY = 3U,
    CY_CSD_IDAC_KEY = 4U,
    CY_CSD_CMP_KEY = 5U
}cy_en_csd_key_t;
typedef struct
{
    uint32_t config;
    uint32_t spare;
    uint32_t status;
    uint32_t statSeq;
    uint32_t statCnts;
    uint32_t statHcnt;
    uint32_t resultVal1;
    uint32_t resultVal2;
    uint32_t adcRes;
    uint32_t intr;
    uint32_t intrSet;
    uint32_t intrMask;
    uint32_t intrMasked;
    uint32_t hscmp;
    uint32_t ambuf;
    uint32_t refgen;
    uint32_t csdCmp;
    uint32_t swRes;
    uint32_t sensePeriod;
    uint32_t senseDuty;
    uint32_t swHsPosSel;
    uint32_t swHsNegSel;
    uint32_t swShieldSel;
    uint32_t swAmuxbufSel;
    uint32_t swBypSel;
    uint32_t swCmpPosSel;
    uint32_t swCmpNegSel;
    uint32_t swRefgenSel;
    uint32_t swFwModSel;
    uint32_t swFwTankSel;
    uint32_t swDsiSel;
    uint32_t ioSel;
    uint32_t seqTime;
    uint32_t seqInitCnt;
    uint32_t seqNormCnt;
    uint32_t adcCtl;
    uint32_t seqStart;
    uint32_t idacA;
    uint32_t idacB;
} cy_stc_csd_config_t;
typedef struct
{
    cy_en_csd_key_t lockKey;
} cy_stc_csd_context_t;
cy_en_csd_status_t Cy_CSD_Init(CSD_Type * base, cy_stc_csd_config_t const * config, cy_en_csd_key_t key, cy_stc_csd_context_t * context);
cy_en_csd_status_t Cy_CSD_DeInit(const CSD_Type * base, cy_en_csd_key_t key, cy_stc_csd_context_t * context);
cy_en_csd_status_t Cy_CSD_Capture(CSD_Type * base, cy_en_csd_key_t key, cy_stc_csd_context_t * context);
cy_en_csd_status_t Cy_CSD_Configure(CSD_Type * base, const cy_stc_csd_config_t * config, cy_en_csd_key_t key, const cy_stc_csd_context_t * context);
static inline cy_en_csd_key_t Cy_CSD_GetLockStatus(const CSD_Type * base, const cy_stc_csd_context_t * context);
static inline cy_en_csd_status_t Cy_CSD_GetConversionStatus(const CSD_Type * base, const cy_stc_csd_context_t * context);
uint32_t Cy_CSD_GetVrefTrim(uint32_t referenceVoltage);
static inline uint32_t Cy_CSD_ReadReg(const CSD_Type * base, uint32_t offset);
static inline void Cy_CSD_WriteReg(CSD_Type * base, uint32_t offset, uint32_t value);
static inline void Cy_CSD_SetBits(CSD_Type * base, uint32_t offset, uint32_t mask);
static inline void Cy_CSD_ClrBits(CSD_Type * base, uint32_t offset, uint32_t mask);
static inline void Cy_CSD_WriteBits(CSD_Type* base, uint32_t offset, uint32_t mask, uint32_t value);
static inline uint32_t Cy_CSD_ReadReg(const CSD_Type * base, uint32_t offset)
{
    return(* (volatile uint32_t *)((uint32_t)base + offset));
}
static inline void Cy_CSD_WriteReg(CSD_Type * base, uint32_t offset, uint32_t value)
{
    (* (volatile uint32_t *)((uint32_t)base + offset)) = value;
}
static inline void Cy_CSD_SetBits(CSD_Type * base, uint32_t offset, uint32_t mask)
{
    volatile uint32_t * regPtr = (volatile uint32_t *)((uint32_t)base + offset);
    (* regPtr) |= mask;
}
static inline void Cy_CSD_ClrBits(CSD_Type * base, uint32_t offset, uint32_t mask)
{
    volatile uint32_t * regPtr = (volatile uint32_t *)((uint32_t)base + offset);
    (* regPtr) &= ~mask;
}
static inline void Cy_CSD_WriteBits(CSD_Type * base, uint32_t offset, uint32_t mask, uint32_t value)
{
    volatile uint32_t * regPtr = (volatile uint32_t *)((uint32_t)base + offset);
    (* regPtr) = ((* regPtr) & ~mask) | (value & mask);
}
static inline cy_en_csd_key_t Cy_CSD_GetLockStatus(const CSD_Type * base, const cy_stc_csd_context_t * context)
{
    (void)base;
    return(context->lockKey);
}
static inline cy_en_csd_status_t Cy_CSD_GetConversionStatus(const CSD_Type * base, const cy_stc_csd_context_t * context)
{
    cy_en_csd_status_t csdStatus = CY_CSD_BUSY;
    (void)context;
    if (((base->SEQ_START & 0x1UL) == 0u) &&
        ((base->STAT_SEQ & (0x7UL | 0x70000UL)) == 0u))
    {
        csdStatus = CY_CSD_SUCCESS;
    }
    return(csdStatus);
}
typedef enum
{
    CY_SYSPM_SUCCESS = 0x0U,
    CY_SYSPM_BAD_PARAM = (((uint32_t)((uint32_t)((0x10U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01U,
    CY_SYSPM_TIMEOUT = (((uint32_t)((uint32_t)((0x10U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02U,
    CY_SYSPM_INVALID_STATE = (((uint32_t)((uint32_t)((0x10U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x03U,
    CY_SYSPM_CANCELED = (((uint32_t)((uint32_t)((0x10U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x04U,
    CY_SYSPM_SYSCALL_PENDING = (((uint32_t)((uint32_t)((0x10U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x05U,
    CY_SYSPM_FAIL = (((uint32_t)((uint32_t)((0x10U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0xFFU
} cy_en_syspm_status_t;
typedef enum
{
    CY_SYSPM_WAIT_FOR_INTERRUPT,
    CY_SYSPM_WAIT_FOR_EVENT
} cy_en_syspm_waitfor_t;
typedef enum
{
    CY_SYSPM_HIBERNATE_LPCOMP0_LOW = ((((uint32_t)((4UL)) << 24UL) & 0xF000000UL)),
    CY_SYSPM_HIBERNATE_LPCOMP0_HIGH = ((((uint32_t)((4UL)) << 24UL) & 0xF000000UL)) | ((((uint32_t)((4UL)) << 20UL) & 0xF00000UL)),
    CY_SYSPM_HIBERNATE_LPCOMP1_LOW = ((((uint32_t)((8UL)) << 24UL) & 0xF000000UL)),
    CY_SYSPM_HIBERNATE_LPCOMP1_HIGH = ((((uint32_t)((8UL)) << 24UL) & 0xF000000UL)) | ((((uint32_t)((8UL)) << 20UL) & 0xF00000UL)),
    CY_SYSPM_HIBERNATE_RTC_ALARM = 0x40000UL,
    CY_SYSPM_HIBERNATE_WDT = 0x80000UL,
    CY_SYSPM_HIBERNATE_PIN0_LOW = ((((uint32_t)((1UL)) << 24UL) & 0xF000000UL)),
    CY_SYSPM_HIBERNATE_PIN0_HIGH = ((((uint32_t)((1UL)) << 24UL) & 0xF000000UL)) | ((((uint32_t)((1UL)) << 20UL) & 0xF00000UL)),
    CY_SYSPM_HIBERNATE_PIN1_LOW = ((((uint32_t)((2UL)) << 24UL) & 0xF000000UL)),
    CY_SYSPM_HIBERNATE_PIN1_HIGH = ((((uint32_t)((2UL)) << 24UL) & 0xF000000UL)) | ((((uint32_t)((2UL)) << 20UL) & 0xF00000UL))
} cy_en_syspm_hibernate_wakeup_source_t;
typedef enum
{
    CY_SYSPM_LDO_VOLTAGE_ULP = 0U,
    CY_SYSPM_LDO_VOLTAGE_LP = 1U,
    CY_SYSPM_LDO_VOLTAGE_0_9V = 0U,
    CY_SYSPM_LDO_VOLTAGE_1_1V = 1U
} cy_en_syspm_ldo_voltage_t;
typedef enum
{
    CY_SYSPM_LDO_MODE_DISABLED = 0U,
    CY_SYSPM_LDO_MODE_NORMAL = 1U,
    CY_SYSPM_LDO_MODE_MIN = 2U
} cy_en_syspm_ldo_mode_t;
typedef enum
{
    CY_SYSPM_BUCK_OUT1_VOLTAGE_ULP = 0x02U,
    CY_SYSPM_BUCK_OUT1_VOLTAGE_LP = 0x05U,
    CY_SYSPM_BUCK_OUT1_VOLTAGE_0_9V = 0x02U,
    CY_SYSPM_BUCK_OUT1_VOLTAGE_1_1V = 0x05U
} cy_en_syspm_buck_voltage1_t;
typedef enum
{
    CY_SYSPM_BUCK_VBUCK_1 = 0x0U,
    CY_SYSPM_BUCK_VRF
} cy_en_syspm_buck_out_t;
typedef enum
{
    CY_SYSPM_BUCK_OUT2_VOLTAGE_1_15V = 0U,
    CY_SYSPM_BUCK_OUT2_VOLTAGE_1_2V = 1U,
    CY_SYSPM_BUCK_OUT2_VOLTAGE_1_25V = 2U,
    CY_SYSPM_BUCK_OUT2_VOLTAGE_1_3V = 3U,
    CY_SYSPM_BUCK_OUT2_VOLTAGE_1_35V = 4U,
    CY_SYSPM_BUCK_OUT2_VOLTAGE_1_4V = 5U,
    CY_SYSPM_BUCK_OUT2_VOLTAGE_1_45V = 6U,
    CY_SYSPM_BUCK_OUT2_VOLTAGE_1_5V = 7U
} cy_en_syspm_buck_voltage2_t;
typedef enum
{
    CY_SYSPM_PMIC_POLARITY_LOW = 0U,
    CY_SYSPM_PMIC_POLARITY_HIGH = 1U
} cy_en_syspm_pmic_wakeup_polarity_t;
typedef enum
{
    CY_SYSPM_VDDBACKUP_DEFAULT = 0U,
    CY_SYSPM_VDDBACKUP_VBACKUP = 2U
} cy_en_syspm_vddbackup_control_t;
typedef enum
{
    CY_SYSPM_SC_CHARGE_ENABLE = 0x3CU,
    CY_SYSPM_SC_CHARGE_DISABLE = 0x00U
} cy_en_syspm_sc_charge_key_t;
typedef enum
{
    CY_SYSPM_FLASH_VOLTAGE_BIT_LP = 0U,
    CY_SYSPM_FLASH_VOLTAGE_BIT_ULP = 1U,
} cy_en_syspm_flash_voltage_bit_t;
typedef enum
{
    CY_SYSPM_SLEEP = 0U,
    CY_SYSPM_DEEPSLEEP = 1U,
    CY_SYSPM_HIBERNATE = 2U,
    CY_SYSPM_LP = 3U,
    CY_SYSPM_ULP = 4U,
} cy_en_syspm_callback_type_t;
typedef enum
{
    CY_SYSPM_SRAM0_MACRO_0 = 0U,
    CY_SYSPM_SRAM0_MACRO_1 = 1U,
    CY_SYSPM_SRAM0_MACRO_2 = 2U,
    CY_SYSPM_SRAM0_MACRO_3 = 3U,
} cy_en_syspm_sram0_macro_t;
typedef enum
{
    CY_SYSPM_CHECK_READY = 0x01U,
    CY_SYSPM_CHECK_FAIL = 0x02U,
    CY_SYSPM_BEFORE_TRANSITION = 0x04U,
    CY_SYSPM_AFTER_TRANSITION = 0x08U,
} cy_en_syspm_callback_mode_t;
typedef enum
{
    CY_SYSPM_SRAM0_MEMORY = 0U,
    CY_SYSPM_SRAM1_MEMORY = 1U,
    CY_SYSPM_SRAM2_MEMORY = 2U,
} cy_en_syspm_sram_index_t;
typedef enum
{
    CY_SYSPM_SRAM_PWR_MODE_OFF = 0U,
    CY_SYSPM_SRAM_PWR_MODE_INVALID = 1U,
    CY_SYSPM_SRAM_PWR_MODE_RET = 2U,
    CY_SYSPM_SRAM_PWR_MODE_ON = 3U
} cy_en_syspm_sram_pwr_mode_t;
typedef struct
{
    void *base;
    void *context;
} cy_stc_syspm_callback_params_t;
typedef cy_en_syspm_status_t (*Cy_SysPmCallback) (cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
typedef struct cy_stc_syspm_callback
{
    Cy_SysPmCallback callback;
    cy_en_syspm_callback_type_t type;
    uint32_t skipMode;
    cy_stc_syspm_callback_params_t *callbackParams;
    struct cy_stc_syspm_callback *prevItm;
    struct cy_stc_syspm_callback *nextItm;
    uint8_t order;
} cy_stc_syspm_callback_t;
typedef struct
{
    uint32_t CY_SYSPM_UDB_UDBIF_BANK_CTL_REG;
    uint32_t CY_SYSPM_UDB_BCTL_MDCLK_EN_REG;
    uint32_t CY_SYSPM_UDB_BCTL_MBCLK_EN_REG;
    uint32_t CY_SYSPM_UDB_BCTL_BOTSEL_L_REG;
    uint32_t CY_SYSPM_UDB_BCTL_BOTSEL_U_REG;
    uint32_t CY_SYSPM_UDB_BCTL_QCLK_EN0_REG;
    uint32_t CY_SYSPM_UDB_BCTL_QCLK_EN1_REG;
    uint32_t CY_SYSPM_UDB_BCTL_QCLK_EN2_REG;
    uint32_t CY_SYSPM_CM0_CLOCK_CTL_REG;
    uint32_t CY_SYSPM_CM4_CLOCK_CTL_REG;
} cy_stc_syspm_backup_regs_t;
cy_en_syspm_status_t Cy_SysPm_SetSRAMMacroPwrMode(cy_en_syspm_sram_index_t sramNum, uint32_t sramMacroNum, cy_en_syspm_sram_pwr_mode_t sramPwrMode);
cy_en_syspm_sram_pwr_mode_t Cy_SysPm_GetSRAMMacroPwrMode(cy_en_syspm_sram_index_t sramNum, uint32_t sramMacroNum);
cy_en_syspm_status_t Cy_SysPm_SetSRAMPwrMode(cy_en_syspm_sram_index_t sramNum, cy_en_syspm_sram_pwr_mode_t sramPwrMode);
cy_en_syspm_status_t Cy_SysPm_WriteVoltageBitForFlash(cy_en_syspm_flash_voltage_bit_t value);
void Cy_SysPm_SaveRegisters(cy_stc_syspm_backup_regs_t *regs);
void Cy_SysPm_RestoreRegisters(cy_stc_syspm_backup_regs_t const *regs);
uint32_t Cy_SysPm_ReadStatus(void);
cy_en_syspm_status_t Cy_SysPm_CpuEnterSleep(cy_en_syspm_waitfor_t waitFor);
cy_en_syspm_status_t Cy_SysPm_CpuEnterDeepSleep(cy_en_syspm_waitfor_t waitFor);
cy_en_syspm_status_t Cy_SysPm_SystemEnterLp(void);
cy_en_syspm_status_t Cy_SysPm_SystemEnterUlp(void);
cy_en_syspm_status_t Cy_SysPm_SystemEnterHibernate(void);
void Cy_SysPm_SetHibernateWakeupSource(uint32_t wakeupSource);
void Cy_SysPm_ClearHibernateWakeupSource(uint32_t wakeupSource);
cy_en_syspm_status_t Cy_SysPm_SystemSetMinRegulatorCurrent(void);
cy_en_syspm_status_t Cy_SysPm_SystemSetNormalRegulatorCurrent(void);
void Cy_SysPm_CpuSleepOnExit(_Bool enable);
cy_en_syspm_status_t Cy_SysPm_LdoSetVoltage(cy_en_syspm_ldo_voltage_t voltage);
cy_en_syspm_status_t Cy_SysPm_LdoSetMode(cy_en_syspm_ldo_mode_t mode);
cy_en_syspm_ldo_mode_t Cy_SysPm_LdoGetMode(void);
cy_en_syspm_status_t Cy_SysPm_BuckEnable(cy_en_syspm_buck_voltage1_t voltage);
cy_en_syspm_status_t Cy_SysPm_BuckSetVoltage1(cy_en_syspm_buck_voltage1_t voltage);
void Cy_SysPm_BuckSetVoltage2(cy_en_syspm_buck_voltage2_t voltage, _Bool waitToSettle);
void Cy_SysPm_BuckEnableVoltage2(void);
_Bool Cy_SysPm_BuckIsOutputEnabled(cy_en_syspm_buck_out_t output);
_Bool Cy_SysPm_RegisterCallback(cy_stc_syspm_callback_t *handler);
_Bool Cy_SysPm_UnregisterCallback(cy_stc_syspm_callback_t const *handler);
cy_en_syspm_status_t Cy_SysPm_ExecuteCallback(cy_en_syspm_callback_type_t type, cy_en_syspm_callback_mode_t mode);
cy_stc_syspm_callback_t* Cy_SysPm_GetFailedCallback(cy_en_syspm_callback_type_t type);
_Bool Cy_SysPm_IsSystemUlp(void);
_Bool Cy_SysPm_IsSystemLp(void);
_Bool Cy_SysPm_Cm4IsActive(void);
_Bool Cy_SysPm_Cm4IsSleep(void);
_Bool Cy_SysPm_Cm4IsDeepSleep(void);
_Bool Cy_SysPm_Cm0IsActive(void);
_Bool Cy_SysPm_Cm0IsSleep(void);
_Bool Cy_SysPm_Cm0IsDeepSleep(void);
void Cy_SysPm_CpuSendWakeupEvent(void);
_Bool Cy_SysPm_SystemIsMinRegulatorCurrentSet(void);
_Bool Cy_SysPm_BuckIsEnabled(void);
cy_en_syspm_buck_voltage1_t Cy_SysPm_BuckGetVoltage1(void);
cy_en_syspm_buck_voltage2_t Cy_SysPm_BuckGetVoltage2(void);
void Cy_SysPm_BuckDisableVoltage2(void);
void Cy_SysPm_BuckSetVoltage2HwControl(_Bool hwControl);
_Bool Cy_SysPm_BuckIsVoltage2HwControlled(void);
cy_en_syspm_ldo_voltage_t Cy_SysPm_LdoGetVoltage(void);
_Bool Cy_SysPm_LdoIsEnabled(void);
_Bool Cy_SysPm_IoIsFrozen(void);
void Cy_SysPm_IoUnfreeze(void);
void Cy_SysPm_PmicEnable(void);
void Cy_SysPm_PmicDisable(cy_en_syspm_pmic_wakeup_polarity_t polarity);
void Cy_SysPm_PmicAlwaysEnable(void);
void Cy_SysPm_PmicEnableOutput(void);
void Cy_SysPm_PmicDisableOutput(void);
void Cy_SysPm_PmicLock(void);
void Cy_SysPm_PmicUnlock(void);
_Bool Cy_SysPm_PmicIsEnabled(void);
_Bool Cy_SysPm_PmicIsOutputEnabled(void);
_Bool Cy_SysPm_PmicIsLocked(void);
void Cy_SysPm_BackupSetSupply(cy_en_syspm_vddbackup_control_t vddBackControl);
cy_en_syspm_vddbackup_control_t Cy_SysPm_BackupGetSupply(void);
void Cy_SysPm_BackupEnableVoltageMeasurement(void);
void Cy_SysPm_BackupDisableVoltageMeasurement(void);
void Cy_SysPm_BackupSuperCapCharge(cy_en_syspm_sc_charge_key_t key);
typedef cy_en_syspm_buck_voltage1_t cy_en_syspm_simo_buck_voltage1_t;
typedef cy_en_syspm_buck_voltage2_t cy_en_syspm_simo_buck_voltage2_t;
typedef cy_en_syspm_hibernate_wakeup_source_t cy_en_syspm_hib_wakeup_source_t;

typedef enum
{
    CY_SYSANALOG_SUCCESS = 0x00UL,
    CY_SYSANALOG_BAD_PARAM = ((uint32_t)((uint32_t)((0x17u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01UL,
    CY_SYSANALOG_UNSUPPORTED = ((uint32_t)((uint32_t)((0x17u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02UL
}cy_en_sysanalog_status_t;
typedef enum
{
    CY_SYSANALOG_STARTUP_NORMAL = 0UL,
    CY_SYSANALOG_STARTUP_FAST = 1UL << 0UL
}cy_en_sysanalog_startup_t;
typedef enum
{
    CY_SYSANALOG_VREF_SOURCE_SRSS = 0UL,
    CY_SYSANALOG_VREF_SOURCE_LOCAL_1_2V = 1UL << 20UL,
    CY_SYSANALOG_VREF_SOURCE_EXTERNAL = 2UL << 20UL
}cy_en_sysanalog_vref_source_t;
typedef enum
{
    CY_SYSANALOG_IZTAT_SOURCE_SRSS = 0UL,
    CY_SYSANALOG_IZTAT_SOURCE_LOCAL = 1UL << 16UL
}cy_en_sysanalog_iztat_source_t;
typedef enum
{
    CY_SYSANALOG_DEEPSLEEP_DISABLE = 0UL,
    CY_SYSANALOG_DEEPSLEEP_IPTAT_1 = 0x40000000UL | (1UL << 28UL),
    CY_SYSANALOG_DEEPSLEEP_IPTAT_2 = 0x40000000UL | (2UL << 28UL),
    CY_SYSANALOG_DEEPSLEEP_IPTAT_IZTAT_VREF = 0x40000000UL | (3UL << 28UL)
}cy_en_sysanalog_deep_sleep_t;
typedef enum
{
    CY_SYSANALOG_INTR_CAUSE_CTB0 = 0x1UL,
    CY_SYSANALOG_INTR_CAUSE_CTB1 = 0x2UL,
    CY_SYSANALOG_INTR_CAUSE_CTB2 = 0x4UL,
    CY_SYSANALOG_INTR_CAUSE_CTB3 = 0x8UL,
    CY_SYSANALOG_INTR_CAUSE_CTDAC0 = 0x10UL,
    CY_SYSANALOG_INTR_CAUSE_CTDAC1 = 0x20UL,
    CY_SYSANALOG_INTR_CAUSE_CTDAC2 = 0x40UL,
    CY_SYSANALOG_INTR_CAUSE_CTDAC3 = 0x80UL,
    CY_SYSANALOG_INTR_CAUSE_SAR0 = 0x100UL,
    CY_SYSANALOG_INTR_CAUSE_SAR1 = 0x200UL,
    CY_SYSANALOG_INTR_CAUSE_SAR2 = 0x400UL,
    CY_SYSANALOG_INTR_CAUSE_SAR3 = 0x800UL,
    CY_SYSANALOG_INTR_CAUSE_FIFO0 = 0x1000UL,
    CY_SYSANALOG_INTR_CAUSE_FIFO1 = 0x2000UL,
    CY_SYSANALOG_INTR_CAUSE_FIFO2 = 0x4000UL,
    CY_SYSANALOG_INTR_CAUSE_FIFO3 = 0x8000UL,
}cy_en_sysanalog_intr_cause_t;
typedef enum
{
    CY_SYSANALOG_DEEPSLEEP_SRC_LPOSC = 0UL,
    CY_SYSANALOG_DEEPSLEEP_SRC_CLK_MF = 1UL
}cy_en_sysanalog_deep_sleep_clock_sel_t;
typedef enum
{
    CY_SYSANALOG_DEEPSLEEP_CLK_NO_DIV = 0UL,
    CY_SYSANALOG_DEEPSLEEP_CLK_DIV_BY_2 = 1UL,
    CY_SYSANALOG_DEEPSLEEP_CLK_DIV_BY_4 = 2UL,
    CY_SYSANALOG_DEEPSLEEP_CLK_DIV_BY_8 = 3UL,
    CY_SYSANALOG_DEEPSLEEP_CLK_DIV_BY_16 = 4UL,
}cy_en_sysanalog_deep_sleep_clock_div_t;
typedef enum
{
    CY_SYSANALOG_LPOSC_DUTY_CYCLED = 0UL,
    CY_SYSANALOG_LPOSC_ALWAYS_ON = 1UL
}cy_en_sysanalog_lposc_deep_sleep_mode_t;
typedef enum
{
    CY_SYSANALOG_TIMER_CLK_PERI = 0UL,
    CY_SYSANALOG_TIMER_CLK_DEEPSLEEP = 1UL,
    CY_SYSANALOG_TIMER_CLK_LF = 2UL
}cy_en_sysanalog_timer_clock_t;
typedef struct
{
    cy_en_sysanalog_startup_t startup;
    cy_en_sysanalog_iztat_source_t iztat;
    cy_en_sysanalog_vref_source_t vref;
    cy_en_sysanalog_deep_sleep_t deepSleep;
}cy_stc_sysanalog_config_t;
typedef struct
{
    cy_en_sysanalog_lposc_deep_sleep_mode_t lpOscDsMode;
    cy_en_sysanalog_deep_sleep_clock_sel_t dsClkSource;
    cy_en_sysanalog_deep_sleep_clock_div_t dsClkdivider;
    cy_en_sysanalog_timer_clock_t timerClock;
    uint32_t timerPeriod;
}cy_stc_sysanalog_deep_sleep_config_t;
extern const cy_stc_sysanalog_config_t Cy_SysAnalog_Fast_Local;
extern const cy_stc_sysanalog_config_t Cy_SysAnalog_Fast_SRSS;
extern const cy_stc_sysanalog_config_t Cy_SysAnalog_Fast_External;
cy_en_sysanalog_status_t Cy_SysAnalog_Init(const cy_stc_sysanalog_config_t * config);
static inline void Cy_SysAnalog_DeInit(void);
static inline uint32_t Cy_SysAnalog_GetIntrCauseExtended(const PASS_Type * base);
static inline void Cy_SysAnalog_SetDeepSleepMode(cy_en_sysanalog_deep_sleep_t deepSleep);
static inline cy_en_sysanalog_deep_sleep_t Cy_SysAnalog_GetDeepSleepMode(void);
static inline void Cy_SysAnalog_Enable(void);
static inline void Cy_SysAnalog_Disable(void);
static inline void Cy_SysAnalog_VrefSelect(cy_en_sysanalog_vref_source_t vref);
static inline void Cy_SysAnalog_IztatSelect(cy_en_sysanalog_iztat_source_t iztat);
cy_en_sysanalog_status_t Cy_SysAnalog_DeepSleepInit(PASS_Type * base, const cy_stc_sysanalog_deep_sleep_config_t * config);
static inline void Cy_SysAnalog_LpOscEnable(PASS_Type * base);
static inline void Cy_SysAnalog_LpOscDisable(PASS_Type * base);
static inline void Cy_SysAnalog_TimerEnable(PASS_Type * base);
static inline void Cy_SysAnalog_TimerDisable(PASS_Type * base);
static inline void Cy_SysAnalog_TimerSetPeriod(PASS_Type * base, uint32_t periodVal);
static inline uint32_t Cy_SysAnalog_TimerGetPeriod(const PASS_Type * base);
static inline void Cy_SysAnalog_DeInit(void)
{
    (((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) = (0UL);
}
static inline uint32_t Cy_SysAnalog_GetIntrCauseExtended(const PASS_Type * base)
{
    return (((PASS_V1_Type*) (base))->INTR_CAUSE);
}
static inline uint32_t Cy_SysAnalog_GetIntrCause(void)
{
    uint32_t retVal = 0UL;
    if ((0x20U > cy_device->passVersion))
    {
        retVal = ((uint32_t)CY_SYSANALOG_INTR_CAUSE_CTB0 |
                  (uint32_t)CY_SYSANALOG_INTR_CAUSE_CTB1 |
                  (uint32_t)CY_SYSANALOG_INTR_CAUSE_CTB2 |
                  (uint32_t)CY_SYSANALOG_INTR_CAUSE_CTB3 |
                  (uint32_t)CY_SYSANALOG_INTR_CAUSE_CTDAC0 |
                  (uint32_t)CY_SYSANALOG_INTR_CAUSE_CTDAC1 |
                  (uint32_t)CY_SYSANALOG_INTR_CAUSE_CTDAC2 |
                  (uint32_t)CY_SYSANALOG_INTR_CAUSE_CTDAC3) &
                  Cy_SysAnalog_GetIntrCauseExtended(((PASS_Type*)cy_device->passBase));
    }
    return (retVal);
}
static inline void Cy_SysAnalog_SetDeepSleepMode(cy_en_sysanalog_deep_sleep_t deepSleep)
{
    do { if(!((((deepSleep) == CY_SYSANALOG_DEEPSLEEP_DISABLE) || ((deepSleep) == CY_SYSANALOG_DEEPSLEEP_IPTAT_1) || ((deepSleep) == CY_SYSANALOG_DEEPSLEEP_IPTAT_2) || ((deepSleep) == CY_SYSANALOG_DEEPSLEEP_IPTAT_IZTAT_VREF)))) { CY_HALT(); } } while (0);
    (((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) = ((((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) & ~(0x40000000UL | 0x30000000UL)) | (uint32_t) deepSleep;
}
static inline cy_en_sysanalog_deep_sleep_t Cy_SysAnalog_GetDeepSleepMode(void)
{
    return (cy_en_sysanalog_deep_sleep_t) (uint32_t) ((((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) & (0x40000000UL | 0x30000000UL));
}
static inline void Cy_SysAnalog_Enable(void)
{
    (((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) |= 0x80000000UL;
}
static inline void Cy_SysAnalog_Disable(void)
{
    (((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) &= ~0x80000000UL;
}
static inline void Cy_SysAnalog_SetArefMode(cy_en_sysanalog_startup_t startup)
{
    ( (void)(startup) );
    (((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) |= (uint32_t)CY_SYSANALOG_STARTUP_FAST;
}
static inline void Cy_SysAnalog_VrefSelect(cy_en_sysanalog_vref_source_t vref)
{
    do { if(!((((vref) == CY_SYSANALOG_VREF_SOURCE_SRSS) || ((vref) == CY_SYSANALOG_VREF_SOURCE_LOCAL_1_2V) || ((vref) == CY_SYSANALOG_VREF_SOURCE_EXTERNAL)))) { CY_HALT(); } } while (0);
    (((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) = ((((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) & ~0x300000UL) | (uint32_t) vref;
}
static inline void Cy_SysAnalog_IztatSelect(cy_en_sysanalog_iztat_source_t iztat)
{
    do { if(!((((iztat) == CY_SYSANALOG_IZTAT_SOURCE_SRSS) || ((iztat) == CY_SYSANALOG_IZTAT_SOURCE_LOCAL)))) { CY_HALT(); } } while (0);
    (((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) = ((((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) & ~0x10000UL) | (uint32_t) iztat;
}
static inline void Cy_SysAnalog_LpOscEnable(PASS_Type * base)
{
    if(!(0x20U > cy_device->passVersion))
    {
        (((PASS_V2_Type*) (base))->LPOSC.CTRL) = 0x80000000UL;
    }
    else
    {
        do { if(!(0)) { CY_HALT(); } } while (0);
    }
}
static inline void Cy_SysAnalog_LpOscDisable(PASS_Type * base)
{
    if(!(0x20U > cy_device->passVersion))
    {
        (((PASS_V2_Type*) (base))->LPOSC.CTRL) = 0UL;
    }
}
static inline void Cy_SysAnalog_TimerEnable(PASS_Type * base)
{
    if (!(0x20U > cy_device->passVersion))
    {
        (((PASS_V2_Type*) (base))->TIMER.CTRL) = 0x80000000UL;
    }
}
static inline void Cy_SysAnalog_TimerDisable(PASS_Type * base)
{
    if (!(0x20U > cy_device->passVersion))
    {
        (((PASS_V2_Type*) (base))->TIMER.CTRL) = 0UL;
    }
}
static inline void Cy_SysAnalog_TimerSetPeriod(PASS_Type * base, uint32_t periodVal)
{
    if (!(0x20U > cy_device->passVersion))
    {
        (((PASS_V2_Type*) (base))->TIMER.PERIOD) = (((uint32_t)(periodVal) << 0UL) & 0xFFFFUL);
    }
    else
    {
        do { if(!(0)) { CY_HALT(); } } while (0);
    }
}
static inline uint32_t Cy_SysAnalog_TimerGetPeriod(const PASS_Type * base)
{
    uint32_t period = 0UL;
    if (!(0x20U > cy_device->passVersion))
    {
        period = (((uint32_t)((((PASS_V2_Type*) (base))->TIMER.PERIOD)) & 0xFFFFUL) >> 0UL);
    }
    return period;
}


typedef enum{
    CY_CTB_OPAMP_NONE = 0UL,
    CY_CTB_OPAMP_0 = 0x1UL,
    CY_CTB_OPAMP_1 = 0x2UL,
    CY_CTB_OPAMP_BOTH = 0x1UL | 0x2UL,
}cy_en_ctb_opamp_sel_t;
typedef enum {
    CY_CTB_DEEPSLEEP_DISABLE = 0UL,
    CY_CTB_DEEPSLEEP_ENABLE = 0x40000000UL,
}cy_en_ctb_deep_sleep_t;
typedef enum {
    CY_CTB_POWER_OFF = 0UL,
    CY_CTB_POWER_LOW = 1UL,
    CY_CTB_POWER_MEDIUM = 2UL,
    CY_CTB_POWER_HIGH = 3UL,
    CY_CTB_POWER_PS_LOW = 5UL,
    CY_CTB_POWER_PS_MEDIUM = 6UL,
    CY_CTB_POWER_PS_HIGH = 7UL,
}cy_en_ctb_power_t;
typedef enum {
    CY_CTB_MODE_OPAMP1X = 0UL,
    CY_CTB_MODE_OPAMP10X = 1UL << 3UL,
    CY_CTB_MODE_COMP = 1UL << 4UL,
}cy_en_ctb_mode_t;
typedef enum{
    CY_CTB_PUMP_DISABLE = 0UL,
    CY_CTB_PUMP_ENABLE = 0x800UL,
}cy_en_ctb_pump_t;
typedef enum
{
    CY_CTB_COMP_EDGE_DISABLE = 0UL,
    CY_CTB_COMP_EDGE_RISING = 1UL << 8UL,
    CY_CTB_COMP_EDGE_FALLING = 2UL << 8UL,
    CY_CTB_COMP_EDGE_BOTH = 3UL << 8UL,
}cy_en_ctb_comp_edge_t;
typedef enum
{
    CY_CTB_COMP_DSI_TRIGGER_OUT_PULSE = 0UL,
    CY_CTB_COMP_DSI_TRIGGER_OUT_LEVEL = 0x80UL,
}cy_en_ctb_comp_level_t;
typedef enum
{
    CY_CTB_COMP_BYPASS_SYNC = 0UL,
    CY_CTB_COMP_BYPASS_NO_SYNC = 0x40UL,
}cy_en_ctb_comp_bypass_t;
typedef enum
{
    CY_CTB_COMP_HYST_DISABLE = 0UL,
    CY_CTB_COMP_HYST_10MV = 0x20UL,
}cy_en_ctb_comp_hyst_t;
typedef enum
{
    CY_CTB_SWITCH_OPEN = 0UL,
    CY_CTB_SWITCH_CLOSE = 1UL
}cy_en_ctb_switch_state_t;
typedef enum
{
    CY_CTB_SWITCH_OA0_SW = 0UL,
    CY_CTB_SWITCH_OA1_SW = 1UL,
    CY_CTB_SWITCH_CTD_SW = 2UL,
}cy_en_ctb_switch_register_sel_t;
typedef enum
{
    CY_CTB_SW_OA0_POS_AMUXBUSA_MASK = 0x1UL,
    CY_CTB_SW_OA0_POS_PIN0_MASK = 0x4UL,
    CY_CTB_SW_OA0_POS_PIN6_MASK = 0x8UL,
    CY_CTB_SW_OA0_NEG_PIN1_MASK = 0x100UL,
    CY_CTB_SW_OA0_NEG_OUT_MASK = 0x4000UL,
    CY_CTB_SW_OA0_OUT_SARBUS0_MASK = 0x40000UL,
    CY_CTB_SW_OA0_OUT_SHORT_1X_10X_MASK = 0x200000UL,
}cy_en_ctb_oa0_switches_t;
typedef enum
{
    CY_CTB_SW_OA1_POS_AMUXBUSB_MASK = 0x1UL,
    CY_CTB_SW_OA1_POS_PIN5_MASK = 0x2UL,
    CY_CTB_SW_OA1_POS_PIN7_MASK = 0x10UL,
    CY_CTB_SW_OA1_POS_AREF_MASK = 0x80UL,
    CY_CTB_SW_OA1_NEG_PIN4_MASK = 0x100UL,
    CY_CTB_SW_OA1_NEG_OUT_MASK = 0x4000UL,
    CY_CTB_SW_OA1_OUT_SARBUS0_MASK = 0x40000UL,
    CY_CTB_SW_OA1_OUT_SARBUS1_MASK = 0x80000UL,
    CY_CTB_SW_OA1_OUT_SHORT_1X_10X_MASK = 0x200000UL,
}cy_en_ctb_oa1_switches_t;
typedef enum
{
    CY_CTB_SW_CTD_REF_OA1_OUT_MASK = 0x2UL,
    CY_CTB_SW_CTD_REFSENSE_OA1_NEG_MASK = 0x10UL,
    CY_CTB_SW_CTD_OUT_OA1_NEG_MASK = 0x20UL,
    CY_CTB_SW_CTD_OUT_PIN6_MASK = 0x100UL,
    CY_CTB_SW_CTD_OUT_CHOLD_MASK = 0x200UL,
    CY_CTB_SW_CTD_OUT_OA0_1X_OUT_MASK = 0x400UL,
    CY_CTB_SW_CTD_CHOLD_CONNECT_MASK = 0x1000UL,
    CY_CTB_SW_CTD_CHOLD_OA0_POS_MASK = 0x2000UL,
    CY_CTB_SW_CTD_CHOLD_OA0_POS_ISOLATE_MASK = 0x4000UL,
    CY_CTB_SW_CTD_CHOLD_LEAKAGE_REDUCTION_MASK = 0x8000UL,
}cy_en_ctb_ctd_switches_t;
typedef enum
{
    CY_CTB_SW_SEQ_CTRL_D51_MASK = 0x400UL,
    CY_CTB_SW_SEQ_CTRL_D52_D62_MASK = 0x800UL,
    CY_CTB_SW_SEQ_CTRL_D51_D52_D62_MASK = 0x400UL | 0x800UL,
}cy_en_ctb_switch_sar_seq_t;
typedef enum
{
    CY_CTB_OPAMP_COMPENSATION_CAP_OFF = 0UL,
    CY_CTB_OPAMP_COMPENSATION_CAP_MIN = 1UL,
    CY_CTB_OPAMP_COMPENSATION_CAP_MED = 2UL,
    CY_CTB_OPAMP_COMPENSATION_CAP_MAX = 3UL,
}cy_en_ctb_compensation_cap_t;
typedef enum
{
    CY_CTB_OPAMP_BOOST_DISABLE = 0UL,
    CY_CTB_OPAMP_BOOST_ENABLE = 0x1000UL,
}cy_en_ctb_boost_en_t;
typedef enum
{
    CY_CTB_SH_DISABLE = 0UL,
    CY_CTB_SH_PREPARE_SAMPLE = 1UL,
    CY_CTB_SH_SAMPLE = 2UL,
    CY_CTB_SH_PREPARE_HOLD = 3UL,
    CY_CTB_SH_HOLD = 4UL,
}cy_en_ctb_sample_hold_mode_t;
typedef enum
{
    CY_CTB_IPTAT_NORMAL = 0UL,
    CY_CTB_IPTAT_LOW = 1UL << 7UL,
}cy_en_ctb_iptat_t;
typedef enum
{
    CY_CTB_CLK_PUMP_SRSS = 0UL,
    CY_CTB_CLK_PUMP_PERI = 1UL << 19UL,
    CY_CTB_CLK_PUMP_DEEPSLEEP = 1UL
}cy_en_ctb_clk_pump_source_t;
typedef enum
{
    CY_CTB_CURRENT_HIGH_ACTIVE = 0UL,
    CY_CTB_CURRENT_HIGH_ACTIVE_DEEPSLEEP = 1UL,
    CY_CTB_CURRENT_LOW_ACTIVE_DEEPSLEEP = 2UL,
}cy_en_ctb_current_mode_t;
typedef enum {
    CY_CTB_SUCCESS = 0x00UL,
    CY_CTB_BAD_PARAM = ((uint32_t)((uint32_t)((0x0Bu) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01UL,
}cy_en_ctb_status_t;
typedef struct {
    cy_en_ctb_deep_sleep_t deepSleep;
    cy_en_ctb_power_t oa0Power;
    cy_en_ctb_mode_t oa0Mode;
    cy_en_ctb_pump_t oa0Pump;
    cy_en_ctb_comp_edge_t oa0CompEdge;
    cy_en_ctb_comp_level_t oa0CompLevel;
    cy_en_ctb_comp_bypass_t oa0CompBypass;
    cy_en_ctb_comp_hyst_t oa0CompHyst;
    _Bool oa0CompIntrEn;
    cy_en_ctb_power_t oa1Power;
    cy_en_ctb_mode_t oa1Mode;
    cy_en_ctb_pump_t oa1Pump;
    cy_en_ctb_comp_edge_t oa1CompEdge;
    cy_en_ctb_comp_level_t oa1CompLevel;
    cy_en_ctb_comp_bypass_t oa1CompBypass;
    cy_en_ctb_comp_hyst_t oa1CompHyst;
    _Bool oa1CompIntrEn;
    _Bool configRouting;
    uint32_t oa0SwitchCtrl;
    uint32_t oa1SwitchCtrl;
    uint32_t ctdSwitchCtrl;
}cy_stc_ctb_config_t;
typedef struct {
    cy_en_ctb_deep_sleep_t deepSleep;
    cy_en_ctb_power_t oaPower;
    cy_en_ctb_mode_t oaMode;
    cy_en_ctb_pump_t oaPump;
    cy_en_ctb_comp_edge_t oaCompEdge;
    cy_en_ctb_comp_level_t oaCompLevel;
    cy_en_ctb_comp_bypass_t oaCompBypass;
    cy_en_ctb_comp_hyst_t oaCompHyst;
    _Bool oaCompIntrEn;
}cy_stc_ctb_opamp_config_t;
typedef struct
{
    cy_en_ctb_power_t oa0Power;
    cy_en_ctb_mode_t oa0Mode;
    uint32_t oa0SwitchCtrl;
    uint32_t ctdSwitchCtrl;
}cy_stc_ctb_fast_config_oa0_t;
typedef struct
{
    cy_en_ctb_power_t oa1Power;
    cy_en_ctb_mode_t oa1Mode;
    uint32_t oa1SwitchCtrl;
    uint32_t ctdSwitchCtrl;
}cy_stc_ctb_fast_config_oa1_t;
extern const cy_stc_ctb_fast_config_oa0_t Cy_CTB_Fast_Opamp0_Unused;
extern const cy_stc_ctb_fast_config_oa0_t Cy_CTB_Fast_Opamp0_Comp;
extern const cy_stc_ctb_fast_config_oa0_t Cy_CTB_Fast_Opamp0_Opamp1x;
extern const cy_stc_ctb_fast_config_oa0_t Cy_CTB_Fast_Opamp0_Opamp10x;
extern const cy_stc_ctb_fast_config_oa0_t Cy_CTB_Fast_Opamp0_Diffamp;
extern const cy_stc_ctb_fast_config_oa0_t Cy_CTB_Fast_Opamp0_Vdac_Out;
extern const cy_stc_ctb_fast_config_oa0_t Cy_CTB_Fast_Opamp0_Vdac_Out_SH;
extern const cy_stc_ctb_fast_config_oa1_t Cy_CTB_Fast_Opamp1_Unused;
extern const cy_stc_ctb_fast_config_oa1_t Cy_CTB_Fast_Opamp1_Comp;
extern const cy_stc_ctb_fast_config_oa1_t Cy_CTB_Fast_Opamp1_Opamp1x;
extern const cy_stc_ctb_fast_config_oa1_t Cy_CTB_Fast_Opamp1_Opamp10x;
extern const cy_stc_ctb_fast_config_oa1_t Cy_CTB_Fast_Opamp1_Diffamp;
extern const cy_stc_ctb_fast_config_oa1_t Cy_CTB_Fast_Opamp1_Vdac_Ref_Aref;
extern const cy_stc_ctb_fast_config_oa1_t Cy_CTB_Fast_Opamp1_Vdac_Ref_Pin5;
cy_en_ctb_status_t Cy_CTB_Init(CTBM_Type *base, const cy_stc_ctb_config_t *config);
cy_en_ctb_status_t Cy_CTB_OpampInit(CTBM_Type *base, cy_en_ctb_opamp_sel_t opampNum, const cy_stc_ctb_opamp_config_t *config);
cy_en_ctb_status_t Cy_CTB_DeInit(CTBM_Type *base, _Bool deInitRouting);
cy_en_ctb_status_t Cy_CTB_FastInit(CTBM_Type *base, const cy_stc_ctb_fast_config_oa0_t *config0, const cy_stc_ctb_fast_config_oa1_t *config1);
              void Cy_CTB_Enable(CTBM_Type *base);
              void Cy_CTB_Disable(CTBM_Type *base);
void Cy_CTB_SetDeepSleepMode(CTBM_Type *base, cy_en_ctb_deep_sleep_t deepSleep);
void Cy_CTB_SetOutputMode(CTBM_Type *base, cy_en_ctb_opamp_sel_t opampNum, cy_en_ctb_mode_t mode);
void Cy_CTB_SetPower(CTBM_Type *base, cy_en_ctb_opamp_sel_t opampNum, cy_en_ctb_power_t power, cy_en_ctb_pump_t pump);
void Cy_CTB_DACSampleAndHold(CTBM_Type *base, cy_en_ctb_sample_hold_mode_t mode);
void Cy_CTB_CompSetConfig(CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum, cy_en_ctb_comp_level_t level, cy_en_ctb_comp_bypass_t bypass, cy_en_ctb_comp_hyst_t hyst);
uint32_t Cy_CTB_CompGetConfig(const CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum);
void Cy_CTB_CompSetInterruptEdgeType(CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum, cy_en_ctb_comp_edge_t edge);
uint32_t Cy_CTB_CompGetStatus(const CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum);
void Cy_CTB_OpampSetOffset(CTBM_Type *base, cy_en_ctb_opamp_sel_t opampNum, uint32_t trim);
uint32_t Cy_CTB_OpampGetOffset(const CTBM_Type *base, cy_en_ctb_opamp_sel_t opampNum);
void Cy_CTB_OpampSetSlope(CTBM_Type *base, cy_en_ctb_opamp_sel_t opampNum, uint32_t trim);
uint32_t Cy_CTB_OpampGetSlope(const CTBM_Type *base, cy_en_ctb_opamp_sel_t opampNum);
void Cy_CTB_SetAnalogSwitch(CTBM_Type *base, cy_en_ctb_switch_register_sel_t switchSelect, uint32_t switchMask, cy_en_ctb_switch_state_t state);
uint32_t Cy_CTB_GetAnalogSwitch(const CTBM_Type *base, cy_en_ctb_switch_register_sel_t switchSelect);
static inline void Cy_CTB_OpenAllSwitches(CTBM_Type *base);
static inline void Cy_CTB_EnableSarSeqCtrl(CTBM_Type *base, cy_en_ctb_switch_sar_seq_t switchMask);
static inline void Cy_CTB_DisableSarSeqCtrl(CTBM_Type *base, cy_en_ctb_switch_sar_seq_t switchMask);
static inline uint32_t Cy_CTB_GetInterruptStatus(const CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum);
static inline void Cy_CTB_ClearInterrupt(CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum);
static inline void Cy_CTB_SetInterrupt(CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum);
static inline void Cy_CTB_SetInterruptMask(CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum);
static inline uint32_t Cy_CTB_GetInterruptMask(const CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum);
static inline uint32_t Cy_CTB_GetInterruptStatusMasked(const CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum);
void Cy_CTB_SetCurrentMode(CTBM_Type *base, cy_en_ctb_current_mode_t currentMode);
static inline void Cy_CTB_SetIptatLevel(cy_en_ctb_iptat_t iptat);
static inline void Cy_CTB_SetPumpClkSource(PASS_Type * base, cy_en_ctb_clk_pump_source_t pumpClk);
static inline void Cy_CTB_EnableRedirect(void);
static inline void Cy_CTB_DisableRedirect(void);
static inline void Cy_CTB_OpenAllSwitches(CTBM_Type *base)
{
    (((CTBM_V1_Type *) (base))->OA0_SW_CLEAR) = (0x1UL | 0x4UL | 0x8UL | 0x100UL | 0x4000UL | 0x40000UL | 0x200000UL);
    (((CTBM_V1_Type *) (base))->OA1_SW_CLEAR) = (0x1UL | 0x2UL | 0x10UL | 0x80UL | 0x100UL | 0x4000UL | 0x40000UL | 0x80000UL | 0x200000UL);
    (((CTBM_V1_Type *) (base))->CTD_SW_CLEAR) = (0x2UL | 0x10UL | 0x20UL | 0x100UL | 0x200UL | 0x400UL | 0x1000UL | 0x2000UL | 0x4000UL | 0x8000UL);
    (((CTBM_V1_Type *) (base))->CTB_SW_DS_CTRL) = (0UL);
    (((CTBM_V1_Type *) (base))->CTB_SW_SQ_CTRL) = (0UL);
}
static inline void Cy_CTB_EnableSarSeqCtrl(CTBM_Type *base, cy_en_ctb_switch_sar_seq_t switchMask)
{
    do { if(!((((switchMask) == CY_CTB_SW_SEQ_CTRL_D51_MASK) || ((switchMask) == CY_CTB_SW_SEQ_CTRL_D52_D62_MASK) || ((switchMask) == CY_CTB_SW_SEQ_CTRL_D51_D52_D62_MASK)))) { CY_HALT(); } } while (0);
    (((CTBM_V1_Type *) (base))->CTB_SW_SQ_CTRL) |= (uint32_t) switchMask;
}
static inline void Cy_CTB_DisableSarSeqCtrl(CTBM_Type *base, cy_en_ctb_switch_sar_seq_t switchMask)
{
    do { if(!((((switchMask) == CY_CTB_SW_SEQ_CTRL_D51_MASK) || ((switchMask) == CY_CTB_SW_SEQ_CTRL_D52_D62_MASK) || ((switchMask) == CY_CTB_SW_SEQ_CTRL_D51_D52_D62_MASK)))) { CY_HALT(); } } while (0);
    (((CTBM_V1_Type *) (base))->CTB_SW_SQ_CTRL) &= ~((uint32_t) switchMask);
}
static inline uint32_t Cy_CTB_GetInterruptStatus(const CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum)
{
    do { if(!((((compNum) == CY_CTB_OPAMP_0) || ((compNum) == CY_CTB_OPAMP_1) || ((compNum) == CY_CTB_OPAMP_BOTH)))) { CY_HALT(); } } while (0);
    return (((CTBM_V1_Type *) (base))->INTR) & (uint32_t) compNum;
}
static inline void Cy_CTB_ClearInterrupt(CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum)
{
    do { if(!((((compNum) == CY_CTB_OPAMP_0) || ((compNum) == CY_CTB_OPAMP_1) || ((compNum) == CY_CTB_OPAMP_BOTH)))) { CY_HALT(); } } while (0);
    (((CTBM_V1_Type *) (base))->INTR) = (uint32_t) compNum;
    (void) (((CTBM_V1_Type *) (base))->INTR);
}
static inline void Cy_CTB_SetInterrupt(CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum)
{
    do { if(!((((compNum) == CY_CTB_OPAMP_0) || ((compNum) == CY_CTB_OPAMP_1) || ((compNum) == CY_CTB_OPAMP_BOTH)))) { CY_HALT(); } } while (0);
    (((CTBM_V1_Type *) (base))->INTR_SET) = (uint32_t) compNum;
}
static inline void Cy_CTB_SetInterruptMask(CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum)
{
    do { if(!((((compNum) == CY_CTB_OPAMP_NONE) || ((compNum) == CY_CTB_OPAMP_0) || ((compNum) == CY_CTB_OPAMP_1) || ((compNum) == CY_CTB_OPAMP_BOTH)))) { CY_HALT(); } } while (0);
    (((CTBM_V1_Type *) (base))->INTR_MASK) = (uint32_t) compNum;
}
static inline uint32_t Cy_CTB_GetInterruptMask(const CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum)
{
    do { if(!((((compNum) == CY_CTB_OPAMP_0) || ((compNum) == CY_CTB_OPAMP_1) || ((compNum) == CY_CTB_OPAMP_BOTH)))) { CY_HALT(); } } while (0);
    return (((CTBM_V1_Type *) (base))->INTR_MASK) & (uint32_t) compNum;
}
static inline uint32_t Cy_CTB_GetInterruptStatusMasked(const CTBM_Type *base, cy_en_ctb_opamp_sel_t compNum)
{
    do { if(!((((compNum) == CY_CTB_OPAMP_0) || ((compNum) == CY_CTB_OPAMP_1) || ((compNum) == CY_CTB_OPAMP_BOTH)))) { CY_HALT(); } } while (0);
    return (((CTBM_V1_Type *) (base))->INTR_MASKED) & (uint32_t) compNum;
}
static inline void Cy_CTB_SetIptatLevel(cy_en_ctb_iptat_t iptat)
{
    do { if(!((((iptat) == CY_CTB_IPTAT_NORMAL) || ((iptat) == CY_CTB_IPTAT_LOW)))) { CY_HALT(); } } while (0);
    (((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) = ((((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) & ~0x80UL) | (uint32_t) iptat;
}
static inline void Cy_CTB_SetPumpClkSource(PASS_Type * base, cy_en_ctb_clk_pump_source_t pumpClk)
{
    do { if(!((((pumpClk) == CY_CTB_CLK_PUMP_SRSS) || ((pumpClk) == CY_CTB_CLK_PUMP_PERI) || ((pumpClk) == CY_CTB_CLK_PUMP_DEEPSLEEP)))) { CY_HALT(); } } while (0);
    ( (void)(base) );
    if (CY_CTB_CLK_PUMP_DEEPSLEEP == pumpClk)
    {
        if (!(0x20U > cy_device->passVersion))
        {
            do{}while(0);
            (((((((void *)0) != (((CTBM_Type*) 0x41100000UL))) ? ((PASS_V2_Type*) cy_device->passBase) : ((void *)0))->CTBM_CLOCK_SEL[((((void *)0) != (((CTBM_Type*) 0x41100000UL))) ? 0UL : 0UL)])) = (((((((((void *)0) != (((CTBM_Type*) 0x41100000UL))) ? ((PASS_V2_Type*) cy_device->passBase) : ((void *)0))->CTBM_CLOCK_SEL[((((void *)0) != (((CTBM_Type*) 0x41100000UL))) ? 0UL : 0UL)]))) & ((uint32_t)(~(0x1UL)))) | ((((uint32_t)((pumpClk)) << 0UL) & 0x1UL))));
        }
        else
        {
            do { if(!(0)) { CY_HALT(); } } while (0);
        }
    }
    else
    {
        (((((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL)) = (((((((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL))) & ((uint32_t)(~(0x80000UL)))) | ((((uint32_t)(((CY_CTB_CLK_PUMP_PERI == pumpClk) ? 1UL : 0UL)) << 19UL) & 0x80000UL))));
    }
}
static inline void Cy_CTB_SetClkPumpSource(cy_en_ctb_clk_pump_source_t clkPump)
{
    if ((0x20U > cy_device->passVersion))
    {
        do { if(!(CY_CTB_CLK_PUMP_DEEPSLEEP != clkPump)) { CY_HALT(); } } while (0);
        (((((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL)) = (((((((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL))) & ((uint32_t)(~(0x80000UL)))) | ((((uint32_t)(((CY_CTB_CLK_PUMP_PERI == clkPump) ? 1UL : 0UL)) << 19UL) & 0x80000UL))));
    }
}
static inline void Cy_CTB_EnableRedirect(void)
{
    (((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) |= 0xFF00UL;
}
static inline void Cy_CTB_DisableRedirect(void)
{
    (((PASS_V1_Type*) ((PASS_Type*)cy_device->passBase))->AREF.AREF_CTRL) &= ~(0xFF00UL);
}

typedef enum
{
    CY_SYSCLK_SUCCESS = 0x00UL,
    CY_SYSCLK_BAD_PARAM = (((uint32_t)((uint32_t)((0x12U) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01UL),
    CY_SYSCLK_TIMEOUT = (((uint32_t)((uint32_t)((0x12U) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02UL),
    CY_SYSCLK_INVALID_STATE = (((uint32_t)((uint32_t)((0x12U) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x03UL),
    CY_SYSCLK_UNSUPPORTED_STATE = (((uint32_t)((uint32_t)((0x12U) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x04UL)
} cy_en_sysclk_status_t;
void Cy_SysClk_ExtClkSetFrequency(uint32_t freq);
uint32_t Cy_SysClk_ExtClkGetFrequency(void);
void Cy_SysClk_EcoSetFrequency(uint32_t freq);
cy_en_sysclk_status_t Cy_SysClk_EcoConfigure(uint32_t freq, uint32_t cSum, uint32_t esr, uint32_t driveLevel);
cy_en_sysclk_status_t Cy_SysClk_EcoEnable(uint32_t timeoutus);
uint32_t Cy_SysClk_EcoGetFrequency(void);
void Cy_SysClk_EcoDisable(void);
uint32_t Cy_SysClk_EcoGetStatus(void);
typedef enum
{
    CY_SYSCLK_CLKPATH_IN_IMO = 0U,
    CY_SYSCLK_CLKPATH_IN_EXT = 1U,
    CY_SYSCLK_CLKPATH_IN_ECO = 2U,
    CY_SYSCLK_CLKPATH_IN_ALTHF = 3U,
    CY_SYSCLK_CLKPATH_IN_DSIMUX = 4U,
    CY_SYSCLK_CLKPATH_IN_DSI = 0x100U,
    CY_SYSCLK_CLKPATH_IN_ILO = 0x110U,
    CY_SYSCLK_CLKPATH_IN_WCO = 0x111U,
    CY_SYSCLK_CLKPATH_IN_ALTLF = 0x112U,
    CY_SYSCLK_CLKPATH_IN_PILO = 0x113U,
} cy_en_clkpath_in_sources_t;
cy_en_sysclk_status_t Cy_SysClk_ClkPathSetSource(uint32_t clkPath, cy_en_clkpath_in_sources_t source);
cy_en_clkpath_in_sources_t Cy_SysClk_ClkPathGetSource(uint32_t clkPath);
uint32_t Cy_SysClk_ClkPathMuxGetFrequency(uint32_t clkPath);
uint32_t Cy_SysClk_ClkPathGetFrequency(uint32_t clkPath);
typedef enum
{
    CY_SYSCLK_FLLPLL_OUTPUT_AUTO = 0U,
    CY_SYSCLK_FLLPLL_OUTPUT_AUTO1 = 1U,
    CY_SYSCLK_FLLPLL_OUTPUT_INPUT = 2U,
    CY_SYSCLK_FLLPLL_OUTPUT_OUTPUT = 3U
} cy_en_fll_pll_output_mode_t;
typedef enum
{
    CY_SYSCLK_FLL_CCO_RANGE0,
    CY_SYSCLK_FLL_CCO_RANGE1,
    CY_SYSCLK_FLL_CCO_RANGE2,
    CY_SYSCLK_FLL_CCO_RANGE3,
    CY_SYSCLK_FLL_CCO_RANGE4
} cy_en_fll_cco_ranges_t;
typedef struct
{
    uint32_t fllMult;
    uint16_t refDiv;
    cy_en_fll_cco_ranges_t ccoRange;
    _Bool enableOutputDiv;
    uint16_t lockTolerance;
    uint8_t igain;
    uint8_t pgain;
    uint16_t settlingCount;
    cy_en_fll_pll_output_mode_t outputMode;
    uint16_t cco_Freq;
} cy_stc_fll_manual_config_t;
cy_en_sysclk_status_t Cy_SysClk_FllConfigure(uint32_t inputFreq, uint32_t outputFreq, cy_en_fll_pll_output_mode_t outputMode);
cy_en_sysclk_status_t Cy_SysClk_FllManualConfigure(const cy_stc_fll_manual_config_t *config);
void Cy_SysClk_FllGetConfiguration(cy_stc_fll_manual_config_t *config);
cy_en_sysclk_status_t Cy_SysClk_FllEnable(uint32_t timeoutus);
_Bool Cy_SysClk_FllIsEnabled(void);
_Bool Cy_SysClk_FllLocked(void);
cy_en_sysclk_status_t Cy_SysClk_FllDisable(void);
uint32_t Cy_SysClk_FllGetFrequency(void);
typedef struct
{
    uint32_t inputFreq;
    uint32_t outputFreq;
    _Bool lfMode;
    cy_en_fll_pll_output_mode_t outputMode;
} cy_stc_pll_config_t;
typedef struct
{
    uint8_t feedbackDiv;
    uint8_t referenceDiv;
    uint8_t outputDiv;
    _Bool lfMode;
    cy_en_fll_pll_output_mode_t outputMode;
} cy_stc_pll_manual_config_t;
cy_en_sysclk_status_t Cy_SysClk_PllConfigure(uint32_t clkPath, const cy_stc_pll_config_t *config);
cy_en_sysclk_status_t Cy_SysClk_PllManualConfigure(uint32_t clkPath, const cy_stc_pll_manual_config_t *config);
cy_en_sysclk_status_t Cy_SysClk_PllGetConfiguration(uint32_t clkPath, cy_stc_pll_manual_config_t *config);
cy_en_sysclk_status_t Cy_SysClk_PllEnable(uint32_t clkPath, uint32_t timeoutus);
_Bool Cy_SysClk_PllIsEnabled(uint32_t clkPath);
_Bool Cy_SysClk_PllLocked(uint32_t clkPath);
_Bool Cy_SysClk_PllLostLock(uint32_t clkPath);
cy_en_sysclk_status_t Cy_SysClk_PllDisable(uint32_t clkPath);
uint32_t Cy_SysClk_PllGetFrequency(uint32_t clkPath);
void Cy_SysClk_IloEnable(void);
_Bool Cy_SysClk_IloIsEnabled(void);
cy_en_sysclk_status_t Cy_SysClk_IloDisable(void);
void Cy_SysClk_IloHibernateOn(_Bool on);
void Cy_SysClk_PiloEnable(void);
_Bool Cy_SysClk_PiloIsEnabled(void);
void Cy_SysClk_PiloDisable(void);
void Cy_SysClk_PiloSetTrim(uint32_t trimVal);
uint32_t Cy_SysClk_PiloGetTrim(void);
uint32_t Cy_SysClk_AltHfGetFrequency(void);
uint32_t Cy_SysClk_AltLfGetFrequency(void);
_Bool Cy_SysClk_AltLfIsEnabled(void);
typedef enum
{
    CY_SYSCLK_MEAS_CLK_NC = 0U,
    CY_SYSCLK_MEAS_CLK_ILO = 1U,
    CY_SYSCLK_MEAS_CLK_WCO = 2U,
    CY_SYSCLK_MEAS_CLK_BAK = 3U,
    CY_SYSCLK_MEAS_CLK_ALTLF = 4U,
    CY_SYSCLK_MEAS_CLK_LFCLK = 5U,
    CY_SYSCLK_MEAS_CLK_IMO = 6U,
    CY_SYSCLK_MEAS_CLK_SLPCTRL = 7U,
    CY_SYSCLK_MEAS_CLK_PILO = 8U,
    CY_SYSCLK_MEAS_CLK_ILO1 = 9U,
    CY_SYSCLK_MEAS_CLK_ECO_PRESCALER = 10U,
    CY_SYSCLK_MEAS_CLK_LPECO = 11U,
    CY_SYSCLK_MEAS_CLK_LPECO_PRESCALER = 12U,
    CY_SYSCLK_MEAS_CLK_MFO = 13U,
    CY_SYSCLK_MEAS_CLK_FAST_CLKS = 0x100U,
    CY_SYSCLK_MEAS_CLK_ECO = 0x101U,
    CY_SYSCLK_MEAS_CLK_EXT = 0x102U,
    CY_SYSCLK_MEAS_CLK_ALTHF = 0x103U,
    CY_SYSCLK_MEAS_CLK_TIMERCLK = 0x104U,
    CY_SYSCLK_MEAS_CLK_IHO = 0x108U,
    CY_SYSCLK_MEAS_CLK_PWR = 0x109U,
    CY_SYSCLK_MEAS_CLK_PATH_CLKS = 0x500U,
    CY_SYSCLK_MEAS_CLK_PATH0 = 0x500U,
    CY_SYSCLK_MEAS_CLK_PATH1 = 0x501U,
    CY_SYSCLK_MEAS_CLK_PATH2 = 0x502U,
    CY_SYSCLK_MEAS_CLK_PATH3 = 0x503U,
    CY_SYSCLK_MEAS_CLK_PATH4 = 0x504U,
    CY_SYSCLK_MEAS_CLK_PATH5 = 0x505U,
    CY_SYSCLK_MEAS_CLK_PATH6 = 0x506U,
    CY_SYSCLK_MEAS_CLK_PATH7 = 0x507U,
    CY_SYSCLK_MEAS_CLK_PATH8 = 0x508U,
    CY_SYSCLK_MEAS_CLK_PATH9 = 0x509U,
    CY_SYSCLK_MEAS_CLK_PATH10 = 0x50AU,
    CY_SYSCLK_MEAS_CLK_PATH11 = 0x50BU,
    CY_SYSCLK_MEAS_CLK_PATH12 = 0x50CU,
    CY_SYSCLK_MEAS_CLK_PATH13 = 0x50DU,
    CY_SYSCLK_MEAS_CLK_PATH14 = 0x50EU,
    CY_SYSCLK_MEAS_CLK_PATH15 = 0x50FU,
    CY_SYSCLK_MEAS_CLK_CLKHFS = 0x600U,
    CY_SYSCLK_MEAS_CLK_CLKHF0 = 0x600U,
    CY_SYSCLK_MEAS_CLK_CLKHF1 = 0x601U,
    CY_SYSCLK_MEAS_CLK_CLKHF2 = 0x602U,
    CY_SYSCLK_MEAS_CLK_CLKHF3 = 0x603U,
    CY_SYSCLK_MEAS_CLK_CLKHF4 = 0x604U,
    CY_SYSCLK_MEAS_CLK_CLKHF5 = 0x605U,
    CY_SYSCLK_MEAS_CLK_CLKHF6 = 0x606U,
    CY_SYSCLK_MEAS_CLK_CLKHF7 = 0x607U,
    CY_SYSCLK_MEAS_CLK_CLKHF8 = 0x608U,
    CY_SYSCLK_MEAS_CLK_CLKHF9 = 0x609U,
    CY_SYSCLK_MEAS_CLK_CLKHF10 = 0x60AU,
    CY_SYSCLK_MEAS_CLK_CLKHF11 = 0x60BU,
    CY_SYSCLK_MEAS_CLK_CLKHF12 = 0x60CU,
    CY_SYSCLK_MEAS_CLK_CLKHF13 = 0x60DU,
    CY_SYSCLK_MEAS_CLK_CLKHF14 = 0x60EU,
    CY_SYSCLK_MEAS_CLK_CLKHF15 = 0x60FU,
    CY_SYSCLK_MEAS_CLK_LAST_CLK = 0x610U
} cy_en_meas_clks_t;
cy_en_sysclk_status_t Cy_SysClk_StartClkMeasurementCounters(cy_en_meas_clks_t clock1, uint32_t count1, cy_en_meas_clks_t clock2);
uint32_t Cy_SysClk_ClkMeasurementCountersGetFreq(_Bool measuredClock, uint32_t refClkFreq);
_Bool Cy_SysClk_ClkMeasurementCountersDone(void);
int32_t Cy_SysClk_IloTrim(uint32_t iloFreq);
int32_t Cy_SysClk_PiloTrim(uint32_t piloFreq);
void Cy_SysClk_PiloInitialTrim(void);
void Cy_SysClk_PiloUpdateTrimStep(void);
cy_en_syspm_status_t Cy_SysClk_DeepSleepCallback(cy_stc_syspm_callback_params_t * callbackParams, cy_en_syspm_callback_mode_t mode);
typedef enum
{
    CY_SYSCLK_WCO_NOT_BYPASSED = 0U,
    CY_SYSCLK_WCO_BYPASSED = 1U
} cy_en_wco_bypass_modes_t;
typedef enum
{
    CY_SYSCLK_WCO_CSV_SUPERVISOR_ILO,
    CY_SYSCLK_WCO_CSV_SUPERVISOR_ALTLF,
    CY_SYSCLK_WCO_CSV_SUPERVISOR_PILO
} cy_en_wco_csv_supervisor_clock_t;
typedef enum
{
    CY_SYSCLK_CSV_LOSS_4_CYCLES = 0U,
    CY_SYSCLK_CSV_LOSS_8_CYCLES = 1U,
    CY_SYSCLK_CSV_LOSS_16_CYCLES = 2U,
    CY_SYSCLK_CSV_LOSS_32_CYCLES = 3U,
    CY_SYSCLK_CSV_LOSS_64_CYCLES = 4U,
    CY_SYSCLK_CSV_LOSS_128_CYCLES = 5U,
    CY_SYSCLK_CSV_LOSS_256_CYCLES = 6U,
    CY_SYSCLK_CSV_LOSS_512_CYCLES = 7U
} cy_en_csv_loss_window_t;
typedef enum
{
    CY_SYSCLK_CSV_ERROR_IGNORE = 0U,
    CY_SYSCLK_CSV_ERROR_FAULT = 1U,
    CY_SYSCLK_CSV_ERROR_RESET = 2U,
    CY_SYSCLK_CSV_ERROR_FAULT_RESET = 3U
} cy_en_csv_error_actions_t;
typedef struct
{
    cy_en_wco_csv_supervisor_clock_t supervisorClock;
    _Bool enableLossDetection;
    cy_en_csv_loss_window_t lossWindow;
    cy_en_csv_error_actions_t lossAction;
} cy_stc_wco_csv_config_t;
cy_en_sysclk_status_t Cy_SysClk_WcoEnable(uint32_t timeoutus);
_Bool Cy_SysClk_WcoOkay(void);
void Cy_SysClk_WcoDisable(void);
void Cy_SysClk_WcoBypass(cy_en_wco_bypass_modes_t bypass);
void Cy_SysClk_MfoEnable(_Bool deepSleepEnable);
_Bool Cy_SysClk_MfoIsEnabled(void);
void Cy_SysClk_MfoDisable(void);
void Cy_SysClk_ClkMfEnable(void);
_Bool Cy_SysClk_ClkMfIsEnabled(void);
void Cy_SysClk_ClkMfDisable(void);
void Cy_SysClk_ClkMfSetDivider(uint32_t divider);
uint32_t Cy_SysClk_ClkMfGetDivider(void);
uint32_t Cy_SysClk_ClkMfGetFrequency(void);
typedef enum
{
    CY_SYSCLK_CLKHF_IN_CLKPATH0 = 0U,
    CY_SYSCLK_CLKHF_IN_CLKPATH1 = 1U,
    CY_SYSCLK_CLKHF_IN_CLKPATH2 = 2U,
    CY_SYSCLK_CLKHF_IN_CLKPATH3 = 3U,
    CY_SYSCLK_CLKHF_IN_CLKPATH4 = 4U,
    CY_SYSCLK_CLKHF_IN_CLKPATH5 = 5U,
    CY_SYSCLK_CLKHF_IN_CLKPATH6 = 6U,
    CY_SYSCLK_CLKHF_IN_CLKPATH7 = 7U,
    CY_SYSCLK_CLKHF_IN_CLKPATH8 = 8U,
    CY_SYSCLK_CLKHF_IN_CLKPATH9 = 9U,
    CY_SYSCLK_CLKHF_IN_CLKPATH10 = 10U,
    CY_SYSCLK_CLKHF_IN_CLKPATH11 = 11U,
    CY_SYSCLK_CLKHF_IN_CLKPATH12 = 12U,
    CY_SYSCLK_CLKHF_IN_CLKPATH13 = 13U,
    CY_SYSCLK_CLKHF_IN_CLKPATH14 = 14U,
    CY_SYSCLK_CLKHF_IN_CLKPATH15 = 15U,
} cy_en_clkhf_in_sources_t;
typedef enum
{
    CY_SYSCLK_CLKHF_NO_DIVIDE = 0U,
    CY_SYSCLK_CLKHF_DIVIDE_BY_2 = 1U,
    CY_SYSCLK_CLKHF_DIVIDE_BY_4 = 2U,
    CY_SYSCLK_CLKHF_DIVIDE_BY_8 = 3U,
    CY_SYSCLK_CLKHF_MAX_DIVIDER
} cy_en_clkhf_dividers_t;
typedef enum
{
    CY_SYSCLK_CLKHF_CSV_SUPERVISOR_IMO = 0U,
    CY_SYSCLK_CLKHF_CSV_SUPERVISOR_EXT = 1U,
    CY_SYSCLK_CLKHF_CSV_SUPERVISOR_ALTHF = 2U
} cy_en_clkhf_csv_supervisor_clock_t;
typedef struct
{
    cy_en_clkhf_csv_supervisor_clock_t supervisorClock;
    uint16_t supervisingWindow;
    _Bool enableFrequencyFaultDetection;
    uint16_t frequencyLowerLimit;
    uint16_t frequencyUpperLimit;
    cy_en_csv_error_actions_t frequencyAction;
    _Bool enableLossDetection;
    cy_en_csv_loss_window_t lossWindow;
    cy_en_csv_error_actions_t lossAction;
} cy_stc_clkhf_csv_config_t;
cy_en_sysclk_status_t Cy_SysClk_ClkHfEnable(uint32_t clkHf);
_Bool Cy_SysClk_ClkHfIsEnabled(uint32_t clkHf);
cy_en_sysclk_status_t Cy_SysClk_ClkHfDisable(uint32_t clkHf);
cy_en_sysclk_status_t Cy_SysClk_ClkHfSetSource(uint32_t clkHf, cy_en_clkhf_in_sources_t source);
cy_en_clkhf_in_sources_t Cy_SysClk_ClkHfGetSource(uint32_t clkHf);
cy_en_sysclk_status_t Cy_SysClk_ClkHfSetDivider(uint32_t clkHf, cy_en_clkhf_dividers_t divider);
cy_en_clkhf_dividers_t Cy_SysClk_ClkHfGetDivider(uint32_t clkHf);
uint32_t Cy_SysClk_ClkHfGetFrequency(uint32_t clkHf);
void Cy_SysClk_ClkFastSetDivider(uint8_t divider);
uint8_t Cy_SysClk_ClkFastGetDivider(void);
uint32_t Cy_SysClk_ClkFastGetFrequency(void);
void Cy_SysClk_ClkPeriSetDivider(uint8_t divider);
uint32_t Cy_SysClk_ClkPeriGetFrequency(void);
uint8_t Cy_SysClk_ClkPeriGetDivider(void);
typedef enum
{
    CY_SYSCLK_DIV_8_BIT = 0U,
    CY_SYSCLK_DIV_16_BIT = 1U,
    CY_SYSCLK_DIV_16_5_BIT = 2U,
    CY_SYSCLK_DIV_24_5_BIT = 3U
} cy_en_divider_types_t;
cy_en_sysclk_status_t
                Cy_SysClk_PeriphSetDivider(cy_en_divider_types_t dividerType,
                                           uint32_t dividerNum, uint32_t dividerValue);
uint32_t Cy_SysClk_PeriphGetDivider(cy_en_divider_types_t dividerType, uint32_t dividerNum);
cy_en_sysclk_status_t
                Cy_SysClk_PeriphSetFracDivider(cy_en_divider_types_t dividerType, uint32_t dividerNum,
                                               uint32_t dividerIntValue, uint32_t dividerFracValue);
void Cy_SysClk_PeriphGetFracDivider(cy_en_divider_types_t dividerType, uint32_t dividerNum,
                                                    uint32_t *dividerIntValue, uint32_t *dividerFracValue);
cy_en_sysclk_status_t
                Cy_SysClk_PeriphAssignDivider(en_clk_dst_t ipBlock,
                                              cy_en_divider_types_t dividerType, uint32_t dividerNum);
uint32_t Cy_SysClk_PeriphGetAssignedDivider(en_clk_dst_t ipBlock);
cy_en_sysclk_status_t
                Cy_SysClk_PeriphEnableDivider(cy_en_divider_types_t dividerType, uint32_t dividerNum);
cy_en_sysclk_status_t
                Cy_SysClk_PeriphDisableDivider(cy_en_divider_types_t dividerType, uint32_t dividerNum);
cy_en_sysclk_status_t
                Cy_SysClk_PeriphEnablePhaseAlignDivider(cy_en_divider_types_t dividerType, uint32_t dividerNum,
                                                        cy_en_divider_types_t dividerTypePA, uint32_t dividerNumPA);
_Bool Cy_SysClk_PeriphGetDividerEnabled(cy_en_divider_types_t dividerType, uint32_t dividerNum);
uint32_t Cy_SysClk_PeriphGetFrequency(cy_en_divider_types_t dividerType, uint32_t dividerNum);
void Cy_SysClk_ClkSlowSetDivider(uint8_t divider);
uint8_t Cy_SysClk_ClkSlowGetDivider(void);
uint32_t Cy_SysClk_ClkSlowGetFrequency(void);
typedef enum
{
    CY_SYSCLK_CLKLF_IN_ILO = 0U,
    CY_SYSCLK_CLKLF_IN_WCO = 1U,
    CY_SYSCLK_CLKLF_IN_ALTLF = 2U,
    CY_SYSCLK_CLKLF_IN_PILO = 3U,
    CY_SYSCLK_CLKLF_IN_ILO1 = 4U,
    CY_SYSCLK_CLKLF_IN_ECO_PRESCALER = 5U,
    CY_SYSCLK_CLKLF_IN_LPECO_PRESCALER = 6U,
    CY_SYSCLK_CLKLF_IN_MAX = 7U
} cy_en_clklf_in_sources_t;
void Cy_SysClk_ClkLfSetSource(cy_en_clklf_in_sources_t source);
cy_en_clklf_in_sources_t Cy_SysClk_ClkLfGetSource(void);
typedef enum
{
    CY_SYSCLK_CLKTIMER_IN_IMO = 0x000U,
    CY_SYSCLK_CLKTIMER_IN_HF0_NODIV = 0x001U,
    CY_SYSCLK_CLKTIMER_IN_HF0_DIV2 = 0x101U,
    CY_SYSCLK_CLKTIMER_IN_HF0_DIV4 = 0x201U,
    CY_SYSCLK_CLKTIMER_IN_HF0_DIV8 = 0x301U
} cy_en_clktimer_in_sources_t;
void Cy_SysClk_ClkTimerSetSource(cy_en_clktimer_in_sources_t source);
cy_en_clktimer_in_sources_t Cy_SysClk_ClkTimerGetSource(void);
void Cy_SysClk_ClkTimerSetDivider(uint8_t divider);
uint8_t Cy_SysClk_ClkTimerGetDivider(void);
void Cy_SysClk_ClkTimerEnable(void);
void Cy_SysClk_ClkTimerDisable(void);
_Bool Cy_SysClk_ClkTimerIsEnabled(void);
uint32_t Cy_SysClk_ClkTimerGetFrequency(void);
typedef enum
{
    CY_SYSCLK_PUMP_IN_CLKPATH0 = 0UL,
    CY_SYSCLK_PUMP_IN_CLKPATH1 = 1UL,
    CY_SYSCLK_PUMP_IN_CLKPATH2 = 2UL,
    CY_SYSCLK_PUMP_IN_CLKPATH3 = 3UL,
    CY_SYSCLK_PUMP_IN_CLKPATH4 = 4UL,
    CY_SYSCLK_PUMP_IN_CLKPATH5 = 5UL,
    CY_SYSCLK_PUMP_IN_CLKPATH6 = 6UL,
    CY_SYSCLK_PUMP_IN_CLKPATH7 = 7UL,
    CY_SYSCLK_PUMP_IN_CLKPATH8 = 8UL,
    CY_SYSCLK_PUMP_IN_CLKPATH9 = 9UL,
    CY_SYSCLK_PUMP_IN_CLKPATH10 = 10UL,
    CY_SYSCLK_PUMP_IN_CLKPATH11 = 11UL,
    CY_SYSCLK_PUMP_IN_CLKPATH12 = 12UL,
    CY_SYSCLK_PUMP_IN_CLKPATH13 = 13UL,
    CY_SYSCLK_PUMP_IN_CLKPATH14 = 14UL,
    CY_SYSCLK_PUMP_IN_CLKPATH15 = 15UL
} cy_en_clkpump_in_sources_t;
typedef enum
{
    CY_SYSCLK_PUMP_NO_DIV = 0U,
    CY_SYSCLK_PUMP_DIV_2 = 1U,
    CY_SYSCLK_PUMP_DIV_4 = 2U,
    CY_SYSCLK_PUMP_DIV_8 = 3U,
    CY_SYSCLK_PUMP_DIV_16 = 4U
} cy_en_clkpump_divide_t;
void Cy_SysClk_ClkPumpSetSource(cy_en_clkpump_in_sources_t source);
cy_en_clkpump_in_sources_t Cy_SysClk_ClkPumpGetSource(void);
void Cy_SysClk_ClkPumpSetDivider(cy_en_clkpump_divide_t divider);
cy_en_clkpump_divide_t Cy_SysClk_ClkPumpGetDivider(void);
void Cy_SysClk_ClkPumpEnable(void);
_Bool Cy_SysClk_ClkPumpIsEnabled(void);
void Cy_SysClk_ClkPumpDisable(void);
uint32_t Cy_SysClk_ClkPumpGetFrequency(void);
typedef enum
{
    CY_SYSCLK_BAK_IN_WCO,
    CY_SYSCLK_BAK_IN_CLKLF,
} cy_en_clkbak_in_sources_t;
void Cy_SysClk_ClkBakSetSource(cy_en_clkbak_in_sources_t source);
cy_en_clkbak_in_sources_t Cy_SysClk_ClkBakGetSource(void);

typedef enum {
    CY_CTDAC_UPDATE_DIRECT_WRITE = 0uL,
    CY_CTDAC_UPDATE_BUFFERED_WRITE = 1uL,
    CY_CTDAC_UPDATE_STROBE_EDGE_SYNC = 2uL,
    CY_CTDAC_UPDATE_STROBE_EDGE_IMMEDIATE = 3uL,
    CY_CTDAC_UPDATE_STROBE_LEVEL = 4uL
}cy_en_ctdac_update_t;
typedef enum {
    CY_CTDAC_FORMAT_UNSIGNED = 0uL,
    CY_CTDAC_FORMAT_SIGNED = 1uL << 24UL
}cy_en_ctdac_format_t;
typedef enum {
    CY_CTDAC_DEEPSLEEP_DISABLE = 0uL,
    CY_CTDAC_DEEPSLEEP_ENABLE = 0x40000000UL
}cy_en_ctdac_deep_sleep_t;
typedef enum {
    CY_CTDAC_OUTPUT_HIGHZ = 0uL,
    CY_CTDAC_OUTPUT_VALUE = 0x400000UL,
    CY_CTDAC_OUTPUT_VALUE_PLUS1 = 0x400000UL | 0x800000UL,
    CY_CTDAC_OUTPUT_VSSA = 0x8000000UL,
    CY_CTDAC_OUTPUT_VREF = 0x8000000UL | 0x800000UL
}cy_en_ctdac_output_mode_t;
typedef enum {
    CY_CTDAC_DEGLITCHMODE_NONE = 0uL,
    CY_CTDAC_DEGLITCHMODE_UNBUFFERED = 0x100UL,
    CY_CTDAC_DEGLITCHMODE_BUFFERED = 0x200UL,
    CY_CTDAC_DEGLITCHMODE_BOTH = 0x200UL | 0x100UL
}cy_en_ctdac_deglitch_t;
typedef enum {
    CY_CTDAC_REFSOURCE_EXTERNAL = 0uL,
    CY_CTDAC_REFSOURCE_VDDA = 1uL
}cy_en_ctdac_ref_source_t;
typedef enum {
    CY_CTDAC_OUTPUT_BUFFERED = 0uL,
    CY_CTDAC_OUTPUT_UNBUFFERED = 1uL
}cy_en_ctdac_output_buffer_t;
typedef enum
{
    CY_CTDAC_SWITCH_OPEN = 0uL,
    CY_CTDAC_SWITCH_CLOSE = 1uL
}cy_en_ctdac_switch_state_t;
typedef enum
{
    CY_CTDAC_SWITCH_CVD_MASK = 0x1UL,
    CY_CTDAC_SWITCH_CO6_MASK = 0x100UL
}cy_en_ctdac_switches_t;
typedef enum {
    CY_CTDAC_SUCCESS = 0x00uL,
    CY_CTDAC_BAD_PARAM = ((uint32_t)((uint32_t)((0x19u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01uL
}cy_en_ctdac_status_t;
typedef struct
{
    cy_en_ctdac_ref_source_t refSource;
    cy_en_ctdac_format_t formatMode;
    cy_en_ctdac_update_t updateMode;
    cy_en_ctdac_deglitch_t deglitchMode;
    cy_en_ctdac_output_mode_t outputMode;
    cy_en_ctdac_output_buffer_t outputBuffer;
    cy_en_ctdac_deep_sleep_t deepSleep;
    uint32_t deglitchCycles;
    int32_t value;
    int32_t nextValue;
    _Bool enableInterrupt;
    _Bool configClock;
    cy_en_divider_types_t dividerType;
    uint32_t dividerNum;
    uint32_t dividerIntValue;
    uint32_t dividerFracValue;
}cy_stc_ctdac_config_t;
typedef struct
{
    cy_en_ctdac_ref_source_t refSource;
    cy_en_ctdac_output_buffer_t outputBuffer;
}cy_stc_ctdac_fast_config_t;
typedef struct
{
    uint32_t deglitchModeBeforeSleep;
}cy_stc_ctdac_context_t;
extern const cy_stc_ctdac_fast_config_t Cy_CTDAC_Fast_VddaRef_UnbufferedOut;
extern const cy_stc_ctdac_fast_config_t Cy_CTDAC_Fast_VddaRef_BufferedOut;
extern const cy_stc_ctdac_fast_config_t Cy_CTDAC_Fast_OA1Ref_UnbufferedOut;
extern const cy_stc_ctdac_fast_config_t Cy_CTDAC_Fast_OA1Ref_BufferedOut;
cy_en_ctdac_status_t Cy_CTDAC_Init(CTDAC_Type *base, const cy_stc_ctdac_config_t *config);
cy_en_ctdac_status_t Cy_CTDAC_DeInit(CTDAC_Type *base, _Bool deInitRouting);
cy_en_ctdac_status_t Cy_CTDAC_FastInit(CTDAC_Type *base, const cy_stc_ctdac_fast_config_t *config);
static inline void Cy_CTDAC_Enable(CTDAC_Type *base);
static inline void Cy_CTDAC_Disable(CTDAC_Type *base);
static inline void Cy_CTDAC_SetValue(CTDAC_Type *base, int32_t value);
static inline void Cy_CTDAC_SetValueBuffered(CTDAC_Type *base, int32_t value);
void Cy_CTDAC_SetSignMode(CTDAC_Type *base, cy_en_ctdac_format_t formatMode);
void Cy_CTDAC_SetDeepSleepMode(CTDAC_Type *base, cy_en_ctdac_deep_sleep_t deepSleep);
void Cy_CTDAC_SetOutputMode(CTDAC_Type *base, cy_en_ctdac_output_mode_t outputMode);
void Cy_CTDAC_SetDeglitchMode(CTDAC_Type *base, cy_en_ctdac_deglitch_t deglitchMode);
void Cy_CTDAC_SetDeglitchCycles(CTDAC_Type *base, uint32_t deglitchCycles);
void Cy_CTDAC_SetRef(CTDAC_Type *base, cy_en_ctdac_ref_source_t refSource);
void Cy_CTDAC_SetAnalogSwitch(CTDAC_Type *base, uint32_t switchMask, cy_en_ctdac_switch_state_t state);
static inline uint32_t Cy_CTDAC_GetAnalogSwitch(const CTDAC_Type *base);
static inline void Cy_CTDAC_SetSwitchCO6(CTDAC_Type *base, cy_en_ctdac_switch_state_t state);
static inline void Cy_CTDAC_OpenAllSwitches(CTDAC_Type *base);
static inline uint32_t Cy_CTDAC_GetInterruptStatus(const CTDAC_Type *base);
static inline void Cy_CTDAC_ClearInterrupt(CTDAC_Type *base);
static inline void Cy_CTDAC_SetInterrupt(CTDAC_Type *base);
static inline void Cy_CTDAC_SetInterruptMask(CTDAC_Type *base, uint32_t mask);
static inline uint32_t Cy_CTDAC_GetInterruptMask(const CTDAC_Type *base);
static inline uint32_t Cy_CTDAC_GetInterruptStatusMasked(const CTDAC_Type *base);
cy_en_syspm_status_t Cy_CTDAC_DeepSleepCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
static inline void Cy_CTDAC_Enable(CTDAC_Type *base)
{
    (((CTDAC_V1_Type *) (base))->CTDAC_CTRL) |= 0x80000000UL;
}
static inline void Cy_CTDAC_Disable(CTDAC_Type *base)
{
    (((CTDAC_V1_Type *) (base))->CTDAC_CTRL) &= ~0x80000000UL;
}
static inline void Cy_CTDAC_SetValue(CTDAC_Type *base, int32_t value)
{
    (((CTDAC_V1_Type *) (base))->CTDAC_VAL) = (((uint32_t)value) << 0UL) & 0xFFFUL;
}
static inline void Cy_CTDAC_SetValueBuffered(CTDAC_Type *base, int32_t value)
{
    (((CTDAC_V1_Type *) (base))->CTDAC_VAL_NXT) = (((uint32_t)value) << 0UL) & 0xFFFUL;
}
static inline uint32_t Cy_CTDAC_GetAnalogSwitch(const CTDAC_Type *base)
{
    return (((CTDAC_V1_Type *) (base))->CTDAC_SW);
}
static inline void Cy_CTDAC_SetSwitchCO6(CTDAC_Type *base, cy_en_ctdac_switch_state_t state)
{
    Cy_CTDAC_SetAnalogSwitch(base, (uint32_t) CY_CTDAC_SWITCH_CO6_MASK, state);
}
static inline void Cy_CTDAC_OpenAllSwitches(CTDAC_Type *base)
{
    (((CTDAC_V1_Type *) (base))->CTDAC_SW_CLEAR) = (0x1UL | 0x100UL);
}
static inline uint32_t Cy_CTDAC_GetInterruptStatus(const CTDAC_Type *base)
{
    return ((((CTDAC_V1_Type *) (base))->INTR) & 0x1UL) >> 0UL;
}
static inline void Cy_CTDAC_ClearInterrupt(CTDAC_Type *base)
{
    (((CTDAC_V1_Type *) (base))->INTR) = 0x1UL;
    (void) (((CTDAC_V1_Type *) (base))->INTR);
}
static inline void Cy_CTDAC_SetInterrupt(CTDAC_Type *base)
{
    (((CTDAC_V1_Type *) (base))->INTR_SET) = 0x1UL;
}
static inline void Cy_CTDAC_SetInterruptMask(CTDAC_Type *base, uint32_t mask)
{
    do { if(!((((mask) == 0uL) || ((mask) == 1uL)))) { CY_HALT(); } } while (0);
    (((CTDAC_V1_Type *) (base))->INTR_MASK) = mask & 0x1UL;
}
static inline uint32_t Cy_CTDAC_GetInterruptMask(const CTDAC_Type *base)
{
    return ((((CTDAC_V1_Type *) (base))->INTR_MASK) & 0x1UL) >> 0UL;
}
static inline uint32_t Cy_CTDAC_GetInterruptStatusMasked(const CTDAC_Type *base){
    return ((((CTDAC_V1_Type *) (base))->INTR_MASKED) & 0x1UL) >> 0UL;
}


typedef enum
{
    CY_DMA_INTR_CAUSE_NO_INTR = 0U,
    CY_DMA_INTR_CAUSE_COMPLETION = 1U,
    CY_DMA_INTR_CAUSE_SRC_BUS_ERROR = 2U,
    CY_DMA_INTR_CAUSE_DST_BUS_ERROR = 3U,
    CY_DMA_INTR_CAUSE_SRC_MISAL = 4U,
    CY_DMA_INTR_CAUSE_DST_MISAL = 5U,
    CY_DMA_INTR_CAUSE_CURR_PTR_NULL = 6U,
    CY_DMA_INTR_CAUSE_ACTIVE_CH_DISABLED = 7U,
    CY_DMA_INTR_CAUSE_DESCR_BUS_ERROR = 8U
} cy_en_dma_intr_cause_t;
typedef enum
{
    CY_DMA_SINGLE_TRANSFER = 0UL,
    CY_DMA_1D_TRANSFER = 1UL,
    CY_DMA_2D_TRANSFER = 2UL,
    CY_DMA_CRC_TRANSFER = 3UL,
} cy_en_dma_descriptor_type_t;
typedef enum
{
    CY_DMA_1ELEMENT = 0UL,
    CY_DMA_X_LOOP = 1UL,
    CY_DMA_DESCR = 2UL,
    CY_DMA_DESCR_CHAIN = 3UL
} cy_en_dma_trigger_type_t;
typedef enum
{
    CY_DMA_BYTE = 0UL,
    CY_DMA_HALFWORD = 1UL,
    CY_DMA_WORD = 2UL
} cy_en_dma_data_size_t;
typedef enum
{
    CY_DMA_RETRIG_IM = 0UL,
    CY_DMA_RETRIG_4CYC = 1UL,
    CY_DMA_RETRIG_16CYC = 2UL,
    CY_DMA_WAIT_FOR_REACT = 3UL
} cy_en_dma_retrigger_t;
typedef enum
{
    CY_DMA_TRANSFER_SIZE_DATA = 0UL,
    CY_DMA_TRANSFER_SIZE_WORD = 1UL,
} cy_en_dma_transfer_size_t;
typedef enum
{
    CY_DMA_CHANNEL_ENABLED = 0UL,
    CY_DMA_CHANNEL_DISABLED = 1UL
} cy_en_dma_channel_state_t;
typedef enum
{
    CY_DMA_SUCCESS = 0x00UL,
    CY_DMA_BAD_PARAM = (((uint32_t)((uint32_t)((0x13U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01UL
} cy_en_dma_status_t;
typedef struct
{
    uint32_t ctl;
    uint32_t src;
    uint32_t dst;
    uint32_t xCtl;
    uint32_t yCtl;
    uint32_t nextPtr;
} cy_stc_dma_descriptor_t;
typedef struct
{
    cy_en_dma_retrigger_t retrigger;
    cy_en_dma_trigger_type_t interruptType;
    cy_en_dma_trigger_type_t triggerOutType;
    cy_en_dma_channel_state_t channelState;
    cy_en_dma_trigger_type_t triggerInType;
    cy_en_dma_data_size_t dataSize;
    cy_en_dma_transfer_size_t srcTransferSize;
    cy_en_dma_transfer_size_t dstTransferSize;
    cy_en_dma_descriptor_type_t descriptorType;
    void * srcAddress;
    void * dstAddress;
    int32_t srcXincrement;
    int32_t dstXincrement;
    uint32_t xCount;
    int32_t srcYincrement;
    int32_t dstYincrement;
    uint32_t yCount;
    cy_stc_dma_descriptor_t * nextDescriptor;
} cy_stc_dma_descriptor_config_t;
typedef struct
{
    cy_stc_dma_descriptor_t * descriptor;
    _Bool preemptable;
    uint32_t priority;
    _Bool enable;
    _Bool bufferable;
} cy_stc_dma_channel_config_t;
typedef struct
{
    _Bool dataReverse;
    uint32_t dataXor;
    _Bool reminderReverse;
    uint32_t reminderXor;
    uint32_t polynomial;
    uint32_t lfsrInitVal;
} cy_stc_dma_crc_config_t;
static inline void Cy_DMA_Enable (DW_Type * base);
static inline void Cy_DMA_Disable (DW_Type * base);
static inline uint32_t Cy_DMA_GetActiveChannel (DW_Type const * base);
static inline void * Cy_DMA_GetActiveSrcAddress(DW_Type const * base);
static inline void * Cy_DMA_GetActiveDstAddress(DW_Type const * base);
      cy_en_dma_status_t Cy_DMA_Crc_Init (DW_Type * base, cy_stc_dma_crc_config_t const * crcConfig);
      cy_en_dma_status_t Cy_DMA_Channel_Init (DW_Type * base, uint32_t channel, cy_stc_dma_channel_config_t const * channelConfig);
                void Cy_DMA_Channel_DeInit (DW_Type * base, uint32_t channel);
static inline void Cy_DMA_Channel_SetDescriptor (DW_Type * base, uint32_t channel, cy_stc_dma_descriptor_t const * descriptor);
static inline void Cy_DMA_Channel_Enable (DW_Type * base, uint32_t channel);
static inline void Cy_DMA_Channel_Disable (DW_Type * base, uint32_t channel);
static inline void Cy_DMA_Channel_SetPriority (DW_Type * base, uint32_t channel, uint32_t priority);
static inline uint32_t Cy_DMA_Channel_GetPriority (DW_Type const * base, uint32_t channel);
static inline
  cy_en_dma_intr_cause_t Cy_DMA_Channel_GetStatus (DW_Type const * base, uint32_t channel);
static inline
cy_stc_dma_descriptor_t * Cy_DMA_Channel_GetCurrentDescriptor (DW_Type const * base, uint32_t channel);
static inline uint32_t Cy_DMA_Channel_GetInterruptStatus (DW_Type const * base, uint32_t channel);
static inline void Cy_DMA_Channel_ClearInterrupt (DW_Type * base, uint32_t channel);
static inline void Cy_DMA_Channel_SetInterrupt (DW_Type * base, uint32_t channel);
static inline uint32_t Cy_DMA_Channel_GetInterruptMask (DW_Type const * base, uint32_t channel);
static inline void Cy_DMA_Channel_SetInterruptMask (DW_Type * base, uint32_t channel, uint32_t interrupt);
static inline uint32_t Cy_DMA_Channel_GetInterruptStatusMasked(DW_Type const * base, uint32_t channel);
  cy_en_dma_status_t Cy_DMA_Descriptor_Init (cy_stc_dma_descriptor_t * descriptor, cy_stc_dma_descriptor_config_t const * config);
                void Cy_DMA_Descriptor_DeInit(cy_stc_dma_descriptor_t * descriptor);
                void Cy_DMA_Descriptor_SetNextDescriptor (cy_stc_dma_descriptor_t * descriptor, cy_stc_dma_descriptor_t const * nextDescriptor);
                void Cy_DMA_Descriptor_SetDescriptorType (cy_stc_dma_descriptor_t * descriptor, cy_en_dma_descriptor_type_t descriptorType);
static inline void Cy_DMA_Descriptor_SetSrcAddress (cy_stc_dma_descriptor_t * descriptor, void const * srcAddress);
static inline void Cy_DMA_Descriptor_SetDstAddress (cy_stc_dma_descriptor_t * descriptor, void const * dstAddress);
static inline void Cy_DMA_Descriptor_SetXloopDataCount (cy_stc_dma_descriptor_t * descriptor, uint32_t xCount);
static inline void Cy_DMA_Descriptor_SetYloopDataCount (cy_stc_dma_descriptor_t * descriptor, uint32_t yCount);
static inline void Cy_DMA_Descriptor_SetXloopSrcIncrement(cy_stc_dma_descriptor_t * descriptor, int32_t srcXincrement);
static inline void Cy_DMA_Descriptor_SetXloopDstIncrement(cy_stc_dma_descriptor_t * descriptor, int32_t dstXincrement);
static inline void Cy_DMA_Descriptor_SetYloopSrcIncrement(cy_stc_dma_descriptor_t * descriptor, int32_t srcYincrement);
static inline void Cy_DMA_Descriptor_SetYloopDstIncrement(cy_stc_dma_descriptor_t * descriptor, int32_t dstYincrement);
static inline void Cy_DMA_Descriptor_SetInterruptType (cy_stc_dma_descriptor_t * descriptor, cy_en_dma_trigger_type_t interruptType);
static inline void Cy_DMA_Descriptor_SetTriggerInType (cy_stc_dma_descriptor_t * descriptor, cy_en_dma_trigger_type_t triggerInType);
static inline void Cy_DMA_Descriptor_SetTriggerOutType (cy_stc_dma_descriptor_t * descriptor, cy_en_dma_trigger_type_t triggerOutType);
static inline void Cy_DMA_Descriptor_SetDataSize (cy_stc_dma_descriptor_t * descriptor, cy_en_dma_data_size_t dataSize);
static inline void Cy_DMA_Descriptor_SetSrcTransferSize (cy_stc_dma_descriptor_t * descriptor, cy_en_dma_transfer_size_t srcTransferSize);
static inline void Cy_DMA_Descriptor_SetDstTransferSize (cy_stc_dma_descriptor_t * descriptor, cy_en_dma_transfer_size_t dstTransferSize);
static inline void Cy_DMA_Descriptor_SetRetrigger (cy_stc_dma_descriptor_t * descriptor, cy_en_dma_retrigger_t retrigger);
static inline void Cy_DMA_Descriptor_SetChannelState (cy_stc_dma_descriptor_t * descriptor, cy_en_dma_channel_state_t channelState);
                cy_stc_dma_descriptor_t * Cy_DMA_Descriptor_GetNextDescriptor (cy_stc_dma_descriptor_t const * descriptor);
static inline cy_en_dma_descriptor_type_t Cy_DMA_Descriptor_GetDescriptorType (cy_stc_dma_descriptor_t const * descriptor);
static inline void * Cy_DMA_Descriptor_GetSrcAddress (cy_stc_dma_descriptor_t const * descriptor);
static inline void * Cy_DMA_Descriptor_GetDstAddress (cy_stc_dma_descriptor_t const * descriptor);
static inline uint32_t Cy_DMA_Descriptor_GetXloopDataCount (cy_stc_dma_descriptor_t const * descriptor);
static inline uint32_t Cy_DMA_Descriptor_GetYloopDataCount (cy_stc_dma_descriptor_t const * descriptor);
static inline int32_t Cy_DMA_Descriptor_GetXloopSrcIncrement(cy_stc_dma_descriptor_t const * descriptor);
static inline int32_t Cy_DMA_Descriptor_GetXloopDstIncrement(cy_stc_dma_descriptor_t const * descriptor);
static inline int32_t Cy_DMA_Descriptor_GetYloopSrcIncrement(cy_stc_dma_descriptor_t const * descriptor);
static inline int32_t Cy_DMA_Descriptor_GetYloopDstIncrement(cy_stc_dma_descriptor_t const * descriptor);
static inline cy_en_dma_trigger_type_t Cy_DMA_Descriptor_GetInterruptType (cy_stc_dma_descriptor_t const * descriptor);
static inline cy_en_dma_trigger_type_t Cy_DMA_Descriptor_GetTriggerInType (cy_stc_dma_descriptor_t const * descriptor);
static inline cy_en_dma_trigger_type_t Cy_DMA_Descriptor_GetTriggerOutType (cy_stc_dma_descriptor_t const * descriptor);
static inline cy_en_dma_data_size_t Cy_DMA_Descriptor_GetDataSize (cy_stc_dma_descriptor_t const * descriptor);
static inline cy_en_dma_transfer_size_t Cy_DMA_Descriptor_GetSrcTransferSize (cy_stc_dma_descriptor_t const * descriptor);
static inline cy_en_dma_transfer_size_t Cy_DMA_Descriptor_GetDstTransferSize (cy_stc_dma_descriptor_t const * descriptor);
static inline cy_en_dma_retrigger_t Cy_DMA_Descriptor_GetRetrigger (cy_stc_dma_descriptor_t const * descriptor);
static inline cy_en_dma_channel_state_t Cy_DMA_Descriptor_GetChannelState (cy_stc_dma_descriptor_t const * descriptor);
static inline void Cy_DMA_Enable(DW_Type * base)
{
    (((DW_Type*)(base))->CTL) |= 0x80000000UL;
}
static inline void Cy_DMA_Disable(DW_Type * base)
{
    (((DW_Type*)(base))->CTL) &= (uint32_t) ~0x80000000UL;
}
static inline uint32_t Cy_DMA_GetActiveChannel(DW_Type const * base)
{
        return ((((DW_Type*)(base))->PENDING));
}
static inline uint32_t Cy_DMA_GetActiveChannelIndex(DW_Type const * base)
{
    if ((((uint32_t)((((DW_Type const*)(base))->STATUS)) & 0x80000000UL) >> 31UL) == 1U)
    {
        return((((uint32_t)((((DW_Type const*)(base))->STATUS)) & (cy_device->dwStatusChIdxMsk)) >> ((uint32_t)(cy_device->dwStatusChIdxPos))));
    }
    else
    {
        return (0xFFFFFFFFU);
    }
}
static inline void * Cy_DMA_GetActiveSrcAddress(DW_Type const * base)
{
    return ((void *) (((DW_Type*)(base))->ACT_DESCR_SRC));
}
static inline void * Cy_DMA_GetActiveDstAddress(DW_Type const * base)
{
    return ((void *) (((DW_Type*)(base))->ACT_DESCR_DST));
}
static inline void Cy_DMA_Descriptor_SetSrcAddress(cy_stc_dma_descriptor_t * descriptor, void const * srcAddress)
{
    descriptor->src = (uint32_t) srcAddress;
}
static inline void * Cy_DMA_Descriptor_GetSrcAddress(cy_stc_dma_descriptor_t const * descriptor)
{
    return ((void *) descriptor->src);
}
static inline void Cy_DMA_Descriptor_SetDstAddress(cy_stc_dma_descriptor_t * descriptor, void const * dstAddress)
{
    descriptor->dst = (uint32_t) dstAddress;
}
static inline void * Cy_DMA_Descriptor_GetDstAddress(cy_stc_dma_descriptor_t const * descriptor)
{
    return ((void *) descriptor->dst);
}
static inline void Cy_DMA_Descriptor_SetInterruptType(cy_stc_dma_descriptor_t * descriptor, cy_en_dma_trigger_type_t interruptType)
{
    do { if(!(((CY_DMA_1ELEMENT == (interruptType)) || (CY_DMA_X_LOOP == (interruptType)) || (CY_DMA_DESCR == (interruptType)) || (CY_DMA_DESCR_CHAIN == (interruptType))))) { CY_HALT(); } } while (0);
    ((descriptor->ctl) = ((((descriptor->ctl)) & ((uint32_t)(~(((uint32_t)0x3UL << (2UL)))))) | ((((uint32_t)((interruptType)) << (2UL)) & ((uint32_t)0x3UL << (2UL))))));
}
static inline cy_en_dma_trigger_type_t Cy_DMA_Descriptor_GetInterruptType(cy_stc_dma_descriptor_t const * descriptor)
{
    return((cy_en_dma_trigger_type_t) (((uint32_t)(descriptor->ctl) & ((uint32_t)0x3UL << (2UL))) >> (2UL)));
}
static inline void Cy_DMA_Descriptor_SetTriggerInType(cy_stc_dma_descriptor_t * descriptor, cy_en_dma_trigger_type_t triggerInType)
{
    do { if(!(((CY_DMA_1ELEMENT == (triggerInType)) || (CY_DMA_X_LOOP == (triggerInType)) || (CY_DMA_DESCR == (triggerInType)) || (CY_DMA_DESCR_CHAIN == (triggerInType))))) { CY_HALT(); } } while (0);
    ((descriptor->ctl) = ((((descriptor->ctl)) & ((uint32_t)(~(((uint32_t)0x3UL << (6UL)))))) | ((((uint32_t)((triggerInType)) << (6UL)) & ((uint32_t)0x3UL << (6UL))))));
}
static inline cy_en_dma_trigger_type_t Cy_DMA_Descriptor_GetTriggerInType(cy_stc_dma_descriptor_t const * descriptor)
{
    return((cy_en_dma_trigger_type_t) (((uint32_t)(descriptor->ctl) & ((uint32_t)0x3UL << (6UL))) >> (6UL)));
}
static inline void Cy_DMA_Descriptor_SetTriggerOutType(cy_stc_dma_descriptor_t * descriptor, cy_en_dma_trigger_type_t triggerOutType)
{
    do { if(!(((CY_DMA_1ELEMENT == (triggerOutType)) || (CY_DMA_X_LOOP == (triggerOutType)) || (CY_DMA_DESCR == (triggerOutType)) || (CY_DMA_DESCR_CHAIN == (triggerOutType))))) { CY_HALT(); } } while (0);
    ((descriptor->ctl) = ((((descriptor->ctl)) & ((uint32_t)(~(((uint32_t)0x3UL << (4UL)))))) | ((((uint32_t)((triggerOutType)) << (4UL)) & ((uint32_t)0x3UL << (4UL))))));
}
static inline cy_en_dma_trigger_type_t Cy_DMA_Descriptor_GetTriggerOutType(cy_stc_dma_descriptor_t const * descriptor)
{
    return((cy_en_dma_trigger_type_t) (((uint32_t)(descriptor->ctl) & ((uint32_t)0x3UL << (4UL))) >> (4UL)));
}
static inline void Cy_DMA_Descriptor_SetDataSize(cy_stc_dma_descriptor_t * descriptor, cy_en_dma_data_size_t dataSize)
{
    do { if(!(((CY_DMA_BYTE == (dataSize)) || (CY_DMA_HALFWORD == (dataSize)) || (CY_DMA_WORD == (dataSize))))) { CY_HALT(); } } while (0);
    ((descriptor->ctl) = ((((descriptor->ctl)) & ((uint32_t)(~(((uint32_t)0x3UL << (28UL)))))) | ((((uint32_t)((dataSize)) << (28UL)) & ((uint32_t)0x3UL << (28UL))))));
}
static inline cy_en_dma_data_size_t Cy_DMA_Descriptor_GetDataSize(cy_stc_dma_descriptor_t const * descriptor)
{
    return((cy_en_dma_data_size_t) (((uint32_t)(descriptor->ctl) & ((uint32_t)0x3UL << (28UL))) >> (28UL)));
}
static inline void Cy_DMA_Descriptor_SetSrcTransferSize(cy_stc_dma_descriptor_t * descriptor, cy_en_dma_transfer_size_t srcTransferSize)
{
    do { if(!(((CY_DMA_TRANSFER_SIZE_DATA == (srcTransferSize)) || (CY_DMA_TRANSFER_SIZE_WORD == (srcTransferSize))))) { CY_HALT(); } } while (0);
    ((descriptor->ctl) = ((((descriptor->ctl)) & ((uint32_t)(~(((uint32_t)0x1UL << (26UL)))))) | ((((uint32_t)((srcTransferSize)) << (26UL)) & ((uint32_t)0x1UL << (26UL))))));
}
static inline cy_en_dma_transfer_size_t Cy_DMA_Descriptor_GetSrcTransferSize(cy_stc_dma_descriptor_t const * descriptor)
{
    return((cy_en_dma_transfer_size_t) (((uint32_t)(descriptor->ctl) & ((uint32_t)0x1UL << (26UL))) >> (26UL)));
}
static inline void Cy_DMA_Descriptor_SetDstTransferSize(cy_stc_dma_descriptor_t * descriptor, cy_en_dma_transfer_size_t dstTransferSize)
{
    do { if(!(((CY_DMA_TRANSFER_SIZE_DATA == (dstTransferSize)) || (CY_DMA_TRANSFER_SIZE_WORD == (dstTransferSize))))) { CY_HALT(); } } while (0);
    ((descriptor->ctl) = ((((descriptor->ctl)) & ((uint32_t)(~(((uint32_t)0x1UL << (27UL)))))) | ((((uint32_t)((dstTransferSize)) << (27UL)) & ((uint32_t)0x1UL << (27UL))))));
}
static inline cy_en_dma_transfer_size_t Cy_DMA_Descriptor_GetDstTransferSize(cy_stc_dma_descriptor_t const * descriptor)
{
    return((cy_en_dma_transfer_size_t) (((uint32_t)(descriptor->ctl) & ((uint32_t)0x1UL << (27UL))) >> (27UL)));
}
static inline void Cy_DMA_Descriptor_SetRetrigger(cy_stc_dma_descriptor_t * descriptor, cy_en_dma_retrigger_t retrigger)
{
    do { if(!(((CY_DMA_RETRIG_IM == (retrigger)) || (CY_DMA_RETRIG_4CYC == (retrigger)) || (CY_DMA_RETRIG_16CYC == (retrigger)) || (CY_DMA_WAIT_FOR_REACT == (retrigger))))) { CY_HALT(); } } while (0);
    ((descriptor->ctl) = ((((descriptor->ctl)) & ((uint32_t)(~(((uint32_t)0x3UL << (0UL)))))) | ((((uint32_t)((retrigger)) << (0UL)) & ((uint32_t)0x3UL << (0UL))))));
}
static inline cy_en_dma_retrigger_t Cy_DMA_Descriptor_GetRetrigger(cy_stc_dma_descriptor_t const * descriptor)
{
    return((cy_en_dma_retrigger_t) (((uint32_t)(descriptor->ctl) & ((uint32_t)0x3UL << (0UL))) >> (0UL)));
}
static inline cy_en_dma_descriptor_type_t Cy_DMA_Descriptor_GetDescriptorType(cy_stc_dma_descriptor_t const * descriptor)
{
    return((cy_en_dma_descriptor_type_t) (((uint32_t)(descriptor->ctl) & ((uint32_t)0x3UL << (30UL))) >> (30UL)));
}
static inline void Cy_DMA_Descriptor_SetChannelState(cy_stc_dma_descriptor_t * descriptor, cy_en_dma_channel_state_t channelState)
{
    do { if(!(((CY_DMA_CHANNEL_ENABLED == (channelState)) || (CY_DMA_CHANNEL_DISABLED == (channelState))))) { CY_HALT(); } } while (0);
    ((descriptor->ctl) = ((((descriptor->ctl)) & ((uint32_t)(~(((uint32_t)0x1UL << (24UL)))))) | ((((uint32_t)((channelState)) << (24UL)) & ((uint32_t)0x1UL << (24UL))))));
}
static inline cy_en_dma_channel_state_t Cy_DMA_Descriptor_GetChannelState(cy_stc_dma_descriptor_t const * descriptor)
{
    return((cy_en_dma_channel_state_t) (((uint32_t)(descriptor->ctl) & ((uint32_t)0x1UL << (24UL))) >> (24UL)));
}
static inline void Cy_DMA_Descriptor_SetXloopDataCount(cy_stc_dma_descriptor_t * descriptor, uint32_t xCount)
{
    do { if(!(CY_DMA_SINGLE_TRANSFER != Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    do { if(!((((xCount) >= (1UL)) && ((xCount) <= (256UL))))) { CY_HALT(); } } while (0);
    ((descriptor->xCtl) = ((((descriptor->xCtl)) & ((uint32_t)(~(((uint32_t)0xFFUL << (24UL)))))) | ((((uint32_t)((xCount - 1UL)) << (24UL)) & ((uint32_t)0xFFUL << (24UL))))));
}
static inline uint32_t Cy_DMA_Descriptor_GetXloopDataCount(cy_stc_dma_descriptor_t const * descriptor)
{
    do { if(!(CY_DMA_SINGLE_TRANSFER != Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    return ((((uint32_t)(descriptor->xCtl) & ((uint32_t)0xFFUL << (24UL))) >> (24UL)) + 1UL);
}
static inline void Cy_DMA_Descriptor_SetXloopSrcIncrement(cy_stc_dma_descriptor_t * descriptor, int32_t srcXincrement)
{
    do { if(!(CY_DMA_SINGLE_TRANSFER != Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    do { if(!((((srcXincrement) >= (-2048L)) && ((srcXincrement) <= (2047L))))) { CY_HALT(); } } while (0);
    ((descriptor->xCtl) = ((((descriptor->xCtl)) & ((uint32_t)(~(((uint32_t)0xFFFUL << (0UL)))))) | ((((uint32_t)((srcXincrement)) << (0UL)) & ((uint32_t)0xFFFUL << (0UL))))));
}
static inline int32_t Cy_DMA_Descriptor_GetXloopSrcIncrement(cy_stc_dma_descriptor_t const * descriptor)
{
    do { if(!(CY_DMA_SINGLE_TRANSFER != Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    return ((int32_t) (((uint32_t)(descriptor->xCtl) & ((uint32_t)0xFFFUL << (0UL))) >> (0UL)));
}
static inline void Cy_DMA_Descriptor_SetXloopDstIncrement(cy_stc_dma_descriptor_t * descriptor, int32_t dstXincrement)
{
    do { if(!(CY_DMA_SINGLE_TRANSFER != Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    do { if(!((((dstXincrement) >= (-2048L)) && ((dstXincrement) <= (2047L))))) { CY_HALT(); } } while (0);
    ((descriptor->xCtl) = ((((descriptor->xCtl)) & ((uint32_t)(~(((uint32_t)0xFFFUL << (12UL)))))) | ((((uint32_t)((dstXincrement)) << (12UL)) & ((uint32_t)0xFFFUL << (12UL))))));
}
static inline int32_t Cy_DMA_Descriptor_GetXloopDstIncrement(cy_stc_dma_descriptor_t const * descriptor)
{
    do { if(!(CY_DMA_SINGLE_TRANSFER != Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    return ((int32_t) (((uint32_t)(descriptor->xCtl) & ((uint32_t)0xFFFUL << (12UL))) >> (12UL)));
}
static inline void Cy_DMA_Descriptor_SetYloopDataCount(cy_stc_dma_descriptor_t * descriptor, uint32_t yCount)
{
    do { if(!(CY_DMA_2D_TRANSFER == Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    do { if(!((((yCount) >= (1UL)) && ((yCount) <= (256UL))))) { CY_HALT(); } } while (0);
    ((descriptor->yCtl) = ((((descriptor->yCtl)) & ((uint32_t)(~(((uint32_t)0xFFUL << (24UL)))))) | ((((uint32_t)((yCount - 1UL)) << (24UL)) & ((uint32_t)0xFFUL << (24UL))))));
}
static inline uint32_t Cy_DMA_Descriptor_GetYloopDataCount(cy_stc_dma_descriptor_t const * descriptor)
{
    do { if(!(CY_DMA_2D_TRANSFER == Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    return ((((uint32_t)(descriptor->yCtl) & ((uint32_t)0xFFUL << (24UL))) >> (24UL)) + 1UL);
}
static inline void Cy_DMA_Descriptor_SetYloopSrcIncrement(cy_stc_dma_descriptor_t * descriptor, int32_t srcYincrement)
{
    do { if(!(CY_DMA_2D_TRANSFER == Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    do { if(!((((srcYincrement) >= (-2048L)) && ((srcYincrement) <= (2047L))))) { CY_HALT(); } } while (0);
    ((descriptor->yCtl) = ((((descriptor->yCtl)) & ((uint32_t)(~(((uint32_t)0xFFFUL << (0UL)))))) | ((((uint32_t)((srcYincrement)) << (0UL)) & ((uint32_t)0xFFFUL << (0UL))))));
}
static inline int32_t Cy_DMA_Descriptor_GetYloopSrcIncrement(cy_stc_dma_descriptor_t const * descriptor)
{
    do { if(!(CY_DMA_2D_TRANSFER == Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    return ((int32_t) (((uint32_t)(descriptor->yCtl) & ((uint32_t)0xFFFUL << (0UL))) >> (0UL)));
}
static inline void Cy_DMA_Descriptor_SetYloopDstIncrement(cy_stc_dma_descriptor_t * descriptor, int32_t dstYincrement)
{
    do { if(!(CY_DMA_2D_TRANSFER == Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    do { if(!((((dstYincrement) >= (-2048L)) && ((dstYincrement) <= (2047L))))) { CY_HALT(); } } while (0);
    ((descriptor->yCtl) = ((((descriptor->yCtl)) & ((uint32_t)(~(((uint32_t)0xFFFUL << (12UL)))))) | ((((uint32_t)((dstYincrement)) << (12UL)) & ((uint32_t)0xFFFUL << (12UL))))));
}
static inline int32_t Cy_DMA_Descriptor_GetYloopDstIncrement(cy_stc_dma_descriptor_t const * descriptor)
{
    do { if(!(CY_DMA_2D_TRANSFER == Cy_DMA_Descriptor_GetDescriptorType(descriptor))) { CY_HALT(); } } while (0);
    return ((int32_t) (((uint32_t)(descriptor->yCtl) & ((uint32_t)0xFFFUL << (12UL))) >> (12UL)));
}
static inline void Cy_DMA_Channel_SetDescriptor(DW_Type * base, uint32_t channel, cy_stc_dma_descriptor_t const * descriptor)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    (((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->CH_CURR_PTR) = (uint32_t)descriptor;
    (((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->CH_IDX) &= (uint32_t) ~(0xFFUL | 0xFF00UL);
}
static inline void Cy_DMA_Channel_Enable(DW_Type * base, uint32_t channel)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    (((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->CH_CTL) |= 0x80000000UL;
}
static inline void Cy_DMA_Channel_Disable(DW_Type * base, uint32_t channel)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    (((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->CH_CTL) &= (uint32_t) ~0x80000000UL;
}
static inline void Cy_DMA_Channel_SetPriority(DW_Type * base, uint32_t channel, uint32_t priority)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    do { if(!(((priority) <= 3UL))) { CY_HALT(); } } while (0);
    (((((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->CH_CTL)) = (((((((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->CH_CTL))) & ((uint32_t)(~(((uint32_t)(0x3UL << ((uint32_t)(cy_device->dwChCtlPrioPos)))))))) | ((((uint32_t)((priority)) << ((uint32_t)(cy_device->dwChCtlPrioPos))) & ((uint32_t)(0x3UL << ((uint32_t)(cy_device->dwChCtlPrioPos))))))));
}
static inline uint32_t Cy_DMA_Channel_GetPriority(DW_Type const * base, uint32_t channel)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    return ((uint32_t) (((uint32_t)((((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->CH_CTL)) & ((uint32_t)(0x3UL << ((uint32_t)(cy_device->dwChCtlPrioPos))))) >> ((uint32_t)(cy_device->dwChCtlPrioPos))));
}
static inline cy_stc_dma_descriptor_t * Cy_DMA_Channel_GetCurrentDescriptor(DW_Type const * base, uint32_t channel)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    return ((cy_stc_dma_descriptor_t*)((((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->CH_CURR_PTR)));
}
static inline uint32_t Cy_DMA_Channel_GetInterruptStatus(DW_Type const * base, uint32_t channel)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    return ((((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->INTR));
}
static inline cy_en_dma_intr_cause_t Cy_DMA_Channel_GetStatus(DW_Type const * base, uint32_t channel)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    return ((cy_en_dma_intr_cause_t) (((uint32_t)((((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->CH_STATUS)) & 0xFUL) >> 0UL));
}
static inline void Cy_DMA_Channel_ClearInterrupt(DW_Type * base, uint32_t channel)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    (((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->INTR) = (0x01UL);
    (void) (((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->INTR);
}
static inline void Cy_DMA_Channel_SetInterrupt(DW_Type * base, uint32_t channel)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    (((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->INTR_SET) = (0x01UL);
}
static inline uint32_t Cy_DMA_Channel_GetInterruptMask(DW_Type const * base, uint32_t channel)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    return ((((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->INTR_MASK));
}
static inline void Cy_DMA_Channel_SetInterruptMask(DW_Type * base, uint32_t channel, uint32_t interrupt)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    do { if(!((0UL == ((interrupt) & ((uint32_t) ~(0x01UL)))))) { CY_HALT(); } } while (0);
    (((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->INTR_MASK) = interrupt;
}
static inline uint32_t Cy_DMA_Channel_GetInterruptStatusMasked(DW_Type const * base, uint32_t channel)
{
    do { if(!(((((DW_Type*) 0x40280000UL) == (base)) ? ((channel) < (cy_device->cpussDw0ChNr)) : ((channel) < (cy_device->cpussDw1ChNr))))) { CY_HALT(); } } while (0);
    return ((((DW_CH_STRUCT_V2_Type*)((uint32_t)(base) + cy_device->dwChOffset + ((channel) * cy_device->dwChSize)))->INTR_MASKED));
}

typedef enum
{
    CY_EFUSE_SUCCESS = 0x00UL,
    CY_EFUSE_INVALID_PROTECTION = (((uint32_t)((uint32_t)((0x1AUL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01UL,
    CY_EFUSE_INVALID_FUSE_ADDR = (((uint32_t)((uint32_t)((0x1AUL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02UL,
    CY_EFUSE_BAD_PARAM = (((uint32_t)((uint32_t)((0x1AUL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x03UL,
    CY_EFUSE_IPC_BUSY = (((uint32_t)((uint32_t)((0x1AUL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x04UL,
    CY_EFUSE_WRITE_BUSY = (((uint32_t)((uint32_t)((0x1AUL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x05UL,
    CY_EFUSE_WRITE_ERROR = (((uint32_t)((uint32_t)((0x1AUL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x06UL,
    CY_EFUSE_WRITE_TIMEOUT_ERROR = (((uint32_t)((uint32_t)((0x1AUL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x07UL,
    CY_EFUSE_ERR_UNC = (((uint32_t)((uint32_t)((0x1AUL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0xFFUL
} cy_en_efuse_status_t;
cy_en_efuse_status_t Cy_EFUSE_GetEfuseBit(uint32_t bitNum, _Bool *bitVal);
cy_en_efuse_status_t Cy_EFUSE_GetEfuseByte(uint32_t offset, uint8_t *byteVal);
uint32_t Cy_EFUSE_GetExternalStatus(void);
typedef enum
{
    CY_IPC_DRV_SUCCESS = (0x00U),
    CY_IPC_DRV_ERROR = ( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 1UL),
} cy_en_ipcdrv_status_t;
static inline void Cy_IPC_Drv_WriteDataValue (IPC_STRUCT_Type* base, uint32_t dataValue);
static inline uint32_t Cy_IPC_Drv_ReadDataValue (IPC_STRUCT_Type const * base);
static inline uint32_t Cy_IPC_Drv_ExtractAcquireMask (uint32_t intMask);
static inline uint32_t Cy_IPC_Drv_ExtractReleaseMask (uint32_t intMask);
static inline IPC_STRUCT_Type* Cy_IPC_Drv_GetIpcBaseAddress (uint32_t ipcIndex);
static inline IPC_INTR_STRUCT_Type* Cy_IPC_Drv_GetIntrBaseAddr (uint32_t ipcIntrIndex);
static inline void Cy_IPC_Drv_AcquireNotify (IPC_STRUCT_Type * base, uint32_t notifyEventIntr);
static inline void Cy_IPC_Drv_ReleaseNotify (IPC_STRUCT_Type * base, uint32_t notifyEventIntr);
static inline cy_en_ipcdrv_status_t Cy_IPC_Drv_LockAcquire (IPC_STRUCT_Type const * base);
cy_en_ipcdrv_status_t Cy_IPC_Drv_LockRelease (IPC_STRUCT_Type * base, uint32_t releaseEventIntr);
static inline _Bool Cy_IPC_Drv_IsLockAcquired (IPC_STRUCT_Type const * base);
static inline uint32_t Cy_IPC_Drv_GetLockStatus (IPC_STRUCT_Type const * base);
cy_en_ipcdrv_status_t Cy_IPC_Drv_SendMsgWord (IPC_STRUCT_Type * base, uint32_t notifyEventIntr, uint32_t message);
cy_en_ipcdrv_status_t Cy_IPC_Drv_ReadMsgWord (IPC_STRUCT_Type const * base, uint32_t * message);
static inline cy_en_ipcdrv_status_t Cy_IPC_Drv_SendMsgPtr (IPC_STRUCT_Type* base, uint32_t notifyEventIntr, void const * msgPtr);
static inline cy_en_ipcdrv_status_t Cy_IPC_Drv_ReadMsgPtr (IPC_STRUCT_Type const * base, void ** msgPtr);
static inline void Cy_IPC_Drv_SetInterruptMask (IPC_INTR_STRUCT_Type * base,
                                                      uint32_t ipcReleaseMask, uint32_t ipcNotifyMask);
static inline uint32_t Cy_IPC_Drv_GetInterruptMask (IPC_INTR_STRUCT_Type const * base);
static inline uint32_t Cy_IPC_Drv_GetInterruptStatusMasked (IPC_INTR_STRUCT_Type const * base);
static inline uint32_t Cy_IPC_Drv_GetInterruptStatus (IPC_INTR_STRUCT_Type const * base);
static inline void Cy_IPC_Drv_SetInterrupt (IPC_INTR_STRUCT_Type * base,
                                                      uint32_t ipcReleaseMask, uint32_t ipcNotifyMask);
static inline void Cy_IPC_Drv_ClearInterrupt (IPC_INTR_STRUCT_Type * base,
                                                      uint32_t ipcReleaseMask, uint32_t ipcNotifyMask);
static inline IPC_STRUCT_Type* Cy_IPC_Drv_GetIpcBaseAddress (uint32_t ipcIndex)
{
    do { if(!(((uint32_t)(cy_device->cpussIpcNr)) > ipcIndex)) { CY_HALT(); } } while (0);
    return ( (IPC_STRUCT_Type*) ((IPC_STRUCT_Type*)(cy_device->ipcBase + (cy_device->ipcStructSize * (ipcIndex)))));
}
static inline IPC_INTR_STRUCT_Type* Cy_IPC_Drv_GetIntrBaseAddr (uint32_t ipcIntrIndex)
{
    do { if(!(((uint32_t)(cy_device->cpussIpcIrqNr)) > ipcIntrIndex)) { CY_HALT(); } } while (0);
    return ( (IPC_INTR_STRUCT_Type*) (&(((IPC_Type *)cy_device->ipcBase)->INTR_STRUCT[ipcIntrIndex])));
}
static inline void Cy_IPC_Drv_SetInterruptMask (IPC_INTR_STRUCT_Type* base,
                                              uint32_t ipcReleaseMask, uint32_t ipcNotifyMask)
{
    do { if(!(0UL == (ipcNotifyMask & ~(uint32_t)(0xFFFFUL)))) { CY_HALT(); } } while (0);
    do { if(!(0UL == (ipcReleaseMask & ~(uint32_t)(0xFFFFUL)))) { CY_HALT(); } } while (0);
    (((IPC_INTR_STRUCT_Type*)(base))->INTR_MASK) = (((uint32_t)(ipcNotifyMask) << 16UL) & 0xFFFF0000UL) |
                      (((uint32_t)(ipcReleaseMask) << 0UL) & 0xFFFFUL);
}
static inline uint32_t Cy_IPC_Drv_GetInterruptMask(IPC_INTR_STRUCT_Type const * base)
{
    return (((IPC_INTR_STRUCT_Type*)(base))->INTR_MASK);
}
static inline uint32_t Cy_IPC_Drv_GetInterruptStatusMasked (IPC_INTR_STRUCT_Type const * base)
{
    return (((IPC_INTR_STRUCT_Type*)(base))->INTR_MASKED);
}
static inline uint32_t Cy_IPC_Drv_GetInterruptStatus(IPC_INTR_STRUCT_Type const * base)
{
    return (((IPC_INTR_STRUCT_Type*)(base))->INTR);
}
static inline void Cy_IPC_Drv_SetInterrupt(IPC_INTR_STRUCT_Type* base, uint32_t ipcReleaseMask, uint32_t ipcNotifyMask)
{
    do { if(!(0UL == (ipcNotifyMask & ~(uint32_t)(0xFFFFUL)))) { CY_HALT(); } } while (0);
    do { if(!(0UL == (ipcReleaseMask & ~(uint32_t)(0xFFFFUL)))) { CY_HALT(); } } while (0);
    (((IPC_INTR_STRUCT_Type*)(base))->INTR_SET) = (((uint32_t)(ipcNotifyMask) << 16UL) & 0xFFFF0000UL) |
                      (((uint32_t)(ipcReleaseMask) << 0UL) & 0xFFFFUL);
}
static inline void Cy_IPC_Drv_ClearInterrupt(IPC_INTR_STRUCT_Type* base, uint32_t ipcReleaseMask, uint32_t ipcNotifyMask)
{
    do { if(!(0UL == (ipcNotifyMask & ~(uint32_t)(0xFFFFUL)))) { CY_HALT(); } } while (0);
    do { if(!(0UL == (ipcReleaseMask & ~(uint32_t)(0xFFFFUL)))) { CY_HALT(); } } while (0);
    (((IPC_INTR_STRUCT_Type*)(base))->INTR) = (((uint32_t)(ipcNotifyMask) << 16UL) & 0xFFFF0000UL) |
                  (((uint32_t)(ipcReleaseMask) << 0UL) & 0xFFFFUL);
    (void)(((IPC_INTR_STRUCT_Type*)(base))->INTR);
}
static inline void Cy_IPC_Drv_AcquireNotify (IPC_STRUCT_Type* base, uint32_t notifyEventIntr)
{
    do { if(!(0UL == (notifyEventIntr & ~(uint32_t)(0xFFFFUL)))) { CY_HALT(); } } while (0);
    (((IPC_STRUCT_Type*)(base))->NOTIFY) = (((uint32_t)(notifyEventIntr) << 0UL) & 0xFFFFUL);
}
static inline void Cy_IPC_Drv_ReleaseNotify (IPC_STRUCT_Type* base, uint32_t notifyEventIntr)
{
    do { if(!(0UL == (notifyEventIntr & ~(uint32_t)(0xFFFFUL)))) { CY_HALT(); } } while (0);
    (((IPC_STRUCT_Type*)(base))->RELEASE) = (((uint32_t)(notifyEventIntr) << 0UL) & 0xFFFFUL);
}
static inline void Cy_IPC_Drv_WriteDataValue (IPC_STRUCT_Type* base, uint32_t dataValue)
{
    (((IPC_STRUCT_V1_Type*)(base))->DATA) = dataValue;
}
static inline uint32_t Cy_IPC_Drv_ReadDataValue (IPC_STRUCT_Type const * base)
{
    return (((IPC_STRUCT_V1_Type*)(base))->DATA);
}
static inline _Bool Cy_IPC_Drv_IsLockAcquired (IPC_STRUCT_Type const * base)
{
    return ( 0u != (((uint32_t)((*(volatile uint32_t*)((uint32_t)(base) + cy_device->ipcLockStatusOffset))) & 0x80000000UL) >> 31UL) );
}
static inline uint32_t Cy_IPC_Drv_GetLockStatus (IPC_STRUCT_Type const * base)
{
    return (*(volatile uint32_t*)((uint32_t)(base) + cy_device->ipcLockStatusOffset));
}
static inline uint32_t Cy_IPC_Drv_ExtractAcquireMask (uint32_t intMask)
{
    return (((uint32_t)(intMask) & 0xFFFF0000UL) >> 16UL);
}
static inline uint32_t Cy_IPC_Drv_ExtractReleaseMask (uint32_t intMask)
{
    return (((uint32_t)(intMask) & 0xFFFFUL) >> 0UL);
}
static inline cy_en_ipcdrv_status_t Cy_IPC_Drv_SendMsgPtr(IPC_STRUCT_Type* base, uint32_t notifyEventIntr, void const * msgPtr)
{
    do { if(!(((void *)0) != msgPtr)) { CY_HALT(); } } while (0);
    return Cy_IPC_Drv_SendMsgWord(base, notifyEventIntr, (uint32_t)msgPtr);
}
static inline cy_en_ipcdrv_status_t Cy_IPC_Drv_ReadMsgPtr (IPC_STRUCT_Type const * base, void ** msgPtr)
{
    do { if(!(((void *)0) != msgPtr)) { CY_HALT(); } } while (0);
    return Cy_IPC_Drv_ReadMsgWord(base, (uint32_t *)msgPtr);
}
static inline cy_en_ipcdrv_status_t Cy_IPC_Drv_LockAcquire (IPC_STRUCT_Type const * base)
{
    return ( 0UL != (((uint32_t)((((IPC_STRUCT_Type*)(base))->ACQUIRE)) & 0x80000000UL) >> 31UL)) ? CY_IPC_DRV_SUCCESS : CY_IPC_DRV_ERROR;
}
typedef enum cy_en_flashdrv_status
{
    CY_FLASH_DRV_SUCCESS = 0x00UL,
    CY_FLASH_DRV_INV_PROT = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x0UL),
    CY_FLASH_DRV_INVALID_FM_PL = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x1UL),
    CY_FLASH_DRV_INVALID_FLASH_ADDR = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x2UL),
    CY_FLASH_DRV_ROW_PROTECTED = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x3UL),
    CY_FLASH_DRV_IPC_BUSY = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x5UL),
    CY_FLASH_DRV_INVALID_INPUT_PARAMETERS = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x6UL),
    CY_FLASH_DRV_PL_ROW_COMP_FA = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x22UL),
    CY_FLASH_DRV_ERR_UNC = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0xFFUL),
    CY_FLASH_DRV_PROGRESS_NO_ERROR = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_INFO << ((16U))) ) + 0x0UL),
    CY_FLASH_DRV_OPERATION_STARTED = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_INFO << ((16U))) ) + 0x1UL),
    CY_FLASH_DRV_OPCODE_BUSY = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_INFO << ((16U))) ) + 0x2UL),
    CY_FLASH_DRV_CHECKSUM_NON_ZERO = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x4UL),
    CY_FLASH_DRV_NO_ERASE_SUSPEND = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x7UL),
    CY_FLASH_DRV_FLASH_NOT_ERASED = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x8UL),
    CY_FLASH_DRV_NO_ERASE_ONGOING = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x9UL),
    CY_FLASH_DRV_ACTIVE_ERASE = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0xAUL),
    CY_FLASH_DRV_INVALID_DATA_WIDTH = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0xBUL),
    CY_FLASH_DRV_FLASH_SAFTEY_ENABLED = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0xCUL),
    CY_FLASH_DRV_INVALID_SFLASH_ADDR = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0xDUL),
    CY_FLASH_DRV_SFLASH_BACKUP_ERASED = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0xEUL),
    CY_FLASH_DRV_SECTOR_SUSPEND = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0xFUL),
    CY_FLASH_DRV_SROM_API_TIMEOUT = ( (uint32_t)( (((uint32_t)((uint32_t)((0x14UL) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) + 0x10UL),
} cy_en_flashdrv_status_t;
    typedef struct
    {
        uint8_t clientID;
        uint8_t pktType;
        uint16_t intrRelMask;
    } cy_stc_flash_notify_t;
cy_en_flashdrv_status_t Cy_Flash_EraseRow(uint32_t rowAddr);
cy_en_flashdrv_status_t Cy_Flash_StartEraseRow(uint32_t rowAddr);
cy_en_flashdrv_status_t Cy_Flash_EraseSubsector(uint32_t subSectorAddr);
cy_en_flashdrv_status_t Cy_Flash_StartEraseSubsector(uint32_t subSectorAddr);
cy_en_flashdrv_status_t Cy_Flash_WriteRow(uint32_t rowAddr, const uint32_t* data);
cy_en_flashdrv_status_t Cy_Flash_StartProgram(uint32_t rowAddr, const uint32_t* data);
uint32_t Cy_Flash_GetExternalStatus(void);
void Cy_Flash_InitExt(cy_stc_flash_notify_t *ipcWaitMessageAddr);
void Cy_Flash_ResumeIrqHandler(void);
cy_en_flashdrv_status_t Cy_Flash_IsOperationComplete(void);
cy_en_flashdrv_status_t Cy_Flash_StartWrite(uint32_t rowAddr, const uint32_t* data);
cy_en_flashdrv_status_t Cy_Flash_StartEraseSector(uint32_t sectorAddr);
cy_en_flashdrv_status_t Cy_Flash_ProgramRow(uint32_t rowAddr, const uint32_t* data);
cy_en_flashdrv_status_t Cy_Flash_EraseSector(uint32_t sectorAddr);
cy_en_flashdrv_status_t Cy_Flash_CalculateHash(const uint32_t* data, uint32_t numberOfBytes, uint32_t* hashPtr);
cy_en_flashdrv_status_t Cy_Flash_RowChecksum(uint32_t rowAddr, uint32_t* checksumPtr);
void Cy_Flash_Init(void);
typedef enum
{
    CY_GPIO_SUCCESS = 0x00U,
    CY_GPIO_BAD_PARAM = ((uint32_t)((uint32_t)((0x16U) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01U,
} cy_en_gpio_status_t;
typedef enum
{
    CY_GPIO_AMUX_OPENALL,
    CY_GPIO_AMUX_L,
    CY_GPIO_AMUX_R,
    CY_GPIO_AMUX_LR,
    CY_GPIO_AMUX_G,
    CY_GPIO_AMUX_GL,
    CY_GPIO_AMUX_GR,
    CY_GPIO_AMUX_GLR,
}cy_en_gpio_amuxconnect_t;
typedef enum
{
    CY_GPIO_AMUXBUSA,
    CY_GPIO_AMUXBUSB
}cy_en_gpio_amuxselect_t;
typedef struct
{
    uint32_t out;
    uint32_t intrMask;
    uint32_t intrCfg;
    uint32_t cfg;
    uint32_t cfgIn;
    uint32_t cfgOut;
    uint32_t cfgSIO;
    uint32_t sel0Active;
    uint32_t sel1Active;
} cy_stc_gpio_prt_config_t;
typedef struct
{
    uint32_t outVal;
    uint32_t driveMode;
    en_hsiom_sel_t hsiom;
    uint32_t intEdge;
    uint32_t intMask;
    uint32_t vtrip;
    uint32_t slewRate;
    uint32_t driveSel;
    uint32_t vregEn;
    uint32_t ibufMode;
    uint32_t vtripSel;
    uint32_t vrefSel;
    uint32_t vohSel;
} cy_stc_gpio_pin_config_t;
cy_en_gpio_status_t Cy_GPIO_Pin_Init(GPIO_PRT_Type* base, uint32_t pinNum, const cy_stc_gpio_pin_config_t *config);
cy_en_gpio_status_t Cy_GPIO_Port_Init(GPIO_PRT_Type* base, const cy_stc_gpio_prt_config_t *config);
void Cy_GPIO_Pin_FastInit(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t driveMode, uint32_t outVal, en_hsiom_sel_t hsiom);
void Cy_GPIO_Port_Deinit(GPIO_PRT_Type* base);
void Cy_GPIO_SetHSIOM(GPIO_PRT_Type* base, uint32_t pinNum, en_hsiom_sel_t value);
en_hsiom_sel_t Cy_GPIO_GetHSIOM(GPIO_PRT_Type* base, uint32_t pinNum);
static inline GPIO_PRT_Type* Cy_GPIO_PortToAddr(uint32_t portNum);
void Cy_GPIO_SetAmuxSplit(cy_en_amux_split_t switchCtrl, cy_en_gpio_amuxconnect_t amuxConnect, cy_en_gpio_amuxselect_t amuxBus);
cy_en_gpio_amuxconnect_t Cy_GPIO_GetAmuxSplit(cy_en_amux_split_t switchCtrl, cy_en_gpio_amuxselect_t amuxBus);
uint32_t Cy_GPIO_Read(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_Write(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_ReadOut(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_Set(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_Clr(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_Inv(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetDrivemode(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetDrivemode(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetVtrip(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetVtrip(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetSlewRate(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetSlewRate(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetDriveSel(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetDriveSel(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetVregEn(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetVregEn(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetIbufMode(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetIbufMode(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetVtripSel(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetVtripSel(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetVrefSel(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetVrefSel(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetVohSel(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetVohSel(GPIO_PRT_Type* base, uint32_t pinNum);
uint32_t Cy_GPIO_GetInterruptStatus(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_ClearInterrupt(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetInterruptMask(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetInterruptMask(GPIO_PRT_Type* base, uint32_t pinNum);
uint32_t Cy_GPIO_GetInterruptStatusMasked(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetSwInterrupt(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetInterruptEdge(GPIO_PRT_Type* base, uint32_t pinNum, uint32_t value);
uint32_t Cy_GPIO_GetInterruptEdge(GPIO_PRT_Type* base, uint32_t pinNum);
void Cy_GPIO_SetFilter(GPIO_PRT_Type* base, uint32_t value);
uint32_t Cy_GPIO_GetFilter(GPIO_PRT_Type* base);
static inline uint32_t Cy_GPIO_GetInterruptCause0(void);
static inline uint32_t Cy_GPIO_GetInterruptCause1(void);
static inline uint32_t Cy_GPIO_GetInterruptCause2(void);
static inline uint32_t Cy_GPIO_GetInterruptCause3(void);
static inline GPIO_PRT_Type* Cy_GPIO_PortToAddr(uint32_t portNum)
{
    GPIO_PRT_Type* portBase;
    if(portNum < (uint32_t)15u)
    {
        portBase = (GPIO_PRT_Type *)(((uint32_t)(cy_device->gpioBase)) + (0x00000080UL * portNum));
    }
    else
    {
        portBase = (GPIO_PRT_Type *)(((uint32_t)(cy_device->gpioBase)));
    }
    return (portBase);
}
static inline uint32_t Cy_GPIO_GetInterruptCause0(void)
{
    return ((((GPIO_V1_Type*)(cy_device->gpioBase))->INTR_CAUSE0));
}
static inline uint32_t Cy_GPIO_GetInterruptCause1(void)
{
    return ((((GPIO_V1_Type*)(cy_device->gpioBase))->INTR_CAUSE1));
}
static inline uint32_t Cy_GPIO_GetInterruptCause2(void)
{
    return ((((GPIO_V1_Type*)(cy_device->gpioBase))->INTR_CAUSE2));
}
static inline uint32_t Cy_GPIO_GetInterruptCause3(void)
{
    return ((((GPIO_V1_Type*)(cy_device->gpioBase))->INTR_CAUSE3));
}
typedef enum
{
    CY_I2S_SUCCESS = 0x00UL,
    CY_I2S_BAD_PARAM = (((uint32_t)((uint32_t)((0x20U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01UL
} cy_en_i2s_status_t;
typedef enum
{
    CY_I2S_LEFT_JUSTIFIED = 0U,
    CY_I2S_I2S_MODE = 1U,
    CY_I2S_TDM_MODE_A = 2U,
    CY_I2S_TDM_MODE_B = 3U
} cy_en_i2s_alignment_t;
typedef enum
{
    CY_I2S_LEN8 = 0U,
    CY_I2S_LEN16 = 1U,
    CY_I2S_LEN18 = 2U,
    CY_I2S_LEN20 = 3U,
    CY_I2S_LEN24 = 4U,
    CY_I2S_LEN32 = 5U
} cy_en_i2s_len_t;
typedef enum
{
    CY_I2S_OVHDATA_ZERO = 0U,
    CY_I2S_OVHDATA_ONE = 1U,
} cy_en_i2s_overhead_t;
typedef enum
{
    CY_I2S_WS_ONE_SCK_CYCLE = 0U,
    CY_I2S_WS_ONE_CHANNEL_LENGTH = 1U,
} cy_en_i2s_ws_pw_t;
typedef struct
{
    _Bool txEnabled;
    _Bool rxEnabled;
    _Bool txDmaTrigger;
    _Bool rxDmaTrigger;
    uint8_t clkDiv;
    _Bool extClk;
    _Bool txMasterMode;
    cy_en_i2s_alignment_t txAlignment;
    cy_en_i2s_ws_pw_t txWsPulseWidth;
    _Bool txWatchdogEnable;
    uint32_t txWatchdogValue;
    _Bool txSdoLatchingTime;
    _Bool txSckoInversion;
    _Bool txSckiInversion;
    uint8_t txChannels;
    cy_en_i2s_len_t txChannelLength;
    cy_en_i2s_len_t txWordLength;
    cy_en_i2s_overhead_t txOverheadValue;
    uint8_t txFifoTriggerLevel;
    _Bool rxMasterMode;
    cy_en_i2s_alignment_t rxAlignment;
    cy_en_i2s_ws_pw_t rxWsPulseWidth;
    _Bool rxWatchdogEnable;
    uint32_t rxWatchdogValue;
    _Bool rxSdiLatchingTime;
    _Bool rxSckoInversion;
    _Bool rxSckiInversion;
    uint8_t rxChannels;
    cy_en_i2s_len_t rxChannelLength;
    cy_en_i2s_len_t rxWordLength;
    _Bool rxSignExtension;
    uint8_t rxFifoTriggerLevel;
} cy_stc_i2s_config_t;
typedef struct
{
    uint32_t enableState;
    uint32_t interruptMask;
} cy_stc_i2s_context_t;
  cy_en_i2s_status_t Cy_I2S_Init(I2S_Type * base, cy_stc_i2s_config_t const * config);
                void Cy_I2S_DeInit(I2S_Type * base);
cy_en_syspm_status_t Cy_I2S_DeepSleepCallback(cy_stc_syspm_callback_params_t const * callbackParams, cy_en_syspm_callback_mode_t mode);
static inline void Cy_I2S_EnableTx(I2S_Type * base);
static inline void Cy_I2S_PauseTx(I2S_Type * base);
static inline void Cy_I2S_ResumeTx(I2S_Type * base);
static inline void Cy_I2S_DisableTx(I2S_Type * base);
static inline void Cy_I2S_EnableRx(I2S_Type * base);
static inline void Cy_I2S_DisableRx(I2S_Type * base);
static inline uint32_t Cy_I2S_GetCurrentState(I2S_Type const * base);
static inline void Cy_I2S_ClearTxFifo(I2S_Type * base);
static inline uint32_t Cy_I2S_GetNumInTxFifo(I2S_Type const * base);
static inline void Cy_I2S_WriteTxData(I2S_Type * base, uint32_t data);
static inline uint8_t Cy_I2S_GetTxReadPointer(I2S_Type const * base);
static inline uint8_t Cy_I2S_GetTxWritePointer(I2S_Type const * base);
static inline void Cy_I2S_FreezeTxFifo(I2S_Type * base);
static inline void Cy_I2S_UnfreezeTxFifo(I2S_Type * base);
static inline void Cy_I2S_ClearRxFifo(I2S_Type * base);
static inline uint32_t Cy_I2S_GetNumInRxFifo(I2S_Type const * base);
static inline uint32_t Cy_I2S_ReadRxData(I2S_Type const * base);
static inline uint32_t Cy_I2S_ReadRxDataSilent(I2S_Type const * base);
static inline uint8_t Cy_I2S_GetRxReadPointer(I2S_Type const * base);
static inline uint8_t Cy_I2S_GetRxWritePointer(I2S_Type const * base);
static inline void Cy_I2S_FreezeRxFifo(I2S_Type * base);
static inline void Cy_I2S_UnfreezeRxFifo(I2S_Type * base);
static inline uint32_t Cy_I2S_GetInterruptStatus(I2S_Type const * base);
static inline void Cy_I2S_ClearInterrupt(I2S_Type * base, uint32_t interrupt);
static inline void Cy_I2S_SetInterrupt(I2S_Type * base, uint32_t interrupt);
static inline uint32_t Cy_I2S_GetInterruptMask(I2S_Type const * base);
static inline void Cy_I2S_SetInterruptMask(I2S_Type * base, uint32_t interrupt);
static inline uint32_t Cy_I2S_GetInterruptStatusMasked(I2S_Type const * base);
static inline void Cy_I2S_EnableTx(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->CMD) |= 0x1UL;
}
static inline void Cy_I2S_PauseTx(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->CMD) |= 0x100UL;
}
static inline void Cy_I2S_ResumeTx(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->CMD) &= (uint32_t) ~0x100UL;
}
static inline void Cy_I2S_DisableTx(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->CMD) &= (uint32_t) ~0x1UL;
}
static inline void Cy_I2S_EnableRx(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->CMD) |= 0x10000UL;
}
static inline void Cy_I2S_DisableRx(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->CMD) &= (uint32_t) ~0x10000UL;
}
static inline uint32_t Cy_I2S_GetCurrentState(I2S_Type const * base)
{
    return ((((I2S_V1_Type*)(base))->CMD) & (0x1UL | 0x100UL | 0x10000UL));
}
static inline void Cy_I2S_ClearTxFifo(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->TX_FIFO_CTL) |= 0x10000UL;
    (((I2S_V1_Type*)(base))->TX_FIFO_CTL) &= (uint32_t) ~0x10000UL;
    (void) (((I2S_V1_Type*)(base))->TX_FIFO_CTL);
}
static inline uint32_t Cy_I2S_GetNumInTxFifo(I2S_Type const * base)
{
    return ((((uint32_t)((((I2S_V1_Type*)(base))->TX_FIFO_STATUS)) & 0x1FFUL) >> 0UL));
}
static inline void Cy_I2S_WriteTxData(I2S_Type * base, uint32_t data)
{
    (((I2S_V1_Type*)(base))->TX_FIFO_WR) = data;
}
static inline uint8_t Cy_I2S_GetTxReadPointer(I2S_Type const * base)
{
    return ((uint8_t) (((uint32_t)((((I2S_V1_Type*)(base))->TX_FIFO_STATUS)) & 0xFF0000UL) >> 16UL));
}
static inline uint8_t Cy_I2S_GetTxWritePointer(I2S_Type const * base)
{
    return ((uint8_t) (((uint32_t)((((I2S_V1_Type*)(base))->TX_FIFO_STATUS)) & 0xFF000000UL) >> 24UL));
}
static inline void Cy_I2S_FreezeTxFifo(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->TX_FIFO_CTL) |= 0x20000UL;
}
static inline void Cy_I2S_UnfreezeTxFifo(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->TX_FIFO_CTL) &= (uint32_t) ~0x20000UL;
}
static inline void Cy_I2S_ClearRxFifo(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->RX_FIFO_CTL) |= 0x10000UL;
    (((I2S_V1_Type*)(base))->RX_FIFO_CTL) &= (uint32_t) ~0x10000UL;
    (void) (((I2S_V1_Type*)(base))->RX_FIFO_CTL) ;
}
static inline uint32_t Cy_I2S_GetNumInRxFifo(I2S_Type const * base)
{
    return ((((uint32_t)((((I2S_V1_Type*)(base))->RX_FIFO_STATUS)) & 0x1FFUL) >> 0UL));
}
static inline uint32_t Cy_I2S_ReadRxData(I2S_Type const * base)
{
    return ((((I2S_V1_Type*)(base))->RX_FIFO_RD));
}
static inline uint32_t Cy_I2S_ReadRxDataSilent(I2S_Type const * base)
{
    return ((((I2S_V1_Type*)(base))->RX_FIFO_RD_SILENT));
}
static inline uint8_t Cy_I2S_GetRxReadPointer(I2S_Type const * base)
{
    return ((uint8_t) (((uint32_t)((((I2S_V1_Type*)(base))->RX_FIFO_STATUS)) & 0xFF0000UL) >> 16UL));
}
static inline uint8_t Cy_I2S_GetRxWritePointer(I2S_Type const * base)
{
    return ((uint8_t) (((uint32_t)((((I2S_V1_Type*)(base))->RX_FIFO_STATUS)) & 0xFF000000UL) >> 24UL));
}
static inline void Cy_I2S_FreezeRxFifo(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->RX_FIFO_CTL) |= 0x20000UL;
}
static inline void Cy_I2S_UnfreezeRxFifo(I2S_Type * base)
{
    (((I2S_V1_Type*)(base))->RX_FIFO_CTL) &= (uint32_t) ~0x20000UL;
}
static inline uint32_t Cy_I2S_GetInterruptStatus(I2S_Type const * base)
{
    return ((((I2S_V1_Type*)(base))->INTR));
}
static inline void Cy_I2S_ClearInterrupt(I2S_Type * base, uint32_t interrupt)
{
    do { if(!((0UL == ((interrupt) & ((uint32_t) ~((0x1UL) | (0x2UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x100UL) | (0x10000UL) | (0x40000UL) | (0x80000UL) | (0x200000UL) | (0x400000UL) | (0x1000000UL))))))) { CY_HALT(); } } while (0);
    (((I2S_V1_Type*)(base))->INTR) = interrupt;
    (void) (((I2S_V1_Type*)(base))->INTR);
}
static inline void Cy_I2S_SetInterrupt(I2S_Type * base, uint32_t interrupt)
{
    do { if(!((0UL == ((interrupt) & ((uint32_t) ~((0x1UL) | (0x2UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x100UL) | (0x10000UL) | (0x40000UL) | (0x80000UL) | (0x200000UL) | (0x400000UL) | (0x1000000UL))))))) { CY_HALT(); } } while (0);
    (((I2S_V1_Type*)(base))->INTR_SET) = interrupt;
}
static inline uint32_t Cy_I2S_GetInterruptMask(I2S_Type const * base)
{
    return ((((I2S_V1_Type*)(base))->INTR_MASK));
}
static inline void Cy_I2S_SetInterruptMask(I2S_Type * base, uint32_t interrupt)
{
    do { if(!((0UL == ((interrupt) & ((uint32_t) ~((0x1UL) | (0x2UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x100UL) | (0x10000UL) | (0x40000UL) | (0x80000UL) | (0x200000UL) | (0x400000UL) | (0x1000000UL))))))) { CY_HALT(); } } while (0);
    (((I2S_V1_Type*)(base))->INTR_MASK) = interrupt;
}
static inline uint32_t Cy_I2S_GetInterruptStatusMasked(I2S_Type const * base)
{
    return ((((I2S_V1_Type*)(base))->INTR_MASKED));
}
typedef void (* cy_ipc_pipe_callback_ptr_t)(uint32_t * msgPtr);
typedef void (* cy_ipc_pipe_relcallback_ptr_t)(void);
typedef cy_ipc_pipe_callback_ptr_t *cy_ipc_pipe_callback_array_ptr_t;
typedef struct
{
    uint32_t ipcChan;
    uint32_t intrChan;
    uint32_t pipeIntMask;
    IRQn_Type pipeIntrSrc;
    IPC_STRUCT_Type *ipcPtr;
    IPC_INTR_STRUCT_Type *ipcIntrPtr;
    uint32_t busy;
    uint32_t clientCount;
    cy_ipc_pipe_callback_array_ptr_t callbackArray;
    cy_ipc_pipe_relcallback_ptr_t releaseCallbackPtr;
    cy_ipc_pipe_relcallback_ptr_t defaultReleaseCallbackPtr;
} cy_stc_ipc_pipe_ep_t;
typedef struct
{
    uint32_t ipcNotifierNumber;
    uint32_t ipcNotifierPriority;
    uint32_t ipcNotifierMuxNumber;
    uint32_t epAddress;
    uint32_t epConfig;
} cy_stc_ipc_pipe_ep_config_t;
typedef struct
{
    cy_stc_ipc_pipe_ep_config_t ep0ConfigData;
    cy_stc_ipc_pipe_ep_config_t ep1ConfigData;
    uint32_t endpointClientsCount;
    cy_ipc_pipe_callback_array_ptr_t endpointsCallbacksArray;
    cy_israddress userPipeIsrHandler;
} cy_stc_ipc_pipe_config_t;
typedef enum
{
    CY_IPC_PIPE_SUCCESS =(uint32_t)(0x00u),
    CY_IPC_PIPE_ERROR_NO_IPC =(uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0200UL)) | 1UL),
    CY_IPC_PIPE_ERROR_NO_INTR =(uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0200UL)) | 2UL),
    CY_IPC_PIPE_ERROR_BAD_PRIORITY =(uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0200UL)) | 3UL),
    CY_IPC_PIPE_ERROR_BAD_HANDLE =(uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0200UL)) | 4UL),
    CY_IPC_PIPE_ERROR_BAD_ID =(uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0200UL)) | 5UL),
    CY_IPC_PIPE_ERROR_DIR_ERROR =(uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0200UL)) | 6UL),
    CY_IPC_PIPE_ERROR_SEND_BUSY =(uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0200UL)) | 7UL),
    CY_IPC_PIPE_ERROR_NO_MESSAGE =(uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0200UL)) | 8UL),
    CY_IPC_PIPE_ERROR_BAD_CPU =(uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0200UL)) | 9UL),
    CY_IPC_PIPE_ERROR_BAD_CLIENT =(uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0200UL)) | 10UL)
} cy_en_ipc_pipe_status_t;
void Cy_IPC_Pipe_EndpointInit(uint32_t epAddr, cy_ipc_pipe_callback_array_ptr_t cbArray,
                              uint32_t cbCnt, uint32_t epConfig, cy_stc_sysint_t const *epInterrupt);
cy_en_ipc_pipe_status_t Cy_IPC_Pipe_SendMessage(uint32_t toAddr, uint32_t fromAddr, void *msgPtr,
                              cy_ipc_pipe_relcallback_ptr_t callBackPtr);
cy_en_ipc_pipe_status_t Cy_IPC_Pipe_RegisterCallback(uint32_t epAddr,
                              cy_ipc_pipe_callback_ptr_t callBackPtr, uint32_t clientId);
void Cy_IPC_Pipe_ExecuteCallback(uint32_t epAddr);
void Cy_IPC_Pipe_RegisterCallbackRel(uint32_t epAddr, cy_ipc_pipe_relcallback_ptr_t callBackPtr);
void Cy_IPC_Pipe_Config(cy_stc_ipc_pipe_ep_t * theEpArray);
void Cy_IPC_Pipe_Init(cy_stc_ipc_pipe_config_t const *config);
cy_en_ipc_pipe_status_t Cy_IPC_Pipe_EndpointPause(uint32_t epAddr);
cy_en_ipc_pipe_status_t Cy_IPC_Pipe_EndpointResume(uint32_t epAddr);
void Cy_IPC_Pipe_ExecCallback(cy_stc_ipc_pipe_ep_t * endpoint);
typedef enum
{
    CY_IPC_SEMA_SUCCESS = (uint32_t)(0UL),
    CY_IPC_SEMA_ERROR_LOCKED = (uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0100UL)) | 1UL),
    CY_IPC_SEMA_ERROR_UNLOCKED = (uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0100UL)) | 2UL),
    CY_IPC_SEMA_BAD_PARAM = (uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0100UL)) | 3UL),
    CY_IPC_SEMA_OUT_OF_RANGE = (uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U)))) | (0x0100UL)) | 4UL),
    CY_IPC_SEMA_NOT_ACQUIRED = (uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_INFO << ((16U))) ) | (0x0100UL)) | 2UL),
    CY_IPC_SEMA_LOCKED = (uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_INFO << ((16U))) ) | (0x0100UL)) | 3UL),
    CY_IPC_SEMA_STATUS_LOCKED = (uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_INFO << ((16U))) ) | (0x0100UL)) | 1UL),
    CY_IPC_SEMA_STATUS_UNLOCKED = (uint32_t)((uint32_t)( (uint32_t)( ((uint32_t)((uint32_t)((0x22u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_INFO << ((16U))) ) | (0x0100UL)) | 0UL)
} cy_en_ipcsema_status_t;
typedef struct
{
    uint32_t maxSema;
    uint32_t *arrayPtr;
} cy_stc_ipc_sema_t;
cy_en_ipcsema_status_t Cy_IPC_Sema_Init (uint32_t ipcChannel, uint32_t count, uint32_t memPtr[]);
cy_en_ipcsema_status_t Cy_IPC_Sema_InitExt(uint32_t ipcChannel, cy_stc_ipc_sema_t *ipcSema);
cy_en_ipcsema_status_t Cy_IPC_Sema_Set (uint32_t semaNumber, _Bool preemptable);
cy_en_ipcsema_status_t Cy_IPC_Sema_Clear (uint32_t semaNumber, _Bool preemptable);
cy_en_ipcsema_status_t Cy_IPC_Sema_Status (uint32_t semaNumber);
uint32_t Cy_IPC_Sema_GetMaxSems(void);
typedef enum
{
    CY_LPCOMP_OUT_PULSE = 0u,
    CY_LPCOMP_OUT_DIRECT = 1u,
    CY_LPCOMP_OUT_SYNC = 2u
} cy_en_lpcomp_out_t;
typedef enum
{
    CY_LPCOMP_HYST_ENABLE = 1u,
    CY_LPCOMP_HYST_DISABLE = 0u
} cy_en_lpcomp_hyst_t;
typedef enum
{
    CY_LPCOMP_CHANNEL_0 = 0x1u,
    CY_LPCOMP_CHANNEL_1 = 0x2u
} cy_en_lpcomp_channel_t;
typedef enum
{
    CY_LPCOMP_INTR_DISABLE = 0u,
    CY_LPCOMP_INTR_RISING = 1u,
    CY_LPCOMP_INTR_FALLING = 2u,
    CY_LPCOMP_INTR_BOTH = 3u
} cy_en_lpcomp_int_t;
typedef enum
{
    CY_LPCOMP_MODE_OFF = 0u,
    CY_LPCOMP_MODE_ULP = 1u,
    CY_LPCOMP_MODE_LP = 2u,
    CY_LPCOMP_MODE_NORMAL = 3u
} cy_en_lpcomp_pwr_t;
typedef enum
{
    CY_LPCOMP_SW_GPIO = 0x01u,
    CY_LPCOMP_SW_AMUXBUSA = 0x02u,
    CY_LPCOMP_SW_AMUXBUSB = 0x04u,
    CY_LPCOMP_SW_LOCAL_VREF = 0x08u
} cy_en_lpcomp_inputs_t;
typedef enum
{
    CY_LPCOMP_SUCCESS = 0x00u,
    CY_LPCOMP_BAD_PARAM = ((uint32_t)((uint32_t)((0x23u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01u,
    CY_LPCOMP_TRIMM_ERR = ((uint32_t)((uint32_t)((0x23u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02u,
} cy_en_lpcomp_status_t;
typedef struct {
    cy_en_lpcomp_out_t outputMode;
    cy_en_lpcomp_hyst_t hysteresis;
    cy_en_lpcomp_pwr_t power;
    cy_en_lpcomp_int_t intType;
} cy_stc_lpcomp_config_t;
typedef struct {
    cy_en_lpcomp_int_t intType[(2u)];
    cy_en_lpcomp_pwr_t power[(2u)];
} cy_stc_lpcomp_context_t;
cy_en_lpcomp_status_t Cy_LPComp_Init_Ext(LPCOMP_Type *base, cy_en_lpcomp_channel_t channel, const cy_stc_lpcomp_config_t *config,
                                        cy_stc_lpcomp_context_t *context);
void Cy_LPComp_Enable_Ext(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel, cy_stc_lpcomp_context_t *context);
void Cy_LPComp_Disable_Ext(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel, cy_stc_lpcomp_context_t *context);
cy_en_lpcomp_status_t Cy_LPComp_Init(LPCOMP_Type *base, cy_en_lpcomp_channel_t channel, const cy_stc_lpcomp_config_t *config);
void Cy_LPComp_Enable(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel);
void Cy_LPComp_Disable(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel);
static inline void Cy_LPComp_GlobalEnable(LPCOMP_Type *base);
static inline void Cy_LPComp_GlobalDisable(LPCOMP_Type *base);
static inline void Cy_LPComp_UlpReferenceEnable(LPCOMP_Type *base);
static inline void Cy_LPComp_UlpReferenceDisable(LPCOMP_Type *base);
static inline uint32_t Cy_LPComp_GetCompare(LPCOMP_Type const * base, cy_en_lpcomp_channel_t channel);
void Cy_LPComp_SetPower_Ext(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel, cy_en_lpcomp_pwr_t power,
                           cy_stc_lpcomp_context_t *context);
void Cy_LPComp_SetPower(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel, cy_en_lpcomp_pwr_t power);
void Cy_LPComp_SetHysteresis(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel, cy_en_lpcomp_hyst_t hysteresis);
void Cy_LPComp_SetInputs(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel, cy_en_lpcomp_inputs_t inputP, cy_en_lpcomp_inputs_t inputN);
void Cy_LPComp_SetOutputMode(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel, cy_en_lpcomp_out_t outType);
void Cy_LPComp_SetInterruptTriggerMode_Ext(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel, cy_en_lpcomp_int_t intType,
                                          cy_stc_lpcomp_context_t *context);
void Cy_LPComp_SetInterruptTriggerMode(LPCOMP_Type* base, cy_en_lpcomp_channel_t channel, cy_en_lpcomp_int_t intType);
static inline uint32_t Cy_LPComp_GetInterruptStatus(LPCOMP_Type const * base);
static inline void Cy_LPComp_ClearInterrupt(LPCOMP_Type* base, uint32_t interrupt);
static inline void Cy_LPComp_SetInterrupt(LPCOMP_Type* base, uint32_t interrupt);
static inline uint32_t Cy_LPComp_GetInterruptMask(LPCOMP_Type const * base);
static inline void Cy_LPComp_SetInterruptMask(LPCOMP_Type* base, uint32_t interrupt);
static inline uint32_t Cy_LPComp_GetInterruptStatusMasked(LPCOMP_Type const * base);
static inline void Cy_LPComp_ConnectULPReference(LPCOMP_Type *base, cy_en_lpcomp_channel_t channel);
cy_en_syspm_status_t Cy_LPComp_DeepSleepCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
cy_en_syspm_status_t Cy_LPComp_HibernateCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
static inline void Cy_LPComp_GlobalEnable(LPCOMP_Type* base)
{
    (((LPCOMP_Type *)(base))->CONFIG) |= 0x80000000UL;
}
static inline void Cy_LPComp_GlobalDisable(LPCOMP_Type *base)
{
    (((LPCOMP_Type *)(base))->CONFIG) &= (uint32_t) ~0x80000000UL;
}
static inline void Cy_LPComp_UlpReferenceEnable(LPCOMP_Type *base)
{
    (((LPCOMP_Type *)(base))->CONFIG) |= 0x40000000UL;
}
static inline void Cy_LPComp_UlpReferenceDisable(LPCOMP_Type *base)
{
    (((LPCOMP_Type *)(base))->CONFIG) &= (uint32_t) ~0x40000000UL;
}
static inline uint32_t Cy_LPComp_GetCompare(LPCOMP_Type const * base, cy_en_lpcomp_channel_t channel)
{
    uint32_t result;
    do { if(!((((channel) == CY_LPCOMP_CHANNEL_0) || ((channel) == CY_LPCOMP_CHANNEL_1)))) { CY_HALT(); } } while (0);
    if (CY_LPCOMP_CHANNEL_0 == channel)
    {
        result = (((uint32_t)((((LPCOMP_Type *)(base))->STATUS)) & 0x1UL) >> 0UL);
    }
    else
    {
        result = (((uint32_t)((((LPCOMP_Type *)(base))->STATUS)) & 0x10000UL) >> 16UL);
    }
    return (result);
}
static inline void Cy_LPComp_SetInterruptMask(LPCOMP_Type* base, uint32_t interrupt)
{
    do { if(!((((interrupt) == (0x1UL)) || ((interrupt) == (0x2UL)) || ((interrupt) == ((0x1UL) | (0x2UL)))))) { CY_HALT(); } } while (0);
    (((LPCOMP_Type *)(base))->INTR_MASK) |= interrupt;
}
static inline uint32_t Cy_LPComp_GetInterruptMask(LPCOMP_Type const * base)
{
    return ((((LPCOMP_Type *)(base))->INTR_MASK));
}
static inline uint32_t Cy_LPComp_GetInterruptStatusMasked(LPCOMP_Type const * base)
{
    return ((((LPCOMP_Type *)(base))->INTR_MASKED));
}
static inline uint32_t Cy_LPComp_GetInterruptStatus(LPCOMP_Type const * base)
{
    return ((((uint32_t)((((LPCOMP_Type *)(base))->INTR)) & (0x1UL | 0x2UL)) >> (0UL)));
}
static inline void Cy_LPComp_ClearInterrupt(LPCOMP_Type* base, uint32_t interrupt)
{
    do { if(!((((interrupt) == (0x1UL)) || ((interrupt) == (0x2UL)) || ((interrupt) == ((0x1UL) | (0x2UL)))))) { CY_HALT(); } } while (0);
    (((LPCOMP_Type *)(base))->INTR) |= interrupt;
    (void) (((LPCOMP_Type *)(base))->INTR);
}
static inline void Cy_LPComp_SetInterrupt(LPCOMP_Type* base, uint32_t interrupt)
{
    do { if(!((((interrupt) == (0x1UL)) || ((interrupt) == (0x2UL)) || ((interrupt) == ((0x1UL) | (0x2UL)))))) { CY_HALT(); } } while (0);
    (((LPCOMP_Type *)(base))->INTR_SET) = interrupt;
}
static inline void Cy_LPComp_ConnectULPReference(LPCOMP_Type *base, cy_en_lpcomp_channel_t channel)
{
    do { if(!((((channel) == CY_LPCOMP_CHANNEL_0) || ((channel) == CY_LPCOMP_CHANNEL_1)))) { CY_HALT(); } } while (0);
    if (CY_LPCOMP_CHANNEL_0 == channel)
    {
        (((LPCOMP_Type *)(base))->CMP0_SW_CLEAR) = (0x10UL | 0x20UL | 0x40UL | 0x80UL);
        (((LPCOMP_Type *)(base))->CMP0_SW) = ((((((LPCOMP_Type *)(base))->CMP0_SW)) & ((uint32_t)(~(0x80UL)))) | ((((uint32_t)((1u)) << 7UL) & 0x80UL)));
    }
    else
    {
        (((LPCOMP_Type *)(base))->CMP1_SW_CLEAR) = (0x10UL | 0x20UL | 0x40UL | 0x80UL);
        (((LPCOMP_Type *)(base))->CMP1_SW) = ((((((LPCOMP_Type *)(base))->CMP1_SW)) & ((uint32_t)(~(0x80UL)))) | ((((uint32_t)((1u)) << 7UL) & 0x80UL)));
    }
}
typedef enum
{
    CY_SYSTICK_CLOCK_SOURCE_CLK_LF = 0u,
    CY_SYSTICK_CLOCK_SOURCE_CLK_IMO = 1u,
    CY_SYSTICK_CLOCK_SOURCE_CLK_ECO = 2u,
    CY_SYSTICK_CLOCK_SOURCE_CLK_TIMER = 3u,
    CY_SYSTICK_CLOCK_SOURCE_CLK_CPU = 4u,
} cy_en_systick_clock_source_t;
typedef void (*Cy_SysTick_Callback)(void);
void Cy_SysTick_Init(cy_en_systick_clock_source_t clockSource, uint32_t interval);
void Cy_SysTick_Enable(void);
void Cy_SysTick_Disable(void);
Cy_SysTick_Callback Cy_SysTick_SetCallback(uint32_t number, Cy_SysTick_Callback function);
Cy_SysTick_Callback Cy_SysTick_GetCallback(uint32_t number);
void Cy_SysTick_SetClockSource(cy_en_systick_clock_source_t clockSource);
cy_en_systick_clock_source_t Cy_SysTick_GetClockSource(void);
void Cy_SysTick_EnableInterrupt(void);
void Cy_SysTick_DisableInterrupt(void);
void Cy_SysTick_SetReload(uint32_t value);
uint32_t Cy_SysTick_GetReload(void);
uint32_t Cy_SysTick_GetValue(void);
void Cy_SysTick_Clear(void);
uint32_t Cy_SysTick_GetCountFlag(void);
typedef enum
{
    CY_LVD_THRESHOLD_1_2_V = 0x0U,
    CY_LVD_THRESHOLD_1_4_V = 0x1U,
    CY_LVD_THRESHOLD_1_6_V = 0x2U,
    CY_LVD_THRESHOLD_1_8_V = 0x3U,
    CY_LVD_THRESHOLD_2_0_V = 0x4U,
    CY_LVD_THRESHOLD_2_1_V = 0x5U,
    CY_LVD_THRESHOLD_2_2_V = 0x6U,
    CY_LVD_THRESHOLD_2_3_V = 0x7U,
    CY_LVD_THRESHOLD_2_4_V = 0x8U,
    CY_LVD_THRESHOLD_2_5_V = 0x9U,
    CY_LVD_THRESHOLD_2_6_V = 0xAU,
    CY_LVD_THRESHOLD_2_7_V = 0xBU,
    CY_LVD_THRESHOLD_2_8_V = 0xCU,
    CY_LVD_THRESHOLD_2_9_V = 0xDU,
    CY_LVD_THRESHOLD_3_0_V = 0xEU,
    CY_LVD_THRESHOLD_3_1_V = 0xFU
} cy_en_lvd_tripsel_t;
typedef enum
{
    CY_LVD_INTR_DISABLE = 0x0U,
    CY_LVD_INTR_RISING = 0x1U,
    CY_LVD_INTR_FALLING = 0x2U,
    CY_LVD_INTR_BOTH = 0x3U,
} cy_en_lvd_intr_config_t;
typedef enum
{
    CY_LVD_STATUS_BELOW = 0x0U,
    CY_LVD_STATUS_ABOVE = 0x1U,
} cy_en_lvd_status_t;
typedef enum
{
    CY_LVD_SOURCE_VDDD = 0x0U,
    CY_LVD_SOURCE_AMUXBUSA = 0x1U,
    CY_LVD_SOURCE_RES = 0x2U,
    CY_LVD_SOURCE_VDDIO = 0x3U,
    CY_LVD_SOURCE_AMUXBUSB = 0x4U,
} cy_en_lvd_source_t;
typedef enum
{
    CY_LVD_ACTION_INTERRUPT = 0x0U,
    CY_LVD_ACTION_FAULT = 0x1U,
} cy_en_lvd_action_config_t;
static inline void Cy_LVD_Enable(void);
static inline void Cy_LVD_Disable(void);
static inline void Cy_LVD_SetThreshold(cy_en_lvd_tripsel_t threshold);
static inline cy_en_lvd_status_t Cy_LVD_GetStatus(void);
static inline uint32_t Cy_LVD_GetInterruptStatus(void);
static inline void Cy_LVD_ClearInterrupt(void);
static inline void Cy_LVD_SetInterrupt(void);
static inline uint32_t Cy_LVD_GetInterruptMask(void);
static inline void Cy_LVD_SetInterruptMask(void);
static inline void Cy_LVD_ClearInterruptMask(void);
static inline uint32_t Cy_LVD_GetInterruptStatusMasked(void);
static inline void Cy_LVD_SetInterruptConfig(cy_en_lvd_intr_config_t lvdInterruptConfig);
cy_en_syspm_status_t Cy_LVD_DeepSleepCallback(cy_stc_syspm_callback_params_t * callbackParams, cy_en_syspm_callback_mode_t mode);
static inline void Cy_LVD_Enable(void)
{
        (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->PWR_LVD_CTL) |= (0x80UL);
}
static inline void Cy_LVD_Disable(void)
{
        (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->PWR_LVD_CTL) &= (uint32_t) ~(0x80UL);
}
static inline void Cy_LVD_SetThreshold(cy_en_lvd_tripsel_t threshold)
{
    do { if(!((((threshold) == CY_LVD_THRESHOLD_1_2_V) || ((threshold) == CY_LVD_THRESHOLD_1_4_V) || ((threshold) == CY_LVD_THRESHOLD_1_6_V) || ((threshold) == CY_LVD_THRESHOLD_1_8_V) || ((threshold) == CY_LVD_THRESHOLD_2_0_V) || ((threshold) == CY_LVD_THRESHOLD_2_1_V) || ((threshold) == CY_LVD_THRESHOLD_2_2_V) || ((threshold) == CY_LVD_THRESHOLD_2_3_V) || ((threshold) == CY_LVD_THRESHOLD_2_4_V) || ((threshold) == CY_LVD_THRESHOLD_2_5_V) || ((threshold) == CY_LVD_THRESHOLD_2_6_V) || ((threshold) == CY_LVD_THRESHOLD_2_7_V) || ((threshold) == CY_LVD_THRESHOLD_2_8_V) || ((threshold) == CY_LVD_THRESHOLD_2_9_V) || ((threshold) == CY_LVD_THRESHOLD_3_0_V) || ((threshold) == CY_LVD_THRESHOLD_3_1_V)))) { CY_HALT(); } } while (0);
        (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->PWR_LVD_CTL) = ((((((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->PWR_LVD_CTL)) & ((uint32_t)(~(0xFUL)))) | ((((uint32_t)(threshold) << 0UL) & 0xFUL)));
}
static inline cy_en_lvd_status_t Cy_LVD_GetStatus(void)
{
    do{}while(0);
    return ((cy_en_lvd_status_t) (((uint32_t)((((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->PWR_LVD_STATUS)) & 0x1UL) >> 0UL));
}
static inline uint32_t Cy_LVD_GetInterruptStatus(void)
{
    return ((((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR) & (0x2UL));
}
static inline void Cy_LVD_ClearInterrupt(void)
{
        (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR) = (0x2UL);
    (void) (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR);
}
static inline void Cy_LVD_SetInterrupt(void)
{
        (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR_SET) = (0x2UL);
}
static inline uint32_t Cy_LVD_GetInterruptMask(void)
{
    return ((((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR_MASK) & (0x2UL));
}
static inline void Cy_LVD_SetInterruptMask(void)
{
        (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR_MASK) |= (0x2UL);
}
static inline void Cy_LVD_ClearInterruptMask(void)
{
        (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR_MASK) &= (uint32_t) ~(0x2UL);
}
static inline uint32_t Cy_LVD_GetInterruptStatusMasked(void)
{
    return ((((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR_MASKED) & (0x2UL));
}
static inline void Cy_LVD_SetInterruptConfig(cy_en_lvd_intr_config_t lvdInterruptConfig)
{
    do { if(!((((lvdInterruptConfig) == CY_LVD_INTR_DISABLE) || ((lvdInterruptConfig) == CY_LVD_INTR_RISING) || ((lvdInterruptConfig) == CY_LVD_INTR_FALLING) || ((lvdInterruptConfig) == CY_LVD_INTR_BOTH)))) { CY_HALT(); } } while (0);
             (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR_CFG) = ((((((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR_CFG)) & ((uint32_t)(~(0x3UL)))) | ((((uint32_t)(lvdInterruptConfig) << 0UL) & 0x3UL)));
    (void) lvdInterruptConfig;
}
typedef enum
{
    CY_MCWDT_COUNTER0,
    CY_MCWDT_COUNTER1,
    CY_MCWDT_COUNTER2
} cy_en_mcwdtctr_t;
typedef enum
{
    CY_MCWDT_MODE_NONE,
    CY_MCWDT_MODE_INT,
    CY_MCWDT_MODE_RESET,
    CY_MCWDT_MODE_INT_RESET
} cy_en_mcwdtmode_t;
typedef enum
{
    CY_MCWDT_CASCADE_NONE,
    CY_MCWDT_CASCADE_C0C1,
    CY_MCWDT_CASCADE_C1C2,
    CY_MCWDT_CASCADE_BOTH
} cy_en_mcwdtcascade_t;
typedef enum
{
    CY_MCWDT_SUCCESS = 0x00u,
    CY_MCWDT_BAD_PARAM = ((uint32_t)((uint32_t)((0x35u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01u,
} cy_en_mcwdt_status_t;
typedef struct
{
    uint16_t c0Match;
    uint16_t c1Match;
    uint8_t c0Mode;
    uint8_t c1Mode;
    uint8_t c2ToggleBit;
    uint8_t c2Mode;
    _Bool c0ClearOnMatch;
    _Bool c1ClearOnMatch;
    _Bool c0c1Cascade;
    _Bool c1c2Cascade;
} cy_stc_mcwdt_config_t;
cy_en_mcwdt_status_t Cy_MCWDT_Init(MCWDT_STRUCT_Type *base, cy_stc_mcwdt_config_t const *config);
                void Cy_MCWDT_DeInit(MCWDT_STRUCT_Type *base);
static inline void Cy_MCWDT_Enable(MCWDT_STRUCT_Type *base, uint32_t counters, uint16_t waitUs);
static inline void Cy_MCWDT_Disable(MCWDT_STRUCT_Type *base, uint32_t counters, uint16_t waitUs);
static inline uint32_t Cy_MCWDT_GetEnabledStatus(MCWDT_STRUCT_Type const *base, cy_en_mcwdtctr_t counter);
static inline void Cy_MCWDT_Lock(MCWDT_STRUCT_Type *base);
static inline void Cy_MCWDT_Unlock(MCWDT_STRUCT_Type *base);
static inline uint32_t Cy_MCWDT_GetLockedStatus(MCWDT_STRUCT_Type const *base);
static inline void Cy_MCWDT_SetMode(MCWDT_STRUCT_Type *base, cy_en_mcwdtctr_t counter, cy_en_mcwdtmode_t mode);
static inline cy_en_mcwdtmode_t Cy_MCWDT_GetMode(MCWDT_STRUCT_Type const *base, cy_en_mcwdtctr_t counter);
static inline void Cy_MCWDT_SetClearOnMatch(MCWDT_STRUCT_Type *base, cy_en_mcwdtctr_t counter, uint32_t enable);
static inline uint32_t Cy_MCWDT_GetClearOnMatch(MCWDT_STRUCT_Type const *base, cy_en_mcwdtctr_t counter);
static inline void Cy_MCWDT_SetCascade(MCWDT_STRUCT_Type *base, cy_en_mcwdtcascade_t cascade);
static inline cy_en_mcwdtcascade_t Cy_MCWDT_GetCascade(MCWDT_STRUCT_Type const *base);
static inline void Cy_MCWDT_SetMatch(MCWDT_STRUCT_Type *base, cy_en_mcwdtctr_t counter, uint32_t match, uint16_t waitUs);
static inline uint32_t Cy_MCWDT_GetMatch(MCWDT_STRUCT_Type const *base, cy_en_mcwdtctr_t counter);
uint32_t Cy_MCWDT_GetCountCascaded(MCWDT_STRUCT_Type const *base);
static inline void Cy_MCWDT_SetToggleBit(MCWDT_STRUCT_Type *base, uint32_t bit);
static inline uint32_t Cy_MCWDT_GetToggleBit(MCWDT_STRUCT_Type const *base);
static inline uint32_t Cy_MCWDT_GetCount(MCWDT_STRUCT_Type const *base, cy_en_mcwdtctr_t counter);
static inline void Cy_MCWDT_ResetCounters(MCWDT_STRUCT_Type *base, uint32_t counters, uint16_t waitUs);
static inline uint32_t Cy_MCWDT_GetInterruptStatus(MCWDT_STRUCT_Type const *base);
static inline void Cy_MCWDT_ClearInterrupt(MCWDT_STRUCT_Type *base, uint32_t counters);
static inline void Cy_MCWDT_SetInterrupt(MCWDT_STRUCT_Type *base, uint32_t counters);
static inline uint32_t Cy_MCWDT_GetInterruptMask(MCWDT_STRUCT_Type const *base);
static inline void Cy_MCWDT_SetInterruptMask(MCWDT_STRUCT_Type *base, uint32_t counters);
static inline uint32_t Cy_MCWDT_GetInterruptStatusMasked(MCWDT_STRUCT_Type const *base);
static inline void Cy_MCWDT_Enable(MCWDT_STRUCT_Type *base, uint32_t counters, uint16_t waitUs)
{
    uint32_t enableCounters;
    do { if(!((0U == ((counters) & (uint32_t)~((1UL << (0u)) | (1UL << (1u)) | (1UL << (2u))))))) { CY_HALT(); } } while (0);
    enableCounters = ((0UL != (counters & (1UL << (0u)))) ? 0x1UL : 0UL) |
                     ((0UL != (counters & (1UL << (1u)))) ? 0x100UL : 0UL) |
                     ((0UL != (counters & (1UL << (2u)))) ? 0x10000UL : 0UL);
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_CTL) |= enableCounters;
    Cy_SysLib_DelayUs(waitUs);
}
static inline void Cy_MCWDT_Disable(MCWDT_STRUCT_Type *base, uint32_t counters, uint16_t waitUs)
{
    uint32_t disableCounters;
    do { if(!((0U == ((counters) & (uint32_t)~((1UL << (0u)) | (1UL << (1u)) | (1UL << (2u))))))) { CY_HALT(); } } while (0);
    disableCounters = ((0UL != (counters & (1UL << (0u)))) ? 0x1UL : 0UL) |
                      ((0UL != (counters & (1UL << (1u)))) ? 0x100UL : 0UL) |
                      ((0UL != (counters & (1UL << (2u)))) ? 0x10000UL : 0UL);
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_CTL) &= ~disableCounters;
    Cy_SysLib_DelayUs(waitUs);
}
static inline uint32_t Cy_MCWDT_GetEnabledStatus(MCWDT_STRUCT_Type const *base, cy_en_mcwdtctr_t counter)
{
    uint32_t status = 0u;
    do { if(!(((CY_MCWDT_COUNTER0 == (counter)) || (CY_MCWDT_COUNTER1 == (counter)) || (CY_MCWDT_COUNTER2 == (counter))))) { CY_HALT(); } } while (0);
    switch (counter)
    {
        case CY_MCWDT_COUNTER0:
            status = (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CTL)) & 0x2UL) >> 1UL);
            break;
        case CY_MCWDT_COUNTER1:
            status = (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CTL)) & 0x200UL) >> 9UL);
            break;
        case CY_MCWDT_COUNTER2:
            status = (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CTL)) & 0x20000UL) >> 17UL);
            break;
        default:
            do { if(!(0u != 0u)) { CY_HALT(); } } while (0);
        break;
    }
    return (status);
}
static inline void Cy_MCWDT_Lock(MCWDT_STRUCT_Type *base)
{
    uint32_t interruptState;
    interruptState = Cy_SysLib_EnterCriticalSection();
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_LOCK) = ((((((MCWDT_STRUCT_Type *)(base))->MCWDT_LOCK)) & ((uint32_t)(~(0xC0000000UL)))) | ((((uint32_t)((uint32_t)(3u)) << 30UL) & 0xC0000000UL)));
    Cy_SysLib_ExitCriticalSection(interruptState);
}
static inline void Cy_MCWDT_Unlock(MCWDT_STRUCT_Type *base)
{
    uint32_t interruptState;
    interruptState = Cy_SysLib_EnterCriticalSection();
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_LOCK) = ((((((MCWDT_STRUCT_Type *)(base))->MCWDT_LOCK)) & ((uint32_t)(~(0xC0000000UL)))) | ((((uint32_t)((uint32_t)(1u)) << 30UL) & 0xC0000000UL)));
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_LOCK) = ((((((MCWDT_STRUCT_Type *)(base))->MCWDT_LOCK)) & ((uint32_t)(~(0xC0000000UL)))) | ((((uint32_t)((uint32_t)(2u)) << 30UL) & 0xC0000000UL)));
    Cy_SysLib_ExitCriticalSection(interruptState);
}
static inline uint32_t Cy_MCWDT_GetLockedStatus(MCWDT_STRUCT_Type const *base)
{
    return ((0UL != ((((MCWDT_STRUCT_Type *)(base))->MCWDT_LOCK) & 0xC0000000UL)) ? 1UL : 0UL);
}
static inline void Cy_MCWDT_SetMode(MCWDT_STRUCT_Type *base, cy_en_mcwdtctr_t counter, cy_en_mcwdtmode_t mode)
{
    uint32_t mask, shift;
    do { if(!(((CY_MCWDT_COUNTER0 == (counter)) || (CY_MCWDT_COUNTER1 == (counter)) || (CY_MCWDT_COUNTER2 == (counter))))) { CY_HALT(); } } while (0);
    do { if(!(((CY_MCWDT_MODE_NONE == (mode)) || (CY_MCWDT_MODE_INT == (mode)) || (CY_MCWDT_MODE_RESET == (mode)) || (CY_MCWDT_MODE_INT_RESET == (mode))))) { CY_HALT(); } } while (0);
    shift = (8u) * ((uint32_t)counter);
    mask = (counter == CY_MCWDT_COUNTER2) ? (1u) : (3u);
    mask = mask << shift;
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG) = ((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG) & ~mask) | ((uint32_t) mode << shift);
}
static inline cy_en_mcwdtmode_t Cy_MCWDT_GetMode(MCWDT_STRUCT_Type const *base, cy_en_mcwdtctr_t counter)
{
    uint32_t mode, mask;
    do { if(!(((CY_MCWDT_COUNTER0 == (counter)) || (CY_MCWDT_COUNTER1 == (counter)) || (CY_MCWDT_COUNTER2 == (counter))))) { CY_HALT(); } } while (0);
    mask = (counter == CY_MCWDT_COUNTER2) ? (1u) : (3u);
    mode = ((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG) >> ((8u) * ((uint32_t)counter))) & mask;
    return ((cy_en_mcwdtmode_t) mode);
}
static inline void Cy_MCWDT_SetClearOnMatch(MCWDT_STRUCT_Type *base, cy_en_mcwdtctr_t counter, uint32_t enable)
{
    do { if(!(((CY_MCWDT_COUNTER0 == (counter)) || (CY_MCWDT_COUNTER1 == (counter)) || (CY_MCWDT_COUNTER2 == (counter))))) { CY_HALT(); } } while (0);
    do { if(!((1UL >= (enable)))) { CY_HALT(); } } while (0);
    if (CY_MCWDT_COUNTER0 == counter)
    {
        (((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG) = ((((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG)) & ((uint32_t)(~(0x4UL)))) | ((((uint32_t)(enable) << 2UL) & 0x4UL)));
    }
    else
    {
        (((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG) = ((((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG)) & ((uint32_t)(~(0x400UL)))) | ((((uint32_t)(enable) << 10UL) & 0x400UL)));
    }
}
static inline uint32_t Cy_MCWDT_GetClearOnMatch(MCWDT_STRUCT_Type const *base, cy_en_mcwdtctr_t counter)
{
    uint32_t getClear;
    do { if(!(((CY_MCWDT_COUNTER0 == (counter)) || (CY_MCWDT_COUNTER1 == (counter)) || (CY_MCWDT_COUNTER2 == (counter))))) { CY_HALT(); } } while (0);
    if (CY_MCWDT_COUNTER0 == counter)
    {
        getClear = (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG)) & 0x4UL) >> 2UL);
    }
    else
    {
        getClear = (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG)) & 0x400UL) >> 10UL);
    }
    return (getClear);
}
static inline void Cy_MCWDT_SetCascade(MCWDT_STRUCT_Type *base, cy_en_mcwdtcascade_t cascade)
{
    do { if(!(((CY_MCWDT_CASCADE_NONE == (cascade)) || (CY_MCWDT_CASCADE_C0C1 == (cascade)) || (CY_MCWDT_CASCADE_C1C2 == (cascade)) || (CY_MCWDT_CASCADE_BOTH == (cascade))))) { CY_HALT(); } } while (0);
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG) = ((((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG)) & ((uint32_t)(~(0x8UL)))) | ((((uint32_t)((uint32_t) cascade) << 3UL) & 0x8UL)));
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG) = ((((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG)) & ((uint32_t)(~(0x800UL)))) | ((((uint32_t)(((uint32_t) cascade >> 1u)) << 11UL) & 0x800UL)));
}
static inline cy_en_mcwdtcascade_t Cy_MCWDT_GetCascade(MCWDT_STRUCT_Type const *base)
{
    uint32_t cascade;
    cascade = ((((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG)) & 0x800UL) >> 11UL) << 1u) |
               (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG)) & 0x8UL) >> 3UL);
    return ((cy_en_mcwdtcascade_t) cascade);
}
static inline void Cy_MCWDT_SetMatch(MCWDT_STRUCT_Type *base, cy_en_mcwdtctr_t counter, uint32_t match, uint16_t waitUs)
{
    do { if(!(((CY_MCWDT_COUNTER0 == (counter)) || (CY_MCWDT_COUNTER1 == (counter)) || (CY_MCWDT_COUNTER2 == (counter))))) { CY_HALT(); } } while (0);
    do { if(!((((CY_MCWDT_COUNTER0 == counter) ? (((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG) & 0x4UL) > 0U) : (((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG) & 0x400UL) > 0U)) ? (1UL <= (match)) : 1))) { CY_HALT(); } } while (0);
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_MATCH) = (counter == CY_MCWDT_COUNTER0) ?
        ((((((MCWDT_STRUCT_Type *)(base))->MCWDT_MATCH)) & ((uint32_t)(~(0xFFFFUL)))) | ((((uint32_t)((match & 0xFFFFUL)) << 0UL) & 0xFFFFUL))) :
        ((((((MCWDT_STRUCT_Type *)(base))->MCWDT_MATCH)) & ((uint32_t)(~(0xFFFF0000UL)))) | ((((uint32_t)((match & 0xFFFFUL)) << 16UL) & 0xFFFF0000UL)));
    Cy_SysLib_DelayUs(waitUs);
}
static inline uint32_t Cy_MCWDT_GetMatch(MCWDT_STRUCT_Type const *base, cy_en_mcwdtctr_t counter)
{
    uint32_t match;
    do { if(!(((CY_MCWDT_COUNTER0 == (counter)) || (CY_MCWDT_COUNTER1 == (counter)) || (CY_MCWDT_COUNTER2 == (counter))))) { CY_HALT(); } } while (0);
    match = (counter == CY_MCWDT_COUNTER0) ? (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_MATCH)) & 0xFFFFUL) >> 0UL) :
                                          (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_MATCH)) & 0xFFFF0000UL) >> 16UL);
    return (match);
}
static inline void Cy_MCWDT_SetToggleBit(MCWDT_STRUCT_Type *base, uint32_t bit)
{
    do { if(!((31UL >= (bit)))) { CY_HALT(); } } while (0);
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG) = ((((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG)) & ((uint32_t)(~(0x1F000000UL)))) | ((((uint32_t)(bit) << 24UL) & 0x1F000000UL)));
}
static inline uint32_t Cy_MCWDT_GetToggleBit(MCWDT_STRUCT_Type const *base)
{
    return ((((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CONFIG)) & 0x1F000000UL) >> 24UL));
}
static inline uint32_t Cy_MCWDT_GetCount(MCWDT_STRUCT_Type const *base, cy_en_mcwdtctr_t counter)
{
    uint32_t countVal = 0u;
    do { if(!(((CY_MCWDT_COUNTER0 == (counter)) || (CY_MCWDT_COUNTER1 == (counter)) || (CY_MCWDT_COUNTER2 == (counter))))) { CY_HALT(); } } while (0);
    switch (counter)
    {
        case CY_MCWDT_COUNTER0:
            countVal = (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CNTLOW)) & 0xFFFFUL) >> 0UL);
            break;
        case CY_MCWDT_COUNTER1:
            countVal = (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CNTLOW)) & 0xFFFF0000UL) >> 16UL);
            break;
        case CY_MCWDT_COUNTER2:
            countVal = (((uint32_t)((((MCWDT_STRUCT_Type *)(base))->MCWDT_CNTHIGH)) & 0xFFFFFFFFUL) >> 0UL);
            break;
        default:
            do { if(!(0u != 0u)) { CY_HALT(); } } while (0);
            break;
    }
    return (countVal);
}
static inline void Cy_MCWDT_ResetCounters(MCWDT_STRUCT_Type *base, uint32_t counters, uint16_t waitUs)
{
    uint32_t resetCounters;
    do { if(!((0U == ((counters) & (uint32_t)~((1UL << (0u)) | (1UL << (1u)) | (1UL << (2u))))))) { CY_HALT(); } } while (0);
    resetCounters = ((0UL != (counters & (1UL << (0u)))) ? 0x8UL : 0UL) |
                    ((0UL != (counters & (1UL << (1u)))) ? 0x800UL : 0UL) |
                    ((0UL != (counters & (1UL << (2u)))) ? 0x80000UL : 0UL);
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_CTL) |= resetCounters;
    Cy_SysLib_DelayUs(waitUs);
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_CTL) |= resetCounters;
    Cy_SysLib_DelayUs(waitUs);
}
static inline uint32_t Cy_MCWDT_GetInterruptStatus(MCWDT_STRUCT_Type const *base)
{
    return ((((MCWDT_STRUCT_Type *)(base))->MCWDT_INTR));
}
static inline void Cy_MCWDT_ClearInterrupt(MCWDT_STRUCT_Type *base, uint32_t counters)
{
    do { if(!((0U == ((counters) & (uint32_t)~((1UL << (0u)) | (1UL << (1u)) | (1UL << (2u))))))) { CY_HALT(); } } while (0);
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_INTR) = counters;
    (void) (((MCWDT_STRUCT_Type *)(base))->MCWDT_INTR);
}
static inline void Cy_MCWDT_SetInterrupt(MCWDT_STRUCT_Type *base, uint32_t counters)
{
    do { if(!((0U == ((counters) & (uint32_t)~((1UL << (0u)) | (1UL << (1u)) | (1UL << (2u))))))) { CY_HALT(); } } while (0);
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_INTR_SET) = counters;
}
static inline uint32_t Cy_MCWDT_GetInterruptMask(MCWDT_STRUCT_Type const *base)
{
    return ((((MCWDT_STRUCT_Type *)(base))->MCWDT_INTR_MASK));
}
static inline void Cy_MCWDT_SetInterruptMask(MCWDT_STRUCT_Type *base, uint32_t counters)
{
    do { if(!((0U == ((counters) & (uint32_t)~((1UL << (0u)) | (1UL << (1u)) | (1UL << (2u))))))) { CY_HALT(); } } while (0);
    (((MCWDT_STRUCT_Type *)(base))->MCWDT_INTR_MASK) = counters;
}
static inline uint32_t Cy_MCWDT_GetInterruptStatusMasked(MCWDT_STRUCT_Type const *base)
{
    return ((((MCWDT_STRUCT_Type *)(base))->MCWDT_INTR_MASKED));
}
typedef enum
{
    CY_PDM_PCM_WLEN_16_BIT = 0U,
    CY_PDM_PCM_WLEN_18_BIT = 1U,
    CY_PDM_PCM_WLEN_20_BIT = 2U,
    CY_PDM_PCM_WLEN_24_BIT = 3U
} cy_en_pdm_pcm_word_len_t;
typedef enum
{
    CY_PDM_PCM_CLK_DIV_BYPASS = 0U,
    CY_PDM_PCM_CLK_DIV_1_2 = 1U,
    CY_PDM_PCM_CLK_DIV_1_3 = 2U,
    CY_PDM_PCM_CLK_DIV_1_4 = 3U
} cy_en_pdm_pcm_clk_div_t;
typedef enum
{
    CY_PDM_PCM_OUT_CHAN_LEFT = 1U,
    CY_PDM_PCM_OUT_CHAN_RIGHT = 2U,
    CY_PDM_PCM_OUT_STEREO = 3U
} cy_en_pdm_pcm_out_t;
typedef enum
{
    CY_PDM_PCM_CHAN_LEFT = 0U,
    CY_PDM_PCM_CHAN_RIGHT = 1U
} cy_en_pdm_pcm_chan_select_t;
typedef enum
{
    CY_PDM_PCM_ATTN_12_DB = 0U,
    CY_PDM_PCM_ATTN_10_5_DB = 1U,
    CY_PDM_PCM_ATTN_9_DB = 2U,
    CY_PDM_PCM_ATTN_7_5_DB = 3U,
    CY_PDM_PCM_ATTN_6_DB = 4U,
    CY_PDM_PCM_ATTN_4_5_DB = 5U,
    CY_PDM_PCM_ATTN_3_DB = 6U,
    CY_PDM_PCM_ATTN_1_5_DB = 7U,
    CY_PDM_PCM_BYPASS = 8U,
    CY_PDM_PCM_GAIN_1_5_DB = 9U,
    CY_PDM_PCM_GAIN_3_DB = 10U,
    CY_PDM_PCM_GAIN_4_5_DB = 11U,
    CY_PDM_PCM_GAIN_6_DB = 12U,
    CY_PDM_PCM_GAIN_7_5_DB = 13U,
    CY_PDM_PCM_GAIN_9_DB = 14U,
    CY_PDM_PCM_GAIN_10_5_DB = 15U
} cy_en_pdm_pcm_gain_t;
typedef enum
{
    CY_PDM_PCM_SOFT_MUTE_CYCLES_64 = 0U,
    CY_PDM_PCM_SOFT_MUTE_CYCLES_96 = 1U,
    CY_PDM_PCM_SOFT_MUTE_CYCLES_128 = 2U,
    CY_PDM_PCM_SOFT_MUTE_CYCLES_160 = 3U,
    CY_PDM_PCM_SOFT_MUTE_CYCLES_192 = 4U,
    CY_PDM_PCM_SOFT_MUTE_CYCLES_256 = 5U,
    CY_PDM_PCM_SOFT_MUTE_CYCLES_384 = 6U,
    CY_PDM_PCM_SOFT_MUTE_CYCLES_512 = 7U
} cy_en_pdm_pcm_s_cycles_t;
typedef enum
{
    CY_PDM_PCM_SUCCESS = 0x00UL,
    CY_PDM_PCM_BAD_PARAM = ((uint32_t)((uint32_t)((0x26u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01UL
} cy_en_pdm_pcm_status_t;
typedef struct
{
    cy_en_pdm_pcm_clk_div_t clkDiv;
    cy_en_pdm_pcm_clk_div_t mclkDiv;
    uint8_t ckoDiv;
    uint8_t ckoDelay;
    uint8_t sincDecRate;
    cy_en_pdm_pcm_out_t chanSelect;
    _Bool chanSwapEnable;
    uint8_t highPassFilterGain;
    _Bool highPassDisable;
    cy_en_pdm_pcm_s_cycles_t softMuteCycles;
    uint32_t softMuteFineGain;
    _Bool softMuteEnable;
    cy_en_pdm_pcm_word_len_t wordLen;
    _Bool signExtension;
    cy_en_pdm_pcm_gain_t gainLeft;
    cy_en_pdm_pcm_gain_t gainRight;
    uint8_t rxFifoTriggerLevel;
    _Bool dmaTriggerEnable;
    uint32_t interruptMask;
} cy_stc_pdm_pcm_config_t;
cy_en_pdm_pcm_status_t Cy_PDM_PCM_Init(PDM_Type * base, cy_stc_pdm_pcm_config_t const * config);
                void Cy_PDM_PCM_DeInit(PDM_Type * base);
                void Cy_PDM_PCM_SetGain(PDM_Type * base, cy_en_pdm_pcm_chan_select_t chan, cy_en_pdm_pcm_gain_t gain);
cy_en_pdm_pcm_gain_t Cy_PDM_PCM_GetGain(PDM_Type const * base, cy_en_pdm_pcm_chan_select_t chan);
cy_en_syspm_status_t Cy_PDM_PCM_DeepSleepCallback(cy_stc_syspm_callback_params_t const * callbackParams, cy_en_syspm_callback_mode_t mode);
static inline void Cy_PDM_PCM_Enable(PDM_Type * base);
static inline void Cy_PDM_PCM_Disable(PDM_Type * base);
static inline void Cy_PDM_PCM_SetInterruptMask(PDM_Type * base, uint32_t interrupt);
static inline uint32_t Cy_PDM_PCM_GetInterruptMask(PDM_Type const * base);
static inline uint32_t Cy_PDM_PCM_GetInterruptStatusMasked(PDM_Type const * base);
static inline uint32_t Cy_PDM_PCM_GetInterruptStatus(PDM_Type const * base);
static inline void Cy_PDM_PCM_ClearInterrupt(PDM_Type * base, uint32_t interrupt);
static inline void Cy_PDM_PCM_SetInterrupt(PDM_Type * base, uint32_t interrupt);
static inline uint8_t Cy_PDM_PCM_GetNumInFifo(PDM_Type const * base);
static inline void Cy_PDM_PCM_ClearFifo(PDM_Type * base);
static inline uint32_t Cy_PDM_PCM_ReadFifo(PDM_Type const * base);
static inline void Cy_PDM_PCM_EnableSoftMute(PDM_Type * base);
static inline void Cy_PDM_PCM_DisableSoftMute(PDM_Type * base);
static inline void Cy_PDM_PCM_FreezeFifo(PDM_Type * base);
static inline void Cy_PDM_PCM_UnfreezeFifo(PDM_Type * base);
static inline uint32_t Cy_PDM_PCM_ReadFifoSilent(PDM_Type const * base);
static inline void Cy_PDM_PCM_Enable(PDM_Type * base)
{
    (((PDM_V1_Type*)(base))->CMD) |= 0x1UL;
}
static inline void Cy_PDM_PCM_Disable(PDM_Type * base)
{
    (((PDM_V1_Type*)(base))->CMD) &= (uint32_t) ~0x1UL;
}
static inline uint32_t Cy_PDM_PCM_GetCurrentState(PDM_Type const * base)
{
    return ((((PDM_V1_Type*)(base))->CMD));
}
static inline void Cy_PDM_PCM_SetInterruptMask(PDM_Type * base, uint32_t interrupt)
{
    do { if(!((0UL == ((interrupt) & ((uint32_t) ~((0x10000UL) | (0x40000UL) | (0x200000UL) | (0x400000UL))))))) { CY_HALT(); } } while (0);
    (((PDM_V1_Type*)(base))->INTR_MASK) = interrupt;
}
static inline uint32_t Cy_PDM_PCM_GetInterruptMask(PDM_Type const * base)
{
    return ((((PDM_V1_Type*)(base))->INTR_MASK));
}
static inline uint32_t Cy_PDM_PCM_GetInterruptStatusMasked(PDM_Type const * base)
{
    return ((((PDM_V1_Type*)(base))->INTR_MASKED));
}
static inline uint32_t Cy_PDM_PCM_GetInterruptStatus(PDM_Type const * base)
{
    return ((((PDM_V1_Type*)(base))->INTR));
}
static inline void Cy_PDM_PCM_ClearInterrupt(PDM_Type * base, uint32_t interrupt)
{
    do { if(!((0UL == ((interrupt) & ((uint32_t) ~((0x10000UL) | (0x40000UL) | (0x200000UL) | (0x400000UL))))))) { CY_HALT(); } } while (0);
    (((PDM_V1_Type*)(base))->INTR) = interrupt;
    (void) (((PDM_V1_Type*)(base))->INTR);
}
static inline void Cy_PDM_PCM_SetInterrupt(PDM_Type * base, uint32_t interrupt)
{
    do { if(!((0UL == ((interrupt) & ((uint32_t) ~((0x10000UL) | (0x40000UL) | (0x200000UL) | (0x400000UL))))))) { CY_HALT(); } } while (0);
    (((PDM_V1_Type*)(base))->INTR_SET) = interrupt;
}
static inline uint8_t Cy_PDM_PCM_GetNumInFifo(PDM_Type const * base)
{
    return (uint8_t) ((((uint32_t)((((PDM_V1_Type*)(base))->RX_FIFO_STATUS)) & 0xFFUL) >> 0UL));
}
static inline void Cy_PDM_PCM_ClearFifo(PDM_Type * base)
{
    (((PDM_V1_Type*)(base))->RX_FIFO_CTL) |= 0x10000UL;
    (((PDM_V1_Type*)(base))->RX_FIFO_CTL) &= (uint32_t) ~0x10000UL;
}
static inline uint32_t Cy_PDM_PCM_ReadFifo(PDM_Type const * base)
{
    return ((((PDM_V1_Type*)(base))->RX_FIFO_RD));
}
static inline void Cy_PDM_PCM_EnableSoftMute(PDM_Type * base)
{
    (((PDM_V1_Type*)(base))->CTL) |= 0x10000UL;
}
static inline void Cy_PDM_PCM_DisableSoftMute(PDM_Type * base)
{
    (((PDM_V1_Type*)(base))->CTL) &= (uint32_t) ~0x10000UL;
}
static inline void Cy_PDM_PCM_FreezeFifo(PDM_Type * base)
{
    (((PDM_V1_Type*)(base))->RX_FIFO_CTL) |= 0x20000UL;
}
static inline void Cy_PDM_PCM_UnfreezeFifo(PDM_Type * base)
{
    (((PDM_V1_Type*)(base))->RX_FIFO_CTL) &= (uint32_t) ~0x20000UL;
}
static inline uint32_t Cy_PDM_PCM_ReadFifoSilent(PDM_Type const * base)
{
    return ((((PDM_V1_Type*)(base))->RX_FIFO_RD_SILENT));
}
typedef enum
{
    CY_PROFILE_CLK_TIMER = 0,
    CY_PROFILE_CLK_IMO = 1,
    CY_PROFILE_CLK_ECO = 2,
    CY_PROFILE_CLK_LF = 3,
    CY_PROFILE_CLK_HF = 4,
    CY_PROFILE_CLK_PERI = 5,
} cy_en_profile_ref_clk_t;
typedef enum
{
    CY_PROFILE_EVENT = 0,
    CY_PROFILE_DURATION = 1,
} cy_en_profile_duration_t;
typedef enum
{
    CY_PROFILE_SUCCESS = 0x00U,
    CY_PROFILE_BAD_PARAM = ((uint32_t)((uint32_t)((0x1EU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 1UL
 } cy_en_profile_status_t;
typedef struct
{
    cy_en_profile_duration_t cntDuration;
    cy_en_profile_ref_clk_t refClkSel;
    en_ep_mon_sel_t monSel;
} cy_stc_profile_ctr_ctl_t;
typedef struct
{
    uint8_t ctrNum;
    uint8_t used;
    cy_stc_profile_ctr_ctl_t ctlRegVals;
    PROFILE_CNT_STRUCT_Type * cntAddr;
    uint32_t ctlReg;
    uint32_t cntReg;
    uint32_t overflow;
    uint32_t weight;
} cy_stc_profile_ctr_t;
typedef cy_stc_profile_ctr_t * cy_stc_profile_ctr_ptr_t;
void Cy_Profile_ISR(void);
static inline void Cy_Profile_Init(void);
static inline void Cy_Profile_DeInit(void);
                void Cy_Profile_StartProfiling(void);
static inline void Cy_Profile_StopProfiling(void);
static inline uint32_t Cy_Profile_IsProfiling(void);
static inline void Cy_Profile_Init(void)
{
    (((PROFILE_V1_Type*) 0x402D0000UL)->CTL) = (((uint32_t)(1UL) << 31UL) & 0x80000000UL) |
                  (((uint32_t)(0UL) << 0UL) & 0x1UL);
    (((PROFILE_V1_Type*) 0x402D0000UL)->INTR_MASK) = 0UL;
}
static inline void Cy_Profile_DeInit(void)
{
    (((PROFILE_V1_Type*) 0x402D0000UL)->CTL) = (((uint32_t)(0UL) << 31UL) & 0x80000000UL);
    (((PROFILE_V1_Type*) 0x402D0000UL)->INTR_MASK) = 0UL;
}
static inline void Cy_Profile_StopProfiling(void)
{
    (((PROFILE_V1_Type*) 0x402D0000UL)->CMD) = 2UL;
}
static inline uint32_t Cy_Profile_IsProfiling(void)
{
    return (((uint32_t)((((PROFILE_V1_Type*) 0x402D0000UL)->STATUS)) & 0x1UL) >> 0UL);
}
void Cy_Profile_ClearConfiguration(void);
static inline void Cy_Profile_ClearCounters(void);
cy_stc_profile_ctr_ptr_t Cy_Profile_ConfigureCounter(en_ep_mon_sel_t monitor, cy_en_profile_duration_t duration, cy_en_profile_ref_clk_t refClk, uint32_t weight);
cy_en_profile_status_t Cy_Profile_FreeCounter(cy_stc_profile_ctr_ptr_t ctrAddr);
cy_en_profile_status_t Cy_Profile_EnableCounter(cy_stc_profile_ctr_ptr_t ctrAddr);
cy_en_profile_status_t Cy_Profile_DisableCounter(cy_stc_profile_ctr_ptr_t ctrAddr);
static inline void Cy_Profile_ClearCounters(void)
{
    (((PROFILE_V1_Type*) 0x402D0000UL)->CMD) = 0x100UL;
}
cy_en_profile_status_t Cy_Profile_GetRawCount(cy_stc_profile_ctr_ptr_t ctrAddr, uint64_t *result);
cy_en_profile_status_t Cy_Profile_GetWeightedCount(cy_stc_profile_ctr_ptr_t ctrAddr, uint64_t *result);
uint64_t Cy_Profile_GetSumWeightedCounts(cy_stc_profile_ctr_ptr_t ptrsArray[], uint32_t numCounters);
typedef enum
{
    CY_PROT_SUCCESS = 0x00U,
    CY_PROT_BAD_PARAM = (((uint32_t)((uint32_t)((0x30U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01U,
    CY_PROT_INVALID_STATE = (((uint32_t)((uint32_t)((0x30U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02U,
    CY_PROT_FAILURE = (((uint32_t)((uint32_t)((0x30U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x03U,
    CY_PROT_UNAVAILABLE = (((uint32_t)((uint32_t)((0x30U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x04U
} cy_en_prot_status_t;
typedef enum
{
    CY_PROT_PERM_DISABLED = 0x00U,
    CY_PROT_PERM_R = 0x01U,
    CY_PROT_PERM_W = 0x02U,
    CY_PROT_PERM_RW = 0x03U,
    CY_PROT_PERM_X = 0x04U,
    CY_PROT_PERM_RX = 0x05U,
    CY_PROT_PERM_WX = 0x06U,
    CY_PROT_PERM_RWX = 0x07U
}cy_en_prot_perm_t;
typedef enum
{
    CY_PROT_SIZE_4B = 1U,
    CY_PROT_SIZE_8B = 2U,
    CY_PROT_SIZE_16B = 3U,
    CY_PROT_SIZE_32B = 4U,
    CY_PROT_SIZE_64B = 5U,
    CY_PROT_SIZE_128B = 6U,
    CY_PROT_SIZE_256B = 7U,
    CY_PROT_SIZE_512B = 8U,
    CY_PROT_SIZE_1KB = 9U,
    CY_PROT_SIZE_2KB = 10U,
    CY_PROT_SIZE_4KB = 11U,
    CY_PROT_SIZE_8KB = 12U,
    CY_PROT_SIZE_16KB = 13U,
    CY_PROT_SIZE_32KB = 14U,
    CY_PROT_SIZE_64KB = 15U,
    CY_PROT_SIZE_128KB = 16U,
    CY_PROT_SIZE_256KB = 17U,
    CY_PROT_SIZE_512KB = 18U,
    CY_PROT_SIZE_1MB = 19U,
    CY_PROT_SIZE_2MB = 20U,
    CY_PROT_SIZE_4MB = 21U,
    CY_PROT_SIZE_8MB = 22U,
    CY_PROT_SIZE_16MB = 23U,
    CY_PROT_SIZE_32MB = 24U,
    CY_PROT_SIZE_64MB = 25U,
    CY_PROT_SIZE_128MB = 26U,
    CY_PROT_SIZE_256MB = 27U,
    CY_PROT_SIZE_512MB = 28U,
    CY_PROT_SIZE_1GB = 29U,
    CY_PROT_SIZE_2GB = 30U,
    CY_PROT_SIZE_4GB = 31U
}cy_en_prot_size_t;
enum cy_en_prot_pc_t
{
    CY_PROT_PC1 = 1U,
    CY_PROT_PC2 = 2U,
    CY_PROT_PC3 = 3U,
    CY_PROT_PC4 = 4U,
    CY_PROT_PC5 = 5U,
    CY_PROT_PC6 = 6U,
    CY_PROT_PC7 = 7U,
    CY_PROT_PC8 = 8U,
    CY_PROT_PC9 = 9U,
    CY_PROT_PC10 = 10U,
    CY_PROT_PC11 = 11U,
    CY_PROT_PC12 = 12U,
    CY_PROT_PC13 = 13U,
    CY_PROT_PC14 = 14U,
    CY_PROT_PC15 = 15U
};
enum cy_en_prot_subreg_t
{
    CY_PROT_SUBREGION_DIS0 = 0x01U,
    CY_PROT_SUBREGION_DIS1 = 0x02U,
    CY_PROT_SUBREGION_DIS2 = 0x04U,
    CY_PROT_SUBREGION_DIS3 = 0x08U,
    CY_PROT_SUBREGION_DIS4 = 0x10U,
    CY_PROT_SUBREGION_DIS5 = 0x20U,
    CY_PROT_SUBREGION_DIS6 = 0x40U,
    CY_PROT_SUBREGION_DIS7 = 0x80U
};
enum cy_en_prot_pcmask_t
{
    CY_PROT_PCMASK1 = 0x0001U,
    CY_PROT_PCMASK2 = 0x0002U,
    CY_PROT_PCMASK3 = 0x0004U,
    CY_PROT_PCMASK4 = 0x0008U,
    CY_PROT_PCMASK5 = 0x0010U,
    CY_PROT_PCMASK6 = 0x0020U,
    CY_PROT_PCMASK7 = 0x0040U,
    CY_PROT_PCMASK8 = 0x0080U,
    CY_PROT_PCMASK9 = 0x0100U,
    CY_PROT_PCMASK10 = 0x0200U,
    CY_PROT_PCMASK11 = 0x0400U,
    CY_PROT_PCMASK12 = 0x0800U,
    CY_PROT_PCMASK13 = 0x1000U,
    CY_PROT_PCMASK14 = 0x2000U,
    CY_PROT_PCMASK15 = 0x4000U
};
typedef enum
{
    CY_PROT_REQMODE_HIGHPRIOR = 0U,
    CY_PROT_REQMODE_LOWPRIOR = 1U,
    CY_PROT_REQMODE_INDEX = 2U
}cy_en_prot_req_mode_t;
typedef struct
{
    uint32_t* address;
    cy_en_prot_size_t regionSize;
    uint8_t subregions;
    cy_en_prot_perm_t userPermission;
    cy_en_prot_perm_t privPermission;
    _Bool secure;
} cy_stc_mpu_cfg_t;
typedef struct
{
    uint32_t* address;
    cy_en_prot_size_t regionSize;
    uint8_t subregions;
    cy_en_prot_perm_t userPermission;
    cy_en_prot_perm_t privPermission;
    _Bool secure;
    _Bool pcMatch;
    uint16_t pcMask;
} cy_stc_smpu_cfg_t;
typedef struct
{
    uint32_t* address;
    cy_en_prot_size_t regionSize;
    uint8_t subregions;
    cy_en_prot_perm_t userPermission;
    cy_en_prot_perm_t privPermission;
    _Bool secure;
    _Bool pcMatch;
    uint16_t pcMask;
} cy_stc_ppu_prog_cfg_t;
typedef struct
{
    cy_en_prot_perm_t userPermission;
    cy_en_prot_perm_t privPermission;
    _Bool secure;
    _Bool pcMatch;
    uint16_t pcMask;
} cy_stc_ppu_gr_cfg_t;
typedef struct
{
    cy_en_prot_perm_t userPermission;
    cy_en_prot_perm_t privPermission;
    _Bool secure;
    _Bool pcMatch;
    uint16_t pcMask;
} cy_stc_ppu_sl_cfg_t;
typedef struct
{
    cy_en_prot_perm_t userPermission;
    cy_en_prot_perm_t privPermission;
    _Bool secure;
    _Bool pcMatch;
    uint16_t pcMask;
} cy_stc_ppu_rg_cfg_t;
cy_en_prot_status_t Cy_Prot_ConfigBusMaster(en_prot_master_t busMaster, _Bool privileged, _Bool secure, uint32_t pcMask);
cy_en_prot_status_t Cy_Prot_SetActivePC(en_prot_master_t busMaster, uint32_t pc);
uint32_t Cy_Prot_GetActivePC(en_prot_master_t busMaster);
cy_en_prot_status_t Cy_Prot_ConfigMpuStruct(PROT_MPU_MPU_STRUCT_Type* base, const cy_stc_mpu_cfg_t* config);
cy_en_prot_status_t Cy_Prot_EnableMpuStruct(PROT_MPU_MPU_STRUCT_Type* base);
cy_en_prot_status_t Cy_Prot_DisableMpuStruct(PROT_MPU_MPU_STRUCT_Type* base);
static inline cy_en_prot_status_t Cy_Prot_DisableSmpuStruct(PROT_SMPU_SMPU_STRUCT_Type* base);
cy_en_prot_status_t Cy_Prot_GetSmpuStruct(PROT_SMPU_SMPU_STRUCT_Type** base, cy_en_prot_req_mode_t reqMode, uint32_t smpuIndex);
cy_en_prot_status_t Cy_Prot_ConfigSmpuMasterStruct(PROT_SMPU_SMPU_STRUCT_Type* base, const cy_stc_smpu_cfg_t* config);
cy_en_prot_status_t Cy_Prot_ConfigSmpuSlaveStruct(PROT_SMPU_SMPU_STRUCT_Type* base, const cy_stc_smpu_cfg_t* config);
cy_en_prot_status_t Cy_Prot_EnableSmpuMasterStruct(PROT_SMPU_SMPU_STRUCT_Type* base);
cy_en_prot_status_t Cy_Prot_DisableSmpuMasterStruct(PROT_SMPU_SMPU_STRUCT_Type* base);
cy_en_prot_status_t Cy_Prot_EnableSmpuSlaveStruct(PROT_SMPU_SMPU_STRUCT_Type* base);
cy_en_prot_status_t Cy_Prot_DisableSmpuSlaveStruct(PROT_SMPU_SMPU_STRUCT_Type* base);
static inline cy_en_prot_status_t Cy_Prot_DisablePpuProgStruct(PERI_PPU_PR_Type* base);
cy_en_prot_status_t Cy_Prot_ConfigPpuProgMasterStruct(PERI_PPU_PR_Type* base, const cy_stc_ppu_prog_cfg_t* config);
cy_en_prot_status_t Cy_Prot_ConfigPpuProgSlaveStruct(PERI_PPU_PR_Type* base, const cy_stc_ppu_prog_cfg_t* config);
cy_en_prot_status_t Cy_Prot_EnablePpuProgMasterStruct(PERI_PPU_PR_Type* base);
cy_en_prot_status_t Cy_Prot_DisablePpuProgMasterStruct(PERI_PPU_PR_Type* base);
cy_en_prot_status_t Cy_Prot_EnablePpuProgSlaveStruct(PERI_PPU_PR_Type* base);
cy_en_prot_status_t Cy_Prot_DisablePpuProgSlaveStruct(PERI_PPU_PR_Type* base);
cy_en_prot_status_t Cy_Prot_GetPpuProgStruct(PERI_PPU_PR_Type** base, cy_en_prot_req_mode_t reqMode, uint32_t ppuProgIndex);
cy_en_prot_status_t Cy_Prot_ConfigPpuFixedGrMasterStruct(PERI_PPU_GR_Type* base, const cy_stc_ppu_gr_cfg_t* config);
cy_en_prot_status_t Cy_Prot_ConfigPpuFixedGrSlaveStruct(PERI_PPU_GR_Type* base, const cy_stc_ppu_gr_cfg_t* config);
cy_en_prot_status_t Cy_Prot_EnablePpuFixedGrMasterStruct(PERI_PPU_GR_Type* base);
cy_en_prot_status_t Cy_Prot_DisablePpuFixedGrMasterStruct(PERI_PPU_GR_Type* base);
cy_en_prot_status_t Cy_Prot_EnablePpuFixedGrSlaveStruct(PERI_PPU_GR_Type* base);
cy_en_prot_status_t Cy_Prot_DisablePpuFixedGrSlaveStruct(PERI_PPU_GR_Type* base);
cy_en_prot_status_t Cy_Prot_ConfigPpuFixedSlMasterStruct(PERI_GR_PPU_SL_Type* base, const cy_stc_ppu_sl_cfg_t* config);
cy_en_prot_status_t Cy_Prot_ConfigPpuFixedSlSlaveStruct(PERI_GR_PPU_SL_Type* base, const cy_stc_ppu_sl_cfg_t* config);
cy_en_prot_status_t Cy_Prot_EnablePpuFixedSlMasterStruct(PERI_GR_PPU_SL_Type* base);
cy_en_prot_status_t Cy_Prot_DisablePpuFixedSlMasterStruct(PERI_GR_PPU_SL_Type* base);
cy_en_prot_status_t Cy_Prot_EnablePpuFixedSlSlaveStruct(PERI_GR_PPU_SL_Type* base);
cy_en_prot_status_t Cy_Prot_DisablePpuFixedSlSlaveStruct(PERI_GR_PPU_SL_Type* base);
cy_en_prot_status_t Cy_Prot_ConfigPpuFixedRgMasterStruct(PERI_GR_PPU_RG_Type* base, const cy_stc_ppu_rg_cfg_t* config);
cy_en_prot_status_t Cy_Prot_ConfigPpuFixedRgSlaveStruct(PERI_GR_PPU_RG_Type* base, const cy_stc_ppu_rg_cfg_t* config);
cy_en_prot_status_t Cy_Prot_EnablePpuFixedRgMasterStruct(PERI_GR_PPU_RG_Type* base);
cy_en_prot_status_t Cy_Prot_DisablePpuFixedRgMasterStruct(PERI_GR_PPU_RG_Type* base);
cy_en_prot_status_t Cy_Prot_EnablePpuFixedRgSlaveStruct(PERI_GR_PPU_RG_Type* base);
cy_en_prot_status_t Cy_Prot_DisablePpuFixedRgSlaveStruct(PERI_GR_PPU_RG_Type* base);
static inline cy_en_prot_status_t Cy_Prot_DisableSmpuStruct(PROT_SMPU_SMPU_STRUCT_Type* base)
{
    cy_en_prot_status_t status = Cy_Prot_DisableSmpuMasterStruct(base);
    if (CY_PROT_SUCCESS == status)
    {
        status = Cy_Prot_DisableSmpuSlaveStruct(base);
    }
    return status;
}
static inline cy_en_prot_status_t Cy_Prot_DisablePpuProgStruct(PERI_PPU_PR_Type* base)
{
    cy_en_prot_status_t status = CY_PROT_INVALID_STATE;
    if (((uint32_t)(0x20U > cy_device->periVersion)) != 0U)
    {
        status = Cy_Prot_DisablePpuProgMasterStruct(base);
        if (CY_PROT_SUCCESS == status)
        {
            status = Cy_Prot_DisablePpuProgSlaveStruct(base);
        }
    }
    return status;
}
typedef enum
 {
    CY_RTC_SUCCESS = 0x00U,
    CY_RTC_BAD_PARAM = (((uint32_t)((uint32_t)((0x28U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01U,
    CY_RTC_TIMEOUT = (((uint32_t)((uint32_t)((0x28U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02U,
    CY_RTC_INVALID_STATE = (((uint32_t)((uint32_t)((0x28U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x03U,
    CY_RTC_UNKNOWN = (((uint32_t)((uint32_t)((0x28U) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0xFFU
} cy_en_rtc_status_t;
typedef enum
{
    CY_RTC_FREQ_WCO_32768_HZ,
    CY_RTC_FREQ_60_HZ,
    CY_RTC_FREQ_50_HZ,
} cy_en_rtc_clock_freq_t;
typedef enum cy_en_rtc_alarm
{
    CY_RTC_ALARM_1,
    CY_RTC_ALARM_2
} cy_en_rtc_alarm_t;
typedef enum
{
    CY_RTC_24_HOURS,
    CY_RTC_12_HOURS
} cy_en_rtc_hours_format_t;
typedef enum
{
    CY_RTC_WRITE_DISABLED,
    CY_RTC_WRITE_ENABLED
} cy_en_rtc_write_status_t;
typedef enum
{
    CY_RTC_DST_RELATIVE,
    CY_RTC_DST_FIXED
} cy_en_rtc_dst_format_t;
typedef enum
{
    CY_RTC_AM,
    CY_RTC_PM
} cy_en_rtc_am_pm_t;
typedef enum
{
    CY_RTC_ALARM_DISABLE,
    CY_RTC_ALARM_ENABLE
} cy_en_rtc_alarm_enable_t;
typedef enum
{
    CY_RTC_CLK_SELECT_WCO = 0U,
    CY_RTC_CLK_SELECT_ALTBAK = 1U,
    CY_RTC_CLK_SELECT_ILO = 2U,
    CY_RTC_CLK_SELECT_LPECO_PRESCALER = 3U,
    CY_RTC_CLK_SELECT_PILO = 4U,
} cy_en_rtc_clk_select_sources_t;
typedef enum
{
    CY_RTC_CALIB_SIGN_NEGATIVE = 0,
    CY_RTC_CALIB_SIGN_POSITIVE = 1,
} cy_en_rtc_calib_sign_t;
typedef enum
{
    CY_RTC_CAL_SEL_CAL512 = 0,
    CY_RTC_CAL_SEL_CAL2 = 2,
    CY_RTC_CAL_SEL_CAL1 = 3,
} cy_en_rtc_calib_sel_t;
typedef struct cy_stc_rtc_config
{
    uint32_t sec;
    uint32_t min;
    uint32_t hour;
    cy_en_rtc_am_pm_t amPm;
    cy_en_rtc_hours_format_t hrFormat;
    uint32_t dayOfWeek;
    uint32_t date;
    uint32_t month;
    uint32_t year;
} cy_stc_rtc_config_t;
typedef struct cy_stc_rtc_alarm
{
    uint32_t sec;
    cy_en_rtc_alarm_enable_t secEn;
    uint32_t min;
    cy_en_rtc_alarm_enable_t minEn;
    uint32_t hour;
    cy_en_rtc_alarm_enable_t hourEn;
    uint32_t dayOfWeek;
    cy_en_rtc_alarm_enable_t dayOfWeekEn;
    uint32_t date;
    cy_en_rtc_alarm_enable_t dateEn;
    uint32_t month;
    cy_en_rtc_alarm_enable_t monthEn;
    cy_en_rtc_alarm_enable_t almEn;
} cy_stc_rtc_alarm_t;
typedef struct
{
    cy_en_rtc_dst_format_t format;
    uint32_t hour;
    uint32_t dayOfMonth;
    uint32_t weekOfMonth;
    uint32_t dayOfWeek;
    uint32_t month;
} cy_stc_rtc_dst_format_t;
typedef struct
{
    cy_stc_rtc_dst_format_t startDst;
    cy_stc_rtc_dst_format_t stopDst;
} cy_stc_rtc_dst_t;
cy_en_rtc_status_t Cy_RTC_Init(cy_stc_rtc_config_t const *config);
cy_en_rtc_status_t Cy_RTC_SetDateAndTime(cy_stc_rtc_config_t const *dateTime);
void Cy_RTC_GetDateAndTime(cy_stc_rtc_config_t *dateTime);
cy_en_rtc_status_t Cy_RTC_SetDateAndTimeDirect(uint32_t sec, uint32_t min, uint32_t hour,
                                               uint32_t date, uint32_t month, uint32_t year);
cy_en_rtc_status_t Cy_RTC_SetHoursFormat(cy_en_rtc_hours_format_t hoursFormat);
void Cy_RTC_SelectFrequencyPrescaler(cy_en_rtc_clock_freq_t clkSel);
void Cy_RTC_SelectClockSource(cy_en_rtc_clk_select_sources_t clkSel);
cy_en_rtc_status_t Cy_RTC_CalibrationControlEnable(uint8_t calib_val, cy_en_rtc_calib_sign_t calib_sign, cy_en_rtc_calib_sel_t calib_sel);
cy_en_rtc_status_t Cy_RTC_CalibrationControlDisable(void);
cy_en_rtc_status_t Cy_RTC_SetAlarmDateAndTime(cy_stc_rtc_alarm_t const *alarmDateTime, cy_en_rtc_alarm_t alarmIndex);
void Cy_RTC_GetAlarmDateAndTime(cy_stc_rtc_alarm_t *alarmDateTime, cy_en_rtc_alarm_t alarmIndex);
cy_en_rtc_status_t Cy_RTC_SetAlarmDateAndTimeDirect(uint32_t sec, uint32_t min, uint32_t hour,
                                                    uint32_t date, uint32_t month, cy_en_rtc_alarm_t alarmIndex);
cy_en_rtc_status_t Cy_RTC_EnableDstTime(cy_stc_rtc_dst_t const *dstTime, cy_stc_rtc_config_t const *timeDate);
cy_en_rtc_status_t Cy_RTC_SetNextDstTime(cy_stc_rtc_dst_format_t const *nextDst);
_Bool Cy_RTC_GetDstStatus(cy_stc_rtc_dst_t const *dstTime, cy_stc_rtc_config_t const *timeDate);
void Cy_RTC_Interrupt(cy_stc_rtc_dst_t const *dstTime, _Bool mode);
void Cy_RTC_Alarm1Interrupt(void);
void Cy_RTC_Alarm2Interrupt(void);
void Cy_RTC_DstInterrupt(cy_stc_rtc_dst_t const *dstTime);
void Cy_RTC_CenturyInterrupt(void);
uint32_t Cy_RTC_GetInterruptStatus(void);
uint32_t Cy_RTC_GetInterruptStatusMasked(void);
uint32_t Cy_RTC_GetInterruptMask(void);
void Cy_RTC_ClearInterrupt(uint32_t interruptMask);
void Cy_RTC_SetInterrupt(uint32_t interruptMask);
void Cy_RTC_SetInterruptMask(uint32_t interruptMask);
cy_en_syspm_status_t Cy_RTC_DeepSleepCallback(const cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
cy_en_syspm_status_t Cy_RTC_HibernateCallback(const cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
static inline uint32_t Cy_RTC_ConvertDayOfWeek(uint32_t day, uint32_t month, uint32_t year);
static inline _Bool Cy_RTC_IsLeapYear(uint32_t year);
static inline uint32_t Cy_RTC_DaysInMonth(uint32_t month, uint32_t year);
static inline void Cy_RTC_SyncFromRtc(void);
static inline cy_en_rtc_status_t Cy_RTC_WriteEnable(cy_en_rtc_write_status_t writeEnable);
static inline uint32_t Cy_RTC_GetSyncStatus(void);
static inline cy_en_rtc_hours_format_t Cy_RTC_GetHoursFormat(void);
static inline _Bool Cy_RTC_IsExternalResetOccurred(void);
static inline void Cy_RTC_SyncToRtcAhbDateAndTime(uint32_t timeBcd, uint32_t dateBcd);
static inline void Cy_RTC_SyncToRtcAhbAlarm(uint32_t alarmTimeBcd, uint32_t alarmDateBcd, cy_en_rtc_alarm_t alarmIndex);
extern uint8_t const cy_RTC_daysInMonthTbl[(12U)];
static inline uint32_t Cy_RTC_ConvertDayOfWeek(uint32_t day, uint32_t month, uint32_t year)
{
    uint32_t retVal;
    do { if(!((((day) > 0U) && ((day) <= (31UL))))) { CY_HALT(); } } while (0);
    do { if(!((((month) > 0U) && ((month) <= (12U))))) { CY_HALT(); } } while (0);
    do { if(!(((year) > 0U))) { CY_HALT(); } } while (0);
    if (month < (3UL))
    {
        month = (12U) + month;
        year--;
    }
    retVal =
    (day + (((month + 1UL) * 26UL) / 10UL) + year + (year / 4UL) + (6UL * (year / 100UL)) + (year / 400UL)) % 7UL;
    if (0u == retVal)
    {
        retVal = (7UL);
    }
    return(retVal);
}
static inline _Bool Cy_RTC_IsLeapYear(uint32_t year)
{
    do { if(!(((year) > 0U))) { CY_HALT(); } } while (0);
    return(((0U == (year % 4UL)) && (0U != (year % 100UL))) || (0U == (year % 400UL)));
}
static inline uint32_t Cy_RTC_DaysInMonth(uint32_t month, uint32_t year)
{
    uint32_t retVal;
    do { if(!((((month) > 0U) && ((month) <= (12U))))) { CY_HALT(); } } while (0);
    do { if(!(((year) > 0U))) { CY_HALT(); } } while (0);
    retVal = cy_RTC_daysInMonthTbl[month - 1UL];
    if ((2UL) == month)
    {
        if (Cy_RTC_IsLeapYear(year))
        {
            retVal++;
        }
    }
    return(retVal);
}
static inline void Cy_RTC_SyncFromRtc(void)
{
    uint32_t interruptState;
    uint32_t rtcAccessRetry = (200u);
    interruptState = Cy_SysLib_EnterCriticalSection();
    while((Cy_RTC_GetSyncStatus() == (1UL)) && (rtcAccessRetry != 0U))
    {
        rtcAccessRetry--;
        Cy_SysLib_DelayUs((1u));
    }
    if ((rtcAccessRetry != 0U) && (!((((((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->RTC_RW)) & (0x2UL)) != 0UL)))
    {
        (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->RTC_RW) = 0x1UL;
        Cy_SysLib_DelayUs((uint16_t)((42000000UL / cy_AhbFreqHz) + 1UL));
        (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->RTC_RW) = 0U;
    }
    Cy_SysLib_ExitCriticalSection(interruptState);
}
static inline cy_en_rtc_status_t Cy_RTC_WriteEnable(cy_en_rtc_write_status_t writeEnable)
{
    cy_en_rtc_status_t retVal = CY_RTC_INVALID_STATE;
    uint32_t rtcAccessRetry = (200u);
    do { if(!((((writeEnable) == CY_RTC_WRITE_DISABLED) || ((writeEnable) == CY_RTC_WRITE_ENABLED)))) { CY_HALT(); } } while (0);
    if (writeEnable == CY_RTC_WRITE_ENABLED)
    {
        while((Cy_RTC_GetSyncStatus() == (1UL)) && (rtcAccessRetry != 0U))
        {
            rtcAccessRetry--;
            Cy_SysLib_DelayUs((1u));
        }
        if((rtcAccessRetry != 0U) && (!((((((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->RTC_RW)) & (0x1UL)) != 0UL)))
        {
            (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->RTC_RW) |= 0x2UL;
            retVal = CY_RTC_SUCCESS;
        }
    }
    else
    {
        (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->RTC_RW) &= ((uint32_t) ~0x2UL);
        retVal = CY_RTC_SUCCESS;
    }
    return(retVal);
}
static inline uint32_t Cy_RTC_GetSyncStatus(void)
{
    return((((((((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->STATUS)) & (0x1UL)) != 0UL)) ? (1UL) : (0UL));
}
static inline cy_en_rtc_hours_format_t Cy_RTC_GetHoursFormat(void)
{
    return((((((((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->RTC_TIME)) & (0x400000UL)) != 0UL)) ? CY_RTC_12_HOURS : CY_RTC_24_HOURS);
}
static inline _Bool Cy_RTC_IsExternalResetOccurred(void)
{
    return(0u == Cy_SysLib_GetResetReason());
}
static inline void Cy_RTC_SyncToRtcAhbDateAndTime(uint32_t timeBcd, uint32_t dateBcd)
{
    (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->RTC_TIME) = timeBcd;
    (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->RTC_DATE) = dateBcd;
}
static inline void Cy_RTC_SyncToRtcAhbAlarm(uint32_t alarmTimeBcd, uint32_t alarmDateBcd, cy_en_rtc_alarm_t alarmIndex)
{
    do { if(!((((alarmIndex) == CY_RTC_ALARM_1) || ((alarmIndex) == CY_RTC_ALARM_2)))) { CY_HALT(); } } while (0);
    if (alarmIndex != CY_RTC_ALARM_2)
    {
        (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->ALM1_TIME) = alarmTimeBcd;
        (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->ALM1_DATE) = alarmDateBcd;
    }
    else
    {
        (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->ALM2_TIME) = alarmTimeBcd;
        (((BACKUP_V1_Type *) ((BACKUP_Type*) 0x40270000UL))->ALM2_DATE) = alarmDateBcd;
    }
}
static inline uint32_t Cy_RTC_ConvertBcdToDec(uint32_t bcdNum);
static inline uint32_t Cy_RTC_ConvertDecToBcd(uint32_t decNum);
static inline uint32_t Cy_RTC_ConvertBcdToDec(uint32_t bcdNum)
{
    uint32_t retVal;
    retVal =
    ((bcdNum & ((0x0000000FUL) << (4UL)))
                          >> (4UL) ) * (10UL);
    retVal += bcdNum & (0x0000000FUL);
    return (retVal);
}
static inline uint32_t Cy_RTC_ConvertDecToBcd(uint32_t decNum)
{
    uint32_t retVal;
    uint32_t tmpVal;
    tmpVal = decNum % (100UL);
    retVal = ((uint32_t)(tmpVal / (10UL))) << (4UL);
    retVal += tmpVal % (10UL);
    return (retVal);
}

extern volatile int16_t Cy_SAR_offset[((16u) + 1UL)][(2UL)];
extern volatile int32_t Cy_SAR_countsPer10Volt[((16u) + 1UL)][(2UL)];
typedef enum
{
    CY_SAR_SUCCESS = 0x00UL,
    CY_SAR_BAD_PARAM = ((uint32_t)((uint32_t)((0x01u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01UL,
    CY_SAR_TIMEOUT = ((uint32_t)((uint32_t)((0x01u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02UL,
    CY_SAR_CONVERSION_NOT_COMPLETE = ((uint32_t)((uint32_t)((0x01u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x03UL,
} cy_en_sar_status_t;
typedef enum
{
    CY_SAR_START_CONVERT_SINGLE_SHOT = 0UL,
    CY_SAR_START_CONVERT_CONTINUOUS = 1UL,
} cy_en_sar_start_convert_sel_t;
typedef enum
{
    CY_SAR_RETURN_STATUS = 0UL,
    CY_SAR_WAIT_FOR_RESULT = 1UL,
    CY_SAR_RETURN_STATUS_INJ = 2UL,
    CY_SAR_WAIT_FOR_RESULT_INJ = 3UL,
} cy_en_sar_return_mode_t;
typedef enum
{
    CY_SAR_SWITCH_OPEN = 0UL,
    CY_SAR_SWITCH_CLOSE = 1UL
} cy_en_sar_switch_state_t;
typedef enum
{
    CY_SAR_SWITCH_SEQ_CTRL_DISABLE = 0UL,
    CY_SAR_SWITCH_SEQ_CTRL_ENABLE = 1UL
} cy_en_sar_switch_sar_seq_ctrl_t;
typedef enum
{
    CY_SAR_MUX_SWITCH0 = 0UL,
} cy_en_sar_switch_register_sel_t;
typedef enum
{
    CY_SAR_VREF_PWR_100 = 0UL << 0UL,
    CY_SAR_VREF_PWR_80 = 1UL << 0UL,
    CY_SAR_VREF_PWR_60 = 2UL << 0UL,
    CY_SAR_VREF_PWR_50 = 3UL << 0UL,
    CY_SAR_VREF_PWR_40 = 4UL << 0UL,
    CY_SAR_VREF_PWR_30 = 5UL << 0UL,
    CY_SAR_VREF_PWR_20 = 6UL << 0UL,
    CY_SAR_VREF_PWR_10 = 7UL << 0UL,
} cy_en_sar_ctrl_pwr_ctrl_vref_t;
typedef enum
{
    CY_SAR_VREF_SEL_BGR = 4UL << 4UL,
    CY_SAR_VREF_SEL_EXT = 5UL << 4UL,
    CY_SAR_VREF_SEL_VDDA_DIV_2 = 6UL << 4UL,
    CY_SAR_VREF_SEL_VDDA = 7UL << 4UL
} cy_en_sar_ctrl_vref_sel_t;
typedef enum
{
    CY_SAR_BYPASS_CAP_DISABLE = 0UL << 7UL,
    CY_SAR_BYPASS_CAP_ENABLE = 1UL << 7UL
} cy_en_sar_ctrl_bypass_cap_t;
typedef enum
{
    CY_SAR_NEG_SEL_VSSA_KELVIN = 0UL << 9UL,
    CY_SAR_NEG_SEL_P1 = 2UL << 9UL,
    CY_SAR_NEG_SEL_P3 = 3UL << 9UL,
    CY_SAR_NEG_SEL_P5 = 4UL << 9UL,
    CY_SAR_NEG_SEL_P7 = 5UL << 9UL,
    CY_SAR_NEG_SEL_ACORE = 6UL << 9UL,
    CY_SAR_NEG_SEL_VREF = 7UL << 9UL,
} cy_en_sar_ctrl_neg_sel_t;
typedef enum
{
    CY_SAR_CTRL_NEGVREF_FW_ONLY = 0UL << 13UL,
    CY_SAR_CTRL_NEGVREF_HW = 1UL << 13UL
} cy_en_sar_ctrl_hw_ctrl_negvref_t;
typedef enum
{
    CY_SAR_CTRL_COMP_DLY_2P5 = 0UL << 14UL,
    CY_SAR_CTRL_COMP_DLY_4 = 1UL << 14UL,
    CY_SAR_CTRL_COMP_DLY_10 = 2UL << 14UL,
    CY_SAR_CTRL_COMP_DLY_12 = 3UL << 14UL
} cy_en_sar_ctrl_comp_delay_t;
typedef enum
{
    CY_SAR_COMP_PWR_100 = 0UL << 24UL,
    CY_SAR_COMP_PWR_80 = 1UL << 24UL,
    CY_SAR_COMP_PWR_60 = 2UL << 24UL,
    CY_SAR_COMP_PWR_50 = 3UL << 24UL,
    CY_SAR_COMP_PWR_40 = 4UL << 24UL,
    CY_SAR_COMP_PWR_30 = 5UL << 24UL,
    CY_SAR_COMP_PWR_20 = 6UL << 24UL,
    CY_SAR_COMP_PWR_10 = 7UL << 24UL,
} cy_en_sar_ctrl_comp_pwr_t;
typedef enum
{
    CY_SAR_DEEPSLEEP_SARMUX_OFF = 0UL << 27UL,
    CY_SAR_DEEPSLEEP_SARMUX_ON = 1UL << 27UL
} cy_en_sar_ctrl_sarmux_deep_sleep_t;
typedef enum
{
    CY_SAR_SARSEQ_SWITCH_ENABLE = 0UL << 30UL,
    CY_SAR_SARSEQ_SWITCH_DISABLE = 1UL << 30UL
} cy_en_sar_ctrl_sarseq_routing_switches_t;
typedef enum
{
    CY_SAR_RIGHT_ALIGN = 0UL << 1UL,
    CY_SAR_LEFT_ALIGN = 1UL << 1UL
} cy_en_sar_sample_ctrl_result_align_t;
typedef enum
{
    CY_SAR_SINGLE_ENDED_UNSIGNED = 0UL << 2UL,
    CY_SAR_SINGLE_ENDED_SIGNED = 1UL << 2UL
} cy_en_sar_sample_ctrl_single_ended_format_t;
typedef enum
{
    CY_SAR_DIFFERENTIAL_UNSIGNED = 0UL << 3UL,
    CY_SAR_DIFFERENTIAL_SIGNED = 1UL << 3UL
} cy_en_sar_sample_ctrl_differential_format_t;
typedef enum
{
    CY_SAR_AVG_CNT_2 = 0UL << 4UL,
    CY_SAR_AVG_CNT_4 = 1UL << 4UL,
    CY_SAR_AVG_CNT_8 = 2UL << 4UL,
    CY_SAR_AVG_CNT_16 = 3UL << 4UL,
    CY_SAR_AVG_CNT_32 = 4UL << 4UL,
    CY_SAR_AVG_CNT_64 = 5UL << 4UL,
    CY_SAR_AVG_CNT_128 = 6UL << 4UL,
    CY_SAR_AVG_CNT_256 = 7UL << 4UL
} cy_en_sar_sample_ctrl_avg_cnt_t;
typedef enum
{
    CY_SAR_AVG_MODE_SEQUENTIAL_ACCUM = 0UL,
    CY_SAR_AVG_MODE_SEQUENTIAL_FIXED = 0x80UL,
    CY_SAR_AVG_MODE_INTERLEAVED = 0x100UL,
} cy_en_sar_sample_ctrl_avg_mode_t;
typedef enum
{
    CY_SAR_TRIGGER_MODE_FW_ONLY = 0UL,
    CY_SAR_TRIGGER_MODE_FW_AND_HWEDGE = 0x20000UL,
    CY_SAR_TRIGGER_MODE_FW_AND_HWLEVEL = 0x20000UL | 0x40000UL,
} cy_en_sar_sample_ctrl_trigger_mode_t;
typedef enum
{
    CY_SAR_SAMPLE_TIME0_SHIFT = 0UL,
    CY_SAR_SAMPLE_TIME1_SHIFT = 16UL,
    CY_SAR_SAMPLE_TIME2_SHIFT = 0UL,
    CY_SAR_SAMPLE_TIME3_SHIFT = 16UL,
} cy_en_sar_sample_time_shift_t;
typedef enum
{
    CY_SAR_RANGE_LOW_SHIFT = 0UL,
    CY_SAR_RANGE_HIGH_SHIFT = 16UL,
} cy_en_sar_range_thres_shift_t;
typedef enum
{
    CY_SAR_RANGE_COND_BELOW = 0UL,
    CY_SAR_RANGE_COND_INSIDE = 1UL,
    CY_SAR_RANGE_COND_ABOVE = 2UL,
    CY_SAR_RANGE_COND_OUTSIDE = 3UL,
} cy_en_sar_range_detect_condition_t;
typedef enum
{
    CY_SAR_CHAN_SINGLE_ENDED = 0UL,
    CY_SAR_CHAN_DIFFERENTIAL_PAIRED = 0x100UL,
    CY_SAR_CHAN_DIFFERENTIAL_UNPAIRED = 0x1000000UL
} cy_en_sar_chan_config_input_mode_t;
typedef enum
{
    CY_SAR_CHAN_POS_PIN_ADDR_0 = 0UL,
    CY_SAR_CHAN_POS_PIN_ADDR_1 = 1UL << 0UL,
    CY_SAR_CHAN_POS_PIN_ADDR_2 = 2UL << 0UL,
    CY_SAR_CHAN_POS_PIN_ADDR_3 = 3UL << 0UL,
    CY_SAR_CHAN_POS_PIN_ADDR_4 = 4UL << 0UL,
    CY_SAR_CHAN_POS_PIN_ADDR_5 = 5UL << 0UL,
    CY_SAR_CHAN_POS_PIN_ADDR_6 = 6UL << 0UL,
    CY_SAR_CHAN_POS_PIN_ADDR_7 = 7UL << 0UL,
} cy_en_sar_chan_config_pos_pin_addr_t;
typedef enum
{
    CY_SAR_POS_PORT_ADDR_SARMUX = 0UL,
    CY_SAR_POS_PORT_ADDR_CTB0 = 1UL << 4UL,
    CY_SAR_POS_PORT_ADDR_CTB1 = 2UL << 4UL,
    CY_SAR_POS_PORT_ADDR_CTB2 = 3UL << 4UL,
    CY_SAR_POS_PORT_ADDR_CTB3 = 4UL << 4UL,
    CY_SAR_POS_PORT_ADDR_AROUTE_VIRT2 = 5UL << 4UL,
    CY_SAR_POS_PORT_ADDR_AROUTE_VIRT1 = 6UL << 4UL,
    CY_SAR_POS_PORT_ADDR_SARMUX_VIRT = 7UL << 4UL,
} cy_en_sar_chan_config_pos_port_addr_t;
typedef enum
{
    CY_SAR_CHAN_AVG_DISABLE = 0UL,
    CY_SAR_CHAN_AVG_ENABLE = 1UL << 10UL
} cy_en_sar_chan_config_avg_en_t;
typedef enum
{
    CY_SAR_CHAN_SAMPLE_TIME_0 = 0UL,
    CY_SAR_CHAN_SAMPLE_TIME_1 = 1UL << 12UL,
    CY_SAR_CHAN_SAMPLE_TIME_2 = 2UL << 12UL,
    CY_SAR_CHAN_SAMPLE_TIME_3 = 3UL << 12UL,
} cy_en_sar_chan_config_sample_time_t;
typedef enum
{
    CY_SAR_CHAN_NEG_PIN_ADDR_0 = 0UL,
    CY_SAR_CHAN_NEG_PIN_ADDR_1 = 1UL << 16UL,
    CY_SAR_CHAN_NEG_PIN_ADDR_2 = 2UL << 16UL,
    CY_SAR_CHAN_NEG_PIN_ADDR_3 = 3UL << 16UL,
    CY_SAR_CHAN_NEG_PIN_ADDR_4 = 4UL << 16UL,
    CY_SAR_CHAN_NEG_PIN_ADDR_5 = 5UL << 16UL,
    CY_SAR_CHAN_NEG_PIN_ADDR_6 = 6UL << 16UL,
    CY_SAR_CHAN_NEG_PIN_ADDR_7 = 7UL << 16UL,
} cy_en_sar_chan_config_neg_pin_addr_t;
typedef enum
{
    CY_SAR_NEG_PORT_ADDR_SARMUX = 0UL,
    CY_SAR_NEG_PORT_ADDR_AROUTE_VIRT2 = 5UL << 4UL,
    CY_SAR_NEG_PORT_ADDR_AROUTE_VIRT1 = 6UL << 4UL,
    CY_SAR_NEG_PORT_ADDR_SARMUX_VIRT = 7UL << 4UL,
} cy_en_sar_chan_config_neg_port_addr_t;
typedef enum
{
    CY_SAR_INJ_PORT_ADDR_SARMUX = 0UL,
    CY_SAR_INJ_PORT_ADDR_CTB0 = 1UL << 4UL,
    CY_SAR_INJ_PORT_ADDR_CTB1 = 2UL << 4UL,
    CY_SAR_INJ_PORT_ADDR_CTB2 = 3UL << 4UL,
    CY_SAR_INJ_PORT_ADDR_CTB3 = 4UL << 4UL,
    CY_SAR_INJ_PORT_ADDR_AROUTE_VIRT = 6UL << 4UL,
    CY_SAR_INJ_PORT_ADDR_SARMUX_VIRT = 7UL << 4UL,
} cy_en_sar_inj_chan_config_port_addr_t;
typedef enum
{
    CY_SAR_INTR_MASK_NONE = 0UL,
    CY_SAR_INTR_EOS_MASK = 0x1UL,
    CY_SAR_INTR_OVERFLOW_MASK = 0x2UL,
    CY_SAR_INTR_FW_COLLISION_MASK = 0x4UL,
} cy_en_sar_intr_mask_t;
typedef enum
{
    CY_SAR_MUX_FW_P0_VPLUS = 0x1UL,
    CY_SAR_MUX_FW_P1_VPLUS = 0x2UL,
    CY_SAR_MUX_FW_P2_VPLUS = 0x4UL,
    CY_SAR_MUX_FW_P3_VPLUS = 0x8UL,
    CY_SAR_MUX_FW_P4_VPLUS = 0x10UL,
    CY_SAR_MUX_FW_P5_VPLUS = 0x20UL,
    CY_SAR_MUX_FW_P6_VPLUS = 0x40UL,
    CY_SAR_MUX_FW_P7_VPLUS = 0x80UL,
    CY_SAR_MUX_FW_P0_VMINUS = 0x100UL,
    CY_SAR_MUX_FW_P1_VMINUS = 0x200UL,
    CY_SAR_MUX_FW_P2_VMINUS = 0x400UL,
    CY_SAR_MUX_FW_P3_VMINUS = 0x800UL,
    CY_SAR_MUX_FW_P4_VMINUS = 0x1000UL,
    CY_SAR_MUX_FW_P5_VMINUS = 0x2000UL,
    CY_SAR_MUX_FW_P6_VMINUS = 0x4000UL,
    CY_SAR_MUX_FW_P7_VMINUS = 0x8000UL,
    CY_SAR_MUX_FW_VSSA_VMINUS = 0x10000UL,
    CY_SAR_MUX_FW_TEMP_VPLUS = 0x20000UL,
    CY_SAR_MUX_FW_AMUXBUSA_VPLUS = 0x40000UL,
    CY_SAR_MUX_FW_AMUXBUSB_VPLUS = 0x80000UL,
    CY_SAR_MUX_FW_AMUXBUSA_VMINUS = 0x100000UL,
    CY_SAR_MUX_FW_AMUXBUSB_VMINUS = 0x200000UL,
    CY_SAR_MUX_FW_SARBUS0_VPLUS = 0x400000UL,
    CY_SAR_MUX_FW_SARBUS1_VPLUS = 0x800000UL,
    CY_SAR_MUX_FW_SARBUS0_VMINUS = 0x1000000UL,
    CY_SAR_MUX_FW_SARBUS1_VMINUS = 0x2000000UL,
    CY_SAR_MUX_FW_P4_COREIO0 = 0x4000000UL,
    CY_SAR_MUX_FW_P5_COREIO1 = 0x8000000UL,
    CY_SAR_MUX_FW_P6_COREIO2 = 0x10000000UL,
    CY_SAR_MUX_FW_P7_COREIO3 = 0x20000000UL,
} cy_en_sar_mux_switch_fw_ctrl_t;
typedef enum
{
    CY_SAR_MUX_SQ_CTRL_P0 = 0x1UL,
    CY_SAR_MUX_SQ_CTRL_P1 = 0x2UL,
    CY_SAR_MUX_SQ_CTRL_P2 = 0x4UL,
    CY_SAR_MUX_SQ_CTRL_P3 = 0x8UL,
    CY_SAR_MUX_SQ_CTRL_P4 = 0x10UL,
    CY_SAR_MUX_SQ_CTRL_P5 = 0x20UL,
    CY_SAR_MUX_SQ_CTRL_P6 = 0x40UL,
    CY_SAR_MUX_SQ_CTRL_P7 = 0x80UL,
    CY_SAR_MUX_SQ_CTRL_VSSA = 0x10000UL,
    CY_SAR_MUX_SQ_CTRL_TEMP = 0x20000UL,
    CY_SAR_MUX_SQ_CTRL_AMUXBUSA = 0x40000UL,
    CY_SAR_MUX_SQ_CTRL_AMUXBUSB = 0x80000UL,
    CY_SAR_MUX_SQ_CTRL_SARBUS0 = 0x400000UL,
    CY_SAR_MUX_SQ_CTRL_SARBUS1 = 0x800000UL,
} cy_en_sar_mux_switch_sq_ctrl_t;
typedef enum
{
    CY_SAR_CLK_PERI = 0UL,
    CY_SAR_CLK_DEEPSLEEP = 1UL
} cy_en_sar_clock_source_t;
typedef enum
{
    CY_SAR_SIMULT_TRIG_EVENT_EDGE = 0UL,
    CY_SAR_SIMULT_TRIG_EVENT_LEVEL = 1UL,
} cy_en_sar_simult_trig_event_sel_t;
typedef enum
{
    CY_SAR_SIMULT_TRIG_SYNC_NONE = 0UL,
    CY_SAR_SIMULT_TRIG_SYNC_SAR_CLOCK = 1UL,
} cy_en_sar_simult_trig_sync_sel_t;
typedef enum
{
    CY_SAR_SIMULT_TRIG_SAMPLE_SINGLE = 0UL,
    CY_SAR_SIMULT_TRIG_SAMPLE_SCAN_CNT = 1UL,
} cy_en_sar_simult_trig_sample_sel_t;
typedef enum
{
    CY_SAR_SIMULT_TRIG_INTR_EOS = 0UL,
    CY_SAR_SIMULT_TRIG_INTR_SCAN_CNT = 1UL,
}cy_en_sar_simult_trig_intr_sel_t;
typedef struct
{
    _Bool chanId;
    _Bool chainToNext;
    _Bool clrTrIntrOnRead;
    uint32_t level;
    _Bool trOut;
} cy_stc_sar_fifo_config_t;
typedef struct
{
    uint32_t ctrl;
    uint32_t sampleCtrl;
    uint32_t sampleTime01;
    uint32_t sampleTime23;
    uint32_t rangeThres;
    cy_en_sar_range_detect_condition_t rangeCond;
    uint32_t chanEn;
    uint32_t chanConfig[((16u) + 1UL)];
    uint32_t intrMask;
    uint32_t satIntrMask;
    uint32_t rangeIntrMask;
    uint32_t muxSwitch;
    uint32_t muxSwitchSqCtrl;
    _Bool configRouting;
    uint32_t vrefMvValue;
    cy_en_sar_clock_source_t clock;
    cy_stc_sar_fifo_config_t const * fifoCfgPtr;
    _Bool trTimer;
    _Bool scanCnt;
    _Bool scanCntIntr;
} cy_stc_sar_config_t;
typedef struct
{
    uint32_t pwrUpDelay;
    uint32_t scanCount;
    uint32_t simultControl;
    uint32_t simultTrigSource;
    cy_en_sar_simult_trig_event_sel_t simultTrigEvent;
    cy_en_sar_simult_trig_sync_sel_t simultTrigSync;
    cy_en_sar_simult_trig_sample_sel_t simultSamplesPerTrigger;
    cy_en_sar_simult_trig_intr_sel_t simultEOSIntrSelect;
}cy_stc_sar_common_config_t ;
typedef struct
{
    uint32_t hwEnabled;
    uint32_t continuous;
} cy_stc_sar_state_backup_t;
typedef struct
{
    uint16_t value;
    uint16_t channel;
} cy_stc_sar_fifo_read_t;
cy_en_sar_status_t Cy_SAR_CommonInit(PASS_Type *base, const cy_stc_sar_common_config_t * trigConfig);
static inline void Cy_SAR_SimultStart(PASS_Type *base, uint32_t sarMask, cy_en_sar_start_convert_sel_t mode);
static inline void Cy_SAR_SimultStop(PASS_Type *base, uint32_t sarMask);
cy_en_sar_status_t Cy_SAR_Init(SAR_Type *base, const cy_stc_sar_config_t *config);
cy_en_sar_status_t Cy_SAR_DeInit(SAR_Type *base, _Bool deInitRouting);
void Cy_SAR_Enable(SAR_Type *base);
void Cy_SAR_Disable(SAR_Type *base);
void Cy_SAR_StartConvert(SAR_Type *base, cy_en_sar_start_convert_sel_t startSelect);
void Cy_SAR_StopConvert(SAR_Type *base);
cy_en_sar_status_t Cy_SAR_IsEndConversion(SAR_Type *base, cy_en_sar_return_mode_t retMode);
int16_t Cy_SAR_GetResult16(const SAR_Type *base, uint32_t chan);
int32_t Cy_SAR_GetResult32(const SAR_Type *base, uint32_t chan);
static inline uint32_t Cy_SAR_GetChanResultUpdated(const SAR_Type *base);
static inline void Cy_SAR_EnableInjection(SAR_Type *base, _Bool tailgating);
cy_en_syspm_status_t Cy_SAR_DeepSleepCallback(const cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
void Cy_SAR_DeepSleep(SAR_Type *base);
void Cy_SAR_Wakeup(SAR_Type *base);
void Cy_SAR_SetConvertMode(SAR_Type *base, cy_en_sar_sample_ctrl_trigger_mode_t mode);
static inline void Cy_SAR_SetChanMask(SAR_Type *base, uint32_t enableMask);
void Cy_SAR_SetLowLimit(SAR_Type *base, uint32_t lowLimit);
void Cy_SAR_SetHighLimit(SAR_Type *base, uint32_t highLimit);
static inline void Cy_SAR_SetRangeCond(SAR_Type *base, cy_en_sar_range_detect_condition_t cond);
int16_t Cy_SAR_RawCounts2Counts(const SAR_Type *base, uint32_t chan, int16_t adcCounts);
float32_t Cy_SAR_CountsTo_Volts(const SAR_Type *base, uint32_t chan, int16_t adcCounts);
int16_t Cy_SAR_CountsTo_mVolts(const SAR_Type *base, uint32_t chan, int16_t adcCounts);
int32_t Cy_SAR_CountsTo_uVolts(const SAR_Type *base, uint32_t chan, int16_t adcCounts);
cy_en_sar_status_t Cy_SAR_SetChannelOffset(const SAR_Type *base, uint32_t chan, int16_t offset);
cy_en_sar_status_t Cy_SAR_SetChannelGain(const SAR_Type *base, uint32_t chan, int32_t adcGain);
static inline cy_en_sar_status_t Cy_SAR_SetOffset(uint32_t chan, int16_t offset)
{
    return (Cy_SAR_SetChannelOffset(((SAR_Type*)(cy_device->sar0Base)), chan, offset));
}
static inline cy_en_sar_status_t Cy_SAR_SetGain(uint32_t chan, int32_t adcGain)
{
    return (Cy_SAR_SetChannelGain(((SAR_Type*)(cy_device->sar0Base)), chan, adcGain));
}
void Cy_SAR_SetAnalogSwitch(SAR_Type *base, cy_en_sar_switch_register_sel_t switchSelect, uint32_t switchMask, cy_en_sar_switch_state_t state);
uint32_t Cy_SAR_GetAnalogSwitch(const SAR_Type *base, cy_en_sar_switch_register_sel_t switchSelect);
static inline void Cy_SAR_SetVssaVminusSwitch(SAR_Type *base, cy_en_sar_switch_state_t state);
void Cy_SAR_SetSwitchSarSeqCtrl(SAR_Type *base, uint32_t switchMask, cy_en_sar_switch_sar_seq_ctrl_t ctrl);
static inline void Cy_SAR_SetVssaSarSeqCtrl(SAR_Type *base, cy_en_sar_switch_sar_seq_ctrl_t ctrl);
static inline uint32_t Cy_SAR_GetInterruptStatus(const SAR_Type *base);
static inline void Cy_SAR_ClearInterrupt(SAR_Type *base, uint32_t intrMask);
static inline void Cy_SAR_SetInterrupt(SAR_Type *base, uint32_t intrMask);
static inline void Cy_SAR_SetInterruptMask(SAR_Type *base, uint32_t intrMask);
static inline uint32_t Cy_SAR_GetInterruptMask(const SAR_Type *base);
static inline uint32_t Cy_SAR_GetInterruptStatusMasked(const SAR_Type *base);
static inline uint32_t Cy_SAR_GetRangeInterruptStatus(const SAR_Type *base);
static inline void Cy_SAR_ClearRangeInterrupt(SAR_Type *base, uint32_t chanMask);
static inline void Cy_SAR_SetRangeInterrupt(SAR_Type *base, uint32_t chanMask);
static inline void Cy_SAR_SetRangeInterruptMask(SAR_Type *base, uint32_t chanMask);
static inline uint32_t Cy_SAR_GetRangeInterruptMask(const SAR_Type *base);
static inline uint32_t Cy_SAR_GetRangeInterruptStatusMasked(const SAR_Type *base);
static inline uint32_t Cy_SAR_GetSatInterruptStatus(const SAR_Type *base);
static inline void Cy_SAR_ClearSatInterrupt(SAR_Type *base, uint32_t chanMask);
static inline void Cy_SAR_SetSatInterrupt(SAR_Type *base, uint32_t chanMask);
static inline void Cy_SAR_SetSatInterruptMask(SAR_Type *base, uint32_t chanMask);
static inline uint32_t Cy_SAR_GetSatInterruptMask(const SAR_Type *base);
static inline uint32_t Cy_SAR_GetSatInterruptStatusMasked(const SAR_Type *base);
static inline uint32_t Cy_SAR_GetInterruptCause(const SAR_Type *base);
_Bool Cy_SAR_IsChannelSigned(const SAR_Type *base, uint32_t chan);
_Bool Cy_SAR_IsChannelSingleEnded(const SAR_Type *base, uint32_t chan);
static inline _Bool Cy_SAR_IsChannelDifferential(const SAR_Type *base, uint32_t chan);
cy_en_sar_status_t Cy_SAR_ScanCountEnable(const SAR_Type * base);
static inline void Cy_SAR_ScanCountDisable(const SAR_Type * base);
static inline void Cy_SAR_SelectClock(const SAR_Type * base, cy_en_sar_clock_source_t clock);
static inline void Cy_SAR_FifoRead(const SAR_Type *base, cy_stc_sar_fifo_read_t * readStruct);
static inline uint32_t Cy_SAR_FifoGetDataCount(const SAR_Type *base);
static inline void Cy_SAR_FifoSetLevel(const SAR_Type *base, uint32_t level);
static inline void Cy_SAR_ClearFifoInterrupt(const SAR_Type *base, uint32_t intrMask);
static inline void Cy_SAR_SetFifoInterrupt(const SAR_Type *base, uint32_t intrMask);
static inline void Cy_SAR_SetFifoInterruptMask(const SAR_Type *base, uint32_t intrMask);
static inline uint32_t Cy_SAR_GetFifoInterruptStatus(const SAR_Type *base);
static inline uint32_t Cy_SAR_GetFifoInterruptMask(const SAR_Type *base);
static inline uint32_t Cy_SAR_GetFifoInterruptStatusMasked(const SAR_Type *base);
static inline uint32_t Cy_SAR_GetChanResultUpdated(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->CHAN_RESULT_UPDATED);
}
static inline void Cy_SAR_EnableInjection(SAR_Type *base, _Bool tailgating)
{
    (((SAR_V1_Type *)(base))->INJ_CHAN_CONFIG) = ((((((SAR_V1_Type *)(base))->INJ_CHAN_CONFIG)) & ((uint32_t)(~(0x40000000UL)))) | ((((uint32_t)(tailgating ? 1UL : 0UL) << 30UL) & 0x40000000UL))) | 0x80000000UL;
}
static inline void Cy_SAR_SetChanMask(SAR_Type *base, uint32_t enableMask)
{
    do { if(!((0UL == ((enableMask) & ~((1UL << (16u)) - 1UL))))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->CHAN_EN) = enableMask;
}
static inline void Cy_SAR_SetRangeCond(SAR_Type *base, cy_en_sar_range_detect_condition_t cond)
{
    do { if(!(((cond) <= CY_SAR_RANGE_COND_OUTSIDE))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->RANGE_COND) = (uint32_t)cond << 30UL;
}
static inline uint32_t Cy_SAR_GetInterruptStatus(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->INTR);
}
static inline void Cy_SAR_ClearInterrupt(SAR_Type *base, uint32_t intrMask)
{
    do { if(!((0UL == ((intrMask) & ~((0x1UL) | (0x2UL) | (0x4UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x80UL)))))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->INTR) = intrMask & ((0x1UL) | (0x2UL) | (0x4UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x80UL));
    (void) (((SAR_V1_Type *)(base))->INTR);
}
static inline void Cy_SAR_SetInterrupt(SAR_Type *base, uint32_t intrMask)
{
    do { if(!((0UL == ((intrMask) & ~((0x1UL) | (0x2UL) | (0x4UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x80UL)))))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->INTR_SET) = intrMask & ((0x1UL) | (0x2UL) | (0x4UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x80UL));
}
static inline void Cy_SAR_SetInterruptMask(SAR_Type *base, uint32_t intrMask)
{
    do { if(!((0UL == ((intrMask) & ~((0x1UL) | (0x2UL) | (0x4UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x80UL)))))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->INTR_MASK) = intrMask & ((0x1UL) | (0x2UL) | (0x4UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x80UL));
}
static inline uint32_t Cy_SAR_GetInterruptMask(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->INTR_MASK);
}
static inline uint32_t Cy_SAR_GetInterruptStatusMasked(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->INTR_MASKED);
}
static inline uint32_t Cy_SAR_GetRangeInterruptStatus(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->RANGE_INTR);
}
static inline void Cy_SAR_ClearRangeInterrupt(SAR_Type *base, uint32_t chanMask)
{
    do { if(!((0UL == ((chanMask) & ~((1UL << (16u)) - 1UL))))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->RANGE_INTR) = chanMask & ((1UL << (16u)) - 1UL);
    (void) (((SAR_V1_Type *)(base))->RANGE_INTR);
}
static inline void Cy_SAR_SetRangeInterrupt(SAR_Type *base, uint32_t chanMask)
{
    do { if(!((0UL == ((chanMask) & ~((1UL << (16u)) - 1UL))))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->RANGE_INTR_SET) = chanMask & ((1UL << (16u)) - 1UL);
}
static inline void Cy_SAR_SetRangeInterruptMask(SAR_Type *base, uint32_t chanMask)
{
    do { if(!((0UL == ((chanMask) & ~((1UL << (16u)) - 1UL))))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->RANGE_INTR_MASK) = chanMask & ((1UL << (16u)) - 1UL);
}
static inline uint32_t Cy_SAR_GetRangeInterruptMask(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->RANGE_INTR_MASK);
}
static inline uint32_t Cy_SAR_GetRangeInterruptStatusMasked(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->RANGE_INTR_MASKED);
}
static inline uint32_t Cy_SAR_GetSatInterruptStatus(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->SATURATE_INTR);
}
static inline void Cy_SAR_ClearSatInterrupt(SAR_Type *base, uint32_t chanMask)
{
    do { if(!((0UL == ((chanMask) & ~((1UL << (16u)) - 1UL))))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->SATURATE_INTR) = chanMask & ((1UL << (16u)) - 1UL);
    (void) (((SAR_V1_Type *)(base))->SATURATE_INTR);
}
static inline void Cy_SAR_SetSatInterrupt(SAR_Type *base, uint32_t chanMask)
{
    do { if(!((0UL == ((chanMask) & ~((1UL << (16u)) - 1UL))))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->SATURATE_INTR_SET) = chanMask & ((1UL << (16u)) - 1UL);
}
static inline void Cy_SAR_SetSatInterruptMask(SAR_Type *base, uint32_t chanMask)
{
    do { if(!((0UL == ((chanMask) & ~((1UL << (16u)) - 1UL))))) { CY_HALT(); } } while (0);
    (((SAR_V1_Type *)(base))->SATURATE_INTR_MASK) = chanMask & ((1UL << (16u)) - 1UL);
}
static inline uint32_t Cy_SAR_GetSatInterruptMask(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->SATURATE_INTR_MASK);
}
static inline uint32_t Cy_SAR_GetSatInterruptStatusMasked(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->SATURATE_INTR_MASKED);
}
static inline uint32_t Cy_SAR_GetInterruptCause(const SAR_Type *base)
{
    return (((SAR_V1_Type *)(base))->INTR_CAUSE);
}
static inline _Bool Cy_SAR_IsChannelDifferential(const SAR_Type *base, uint32_t chan)
{
    return !Cy_SAR_IsChannelSingleEnded(base, chan);
}
static inline void Cy_SAR_SetVssaVminusSwitch(SAR_Type *base, cy_en_sar_switch_state_t state)
{
    Cy_SAR_SetAnalogSwitch(base, CY_SAR_MUX_SWITCH0, 0x10000UL, state);
}
static inline void Cy_SAR_SetVssaSarSeqCtrl(SAR_Type *base, cy_en_sar_switch_sar_seq_ctrl_t ctrl)
{
    Cy_SAR_SetSwitchSarSeqCtrl(base, 0x10000UL, ctrl);
}
static inline void Cy_SAR_ScanCountDisable(const SAR_Type *base)
{
    if (!(0x20U > cy_device->passVersion))
    {
        uint32_t interruptState = Cy_SysLib_EnterCriticalSection();
        (((PASS_V2_Type*) (((PASS_V2_Type*)cy_device->passBase)))->SAR_OVR_CTRL) &= ~((1UL << ((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)) << 4UL);
        Cy_SysLib_ExitCriticalSection(interruptState);
    }
}
static inline void Cy_SAR_SelectClock(const SAR_Type * base, cy_en_sar_clock_source_t clock)
{
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if (!(0x20U > cy_device->passVersion))
    {
        do { if(!((((clock) == CY_SAR_CLK_PERI) || ((clock) == CY_SAR_CLK_DEEPSLEEP)))) { CY_HALT(); } } while (0);
        (((PASS_V2_Type*) cy_device->passBase)->SAR_CLOCK_SEL[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]) = (((uint32_t)(clock) << 30UL) & 0x40000000UL);
        (((PASS_V2_Type*) cy_device->passBase)->SAR_DPSLP_CTRL[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]) = ((((CY_SAR_CLK_DEEPSLEEP == clock)) != 0) ? (0x80000000UL) : 0UL);
    }
}
static inline void Cy_SAR_FifoRead(const SAR_Type * base, cy_stc_sar_fifo_read_t * readStruct)
{
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if(!(0x20U > cy_device->passVersion))
    {
        uint32_t locReg = (((PASS_FIFO_V2_Type*)&(((PASS_V2_Type*)cy_device->passBase)->FIFO[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]))->RD_DATA);
        readStruct->channel = (uint16_t)(((uint32_t)(locReg) & 0xF0000UL) >> 16UL);
        readStruct->value = (uint16_t)(((uint32_t)(locReg) & 0xFFFFUL) >> 0UL);
    }
}
static inline uint32_t Cy_SAR_FifoGetDataCount(const SAR_Type * base)
{
    uint32_t retVal = 0UL;
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if(!(0x20U > cy_device->passVersion))
    {
        retVal = (((PASS_FIFO_V2_Type*)&(((PASS_V2_Type*)cy_device->passBase)->FIFO[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]))->USED);
    }
    return (retVal);
}
static inline void Cy_SAR_ClearFifoInterrupt(const SAR_Type * base, uint32_t intrMask)
{
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if(!(0x20U > cy_device->passVersion))
    {
        do { if(!((0UL == ((intrMask) & ~((0x1UL) | (0x2UL) | (0x4UL)))))) { CY_HALT(); } } while (0);
        (((PASS_FIFO_V2_Type*)&(((PASS_V2_Type*)cy_device->passBase)->FIFO[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]))->INTR) = intrMask & ((0x1UL) | (0x2UL) | (0x4UL));
        (void) (((PASS_FIFO_V2_Type*)&(((PASS_V2_Type*)cy_device->passBase)->FIFO[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]))->INTR);
    }
}
static inline void Cy_SAR_SetFifoInterrupt(const SAR_Type * base, uint32_t intrMask)
{
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if(!(0x20U > cy_device->passVersion))
    {
        do { if(!((0UL == ((intrMask) & ~((0x1UL) | (0x2UL) | (0x4UL)))))) { CY_HALT(); } } while (0);
        (((PASS_FIFO_V2_Type*)&(((PASS_V2_Type*)cy_device->passBase)->FIFO[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]))->INTR_SET) = intrMask & ((0x1UL) | (0x2UL) | (0x4UL));
    }
}
static inline void Cy_SAR_SetFifoInterruptMask(const SAR_Type * base, uint32_t intrMask)
{
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if(!(0x20U > cy_device->passVersion))
    {
        do { if(!((0UL == ((intrMask) & ~((0x1UL) | (0x2UL) | (0x4UL)))))) { CY_HALT(); } } while (0);
        (((PASS_FIFO_V2_Type*)&(((PASS_V2_Type*)cy_device->passBase)->FIFO[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]))->INTR_MASK) = intrMask & ((0x1UL) | (0x2UL) | (0x4UL));
    }
}
static inline uint32_t Cy_SAR_GetFifoInterruptStatus(const SAR_Type * base)
{
    uint32_t retVal = 0UL;
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if(!(0x20U > cy_device->passVersion))
    {
        retVal = (((PASS_FIFO_V2_Type*)&(((PASS_V2_Type*)cy_device->passBase)->FIFO[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]))->INTR);
    }
    return (retVal);
}
static inline uint32_t Cy_SAR_GetFifoInterruptMask(const SAR_Type * base)
{
    uint32_t retVal = 0UL;
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if(!(0x20U > cy_device->passVersion))
    {
        retVal = (((PASS_FIFO_V2_Type*)&(((PASS_V2_Type*)cy_device->passBase)->FIFO[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]))->INTR_MASK);
    }
    return (retVal);
}
static inline uint32_t Cy_SAR_GetFifoInterruptStatusMasked(const SAR_Type * base)
{
    uint32_t retVal = 0UL;
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if(!(0x20U > cy_device->passVersion))
    {
        retVal = (((PASS_FIFO_V2_Type*)&(((PASS_V2_Type*)cy_device->passBase)->FIFO[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]))->INTR_MASKED);
    }
    return (retVal);
}
static inline void Cy_SAR_FifoSetLevel(const SAR_Type *base, uint32_t level)
{
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if(!(0x20U > cy_device->passVersion))
    {
        uint32_t locLevel = level - 1UL;
        do { if(!(((locLevel) <= 0xFFUL))) { CY_HALT(); } } while (0);
        (((PASS_FIFO_V2_Type*)&(((PASS_V2_Type*)cy_device->passBase)->FIFO[((((SAR_Type*)(cy_device->sar0Base)) == (base)) ? 0UL : 1UL)]))->LEVEL) = (((uint32_t)(locLevel) << 0UL) & 0xFFUL);
    }
}
static inline void Cy_SAR_SimultStart(PASS_Type *base, uint32_t sarMask, cy_en_sar_start_convert_sel_t mode)
{
    do { if(!(!(0x20U > cy_device->passVersion))) { CY_HALT(); } } while (0);
    if (!(0x20U > cy_device->passVersion))
    {
        do{}while(0);
        (((PASS_V2_Type*) (base))->SAR_SIMULT_FW_START_CTRL) =
            ((((uint32_t)(sarMask) << 0UL) & 0xFUL) |
            ((mode == CY_SAR_START_CONVERT_CONTINUOUS) ? (((uint32_t)(sarMask) << 16UL) & 0xF0000UL) : 0UL));
    }
}
static inline void Cy_SAR_SimultStop(PASS_Type *base, uint32_t sarMask)
{
    if (!(0x20U > cy_device->passVersion))
    {
        do{}while(0);
        (((PASS_V2_Type*) (base))->SAR_SIMULT_FW_START_CTRL) = (((uint32_t)((~sarMask)) << 16UL) & 0xF0000UL);
    }
}


extern double atan (double);
extern double cos (double);
extern double sin (double);
extern double tan (double);
extern double tanh (double);
extern double frexp (double, int *);
extern double modf (double, double *);
extern double ceil (double);
extern double fabs (double);
extern double floor (double);
extern double acos (double);
extern double asin (double);
extern double atan2 (double, double);
extern double cosh (double);
extern double sinh (double);
extern double exp (double);
extern double ldexp (double, int);
extern double log (double);
extern double log10 (double);
extern double pow (double, double);
extern double sqrt (double);
extern double fmod (double, double);
extern int finite (double);
extern int finitef (float);
extern int finitel (long double);
extern int isinff (float);
extern int isnanf (float);
extern int isinf (double);
extern int isnan (double);
    typedef float float_t;
    typedef double double_t;
extern int __isinff (float);
extern int __isinfd (double);
extern int __isnanf (float);
extern int __isnand (double);
extern int __fpclassifyf (float);
extern int __fpclassifyd (double);
extern int __signbitf (float);
extern int __signbitd (double);
extern double infinity (void);
extern double nan (const char *);
extern double copysign (double, double);
extern double logb (double);
extern int ilogb (double);
extern double asinh (double);
extern double cbrt (double);
extern double nextafter (double, double);
extern double rint (double);
extern double scalbn (double, int);
extern double exp2 (double);
extern double scalbln (double, long int);
extern double tgamma (double);
extern double nearbyint (double);
extern long int lrint (double);
extern long long int llrint (double);
extern double round (double);
extern long int lround (double);
extern long long int llround (double);
extern double trunc (double);
extern double remquo (double, double, int *);
extern double fdim (double, double);
extern double fmax (double, double);
extern double fmin (double, double);
extern double fma (double, double, double);
extern double log1p (double);
extern double expm1 (double);
extern double acosh (double);
extern double atanh (double);
extern double remainder (double, double);
extern double gamma (double);
extern double lgamma (double);
extern double erf (double);
extern double erfc (double);
extern double log2 (double);
extern double hypot (double, double);
extern float atanf (float);
extern float cosf (float);
extern float sinf (float);
extern float tanf (float);
extern float tanhf (float);
extern float frexpf (float, int *);
extern float modff (float, float *);
extern float ceilf (float);
extern float fabsf (float);
extern float floorf (float);
extern float acosf (float);
extern float asinf (float);
extern float atan2f (float, float);
extern float coshf (float);
extern float sinhf (float);
extern float expf (float);
extern float ldexpf (float, int);
extern float logf (float);
extern float log10f (float);
extern float powf (float, float);
extern float sqrtf (float);
extern float fmodf (float, float);
extern float exp2f (float);
extern float scalblnf (float, long int);
extern float tgammaf (float);
extern float nearbyintf (float);
extern long int lrintf (float);
extern long long int llrintf (float);
extern float roundf (float);
extern long int lroundf (float);
extern long long int llroundf (float);
extern float truncf (float);
extern float remquof (float, float, int *);
extern float fdimf (float, float);
extern float fmaxf (float, float);
extern float fminf (float, float);
extern float fmaf (float, float, float);
extern float infinityf (void);
extern float nanf (const char *);
extern float copysignf (float, float);
extern float logbf (float);
extern int ilogbf (float);
extern float asinhf (float);
extern float cbrtf (float);
extern float nextafterf (float, float);
extern float rintf (float);
extern float scalbnf (float, int);
extern float log1pf (float);
extern float expm1f (float);
extern float acoshf (float);
extern float atanhf (float);
extern float remainderf (float, float);
extern float gammaf (float);
extern float lgammaf (float);
extern float erff (float);
extern float erfcf (float);
extern float log2f (float);
extern float hypotf (float, float);
extern long double atanl (long double);
extern long double cosl (long double);
extern long double sinl (long double);
extern long double tanl (long double);
extern long double tanhl (long double);
extern long double frexpl (long double, int *);
extern long double modfl (long double, long double *);
extern long double ceill (long double);
extern long double fabsl (long double);
extern long double floorl (long double);
extern long double log1pl (long double);
extern long double expm1l (long double);
extern long double acosl (long double);
extern long double asinl (long double);
extern long double atan2l (long double, long double);
extern long double coshl (long double);
extern long double sinhl (long double);
extern long double expl (long double);
extern long double ldexpl (long double, int);
extern long double logl (long double);
extern long double log10l (long double);
extern long double powl (long double, long double);
extern long double sqrtl (long double);
extern long double fmodl (long double, long double);
extern long double hypotl (long double, long double);
extern long double copysignl (long double, long double);
extern long double nanl (const char *);
extern int ilogbl (long double);
extern long double asinhl (long double);
extern long double cbrtl (long double);
extern long double nextafterl (long double, long double);
extern float nexttowardf (float, long double);
extern double nexttoward (double, long double);
extern long double nexttowardl (long double, long double);
extern long double logbl (long double);
extern long double log2l (long double);
extern long double rintl (long double);
extern long double scalbnl (long double, int);
extern long double exp2l (long double);
extern long double scalblnl (long double, long);
extern long double tgammal (long double);
extern long double nearbyintl (long double);
extern long int lrintl (long double);
extern long long int llrintl (long double);
extern long double roundl (long double);
extern long lroundl (long double);
extern long long int llroundl (long double);
extern long double truncl (long double);
extern long double remquol (long double, long double, int *);
extern long double fdiml (long double, long double);
extern long double fmaxl (long double, long double);
extern long double fminl (long double, long double);
extern long double fmal (long double, long double, long double);
extern long double acoshl (long double);
extern long double atanhl (long double);
extern long double remainderl (long double, long double);
extern long double lgammal (long double);
extern long double erfl (long double);
extern long double erfcl (long double);
extern double drem (double, double);
extern float dremf (float, float);
extern double gamma_r (double, int *);
extern double lgamma_r (double, int *);
extern float gammaf_r (float, int *);
extern float lgammaf_r (float, int *);
extern double y0 (double);
extern double y1 (double);
extern double yn (int, double);
extern double j0 (double);
extern double j1 (double);
extern double jn (int, double);
extern float y0f (float);
extern float y1f (float);
extern float ynf (int, float);
extern float j0f (float);
extern float j1f (float);
extern float jnf (int, float);
extern int *__signgam (void);

__attribute__((always_inline)) static inline uint32_t Cy_SCB_ReadRxFifo (CySCB_Type const *base);
static inline void Cy_SCB_SetRxFifoLevel(CySCB_Type *base, uint32_t level);
static inline uint32_t Cy_SCB_GetNumInRxFifo(CySCB_Type const *base);
static inline uint32_t Cy_SCB_GetRxSrValid (CySCB_Type const *base);
static inline void Cy_SCB_ClearRxFifo (CySCB_Type *base);
__attribute__((always_inline)) static inline void Cy_SCB_WriteTxFifo (CySCB_Type *base, uint32_t data);
static inline void Cy_SCB_SetTxFifoLevel(CySCB_Type *base, uint32_t level);
static inline uint32_t Cy_SCB_GetNumInTxFifo(CySCB_Type const *base);
static inline uint32_t Cy_SCB_GetTxSrValid (CySCB_Type const *base);
static inline _Bool Cy_SCB_IsTxComplete (CySCB_Type const *base);
static inline void Cy_SCB_ClearTxFifo (CySCB_Type *base);
static inline void Cy_SCB_SetByteMode(CySCB_Type *base, _Bool byteMode);
static inline uint32_t Cy_SCB_GetInterruptCause(CySCB_Type const *base);
static inline uint32_t Cy_SCB_GetRxInterruptStatus(CySCB_Type const *base);
static inline void Cy_SCB_SetRxInterruptMask (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetRxInterruptMask (CySCB_Type const *base);
static inline uint32_t Cy_SCB_GetRxInterruptStatusMasked(CySCB_Type const *base);
static inline void Cy_SCB_ClearRxInterrupt (CySCB_Type *base, uint32_t interruptMask);
static inline void Cy_SCB_SetRxInterrupt (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetTxInterruptStatus(CySCB_Type const *base);
static inline void Cy_SCB_SetTxInterruptMask (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetTxInterruptMask (CySCB_Type const *base);
static inline uint32_t Cy_SCB_GetTxInterruptStatusMasked(CySCB_Type const *base);
static inline void Cy_SCB_ClearTxInterrupt (CySCB_Type *base, uint32_t interruptMask);
static inline void Cy_SCB_SetTxInterrupt (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetMasterInterruptStatus(CySCB_Type const *base);
static inline void Cy_SCB_SetMasterInterruptMask (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetMasterInterruptMask (CySCB_Type const *base);
static inline uint32_t Cy_SCB_GetMasterInterruptStatusMasked(CySCB_Type const *base);
static inline void Cy_SCB_ClearMasterInterrupt (CySCB_Type *base, uint32_t interruptMask);
static inline void Cy_SCB_SetMasterInterrupt (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetSlaveInterruptStatus(CySCB_Type const *base);
static inline void Cy_SCB_SetSlaveInterruptMask (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetSlaveInterruptMask (CySCB_Type const *base);
static inline uint32_t Cy_SCB_GetSlaveInterruptStatusMasked(CySCB_Type const *base);
static inline void Cy_SCB_ClearSlaveInterrupt (CySCB_Type *base, uint32_t interruptMask);
static inline void Cy_SCB_SetSlaveInterrupt (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetI2CInterruptStatus(CySCB_Type const *base);
static inline void Cy_SCB_SetI2CInterruptMask (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetI2CInterruptMask (CySCB_Type const *base);
static inline uint32_t Cy_SCB_GetI2CInterruptStatusMasked(CySCB_Type const *base);
static inline void Cy_SCB_ClearI2CInterrupt (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetSpiInterruptStatus(CySCB_Type const *base);
static inline void Cy_SCB_SetSpiInterruptMask (CySCB_Type *base, uint32_t interruptMask);
static inline uint32_t Cy_SCB_GetSpiInterruptMask (CySCB_Type const *base);
static inline uint32_t Cy_SCB_GetSpiInterruptStatusMasked(CySCB_Type const *base);
static inline void Cy_SCB_ClearSpiInterrupt (CySCB_Type *base, uint32_t interruptMask);
void Cy_SCB_ReadArrayNoCheck (CySCB_Type const *base, void *buffer, uint32_t size);
uint32_t Cy_SCB_ReadArray (CySCB_Type const *base, void *buffer, uint32_t size);
void Cy_SCB_ReadArrayBlocking (CySCB_Type const *base, void *buffer, uint32_t size);
uint32_t Cy_SCB_Write (CySCB_Type *base, uint32_t data);
void Cy_SCB_WriteArrayNoCheck (CySCB_Type *base, void *buffer, uint32_t size);
uint32_t Cy_SCB_WriteArray (CySCB_Type *base, void *buffer, uint32_t size);
void Cy_SCB_WriteArrayBlocking(CySCB_Type *base, void *buffer, uint32_t size);
void Cy_SCB_WriteString (CySCB_Type *base, char_t const string[]);
void Cy_SCB_WriteDefaultArrayNoCheck(CySCB_Type *base, uint32_t txData, uint32_t size);
uint32_t Cy_SCB_WriteDefaultArray (CySCB_Type *base, uint32_t txData, uint32_t size);
static inline uint32_t Cy_SCB_GetFifoSize (CySCB_Type const *base);
static inline void Cy_SCB_FwBlockReset(CySCB_Type *base);
static inline _Bool Cy_SCB_IsRxDataWidthByte(CySCB_Type const *base);
static inline _Bool Cy_SCB_IsTxDataWidthByte(CySCB_Type const *base);
static inline uint32_t Cy_SCB_GetRxFifoLevel (CySCB_Type const *base);
__attribute__((always_inline)) static inline uint32_t Cy_SCB_ReadRxFifo(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->RX_FIFO_RD));
}
static inline void Cy_SCB_SetRxFifoLevel(CySCB_Type *base, uint32_t level)
{
    do { if(!(((level) < Cy_SCB_GetFifoSize(base)))) { CY_HALT(); } } while (0);
    (((((CySCB_V1_Type*) (base))->RX_FIFO_CTRL)) = (((((((CySCB_V1_Type*) (base))->RX_FIFO_CTRL))) & ((uint32_t)(~(0xFFUL)))) | ((((uint32_t)((level)) << 0UL) & 0xFFUL))));
}
static inline uint32_t Cy_SCB_GetNumInRxFifo(CySCB_Type const *base)
{
    return (((uint32_t)((((CySCB_V1_Type*) (base))->RX_FIFO_STATUS)) & 0x1FFUL) >> 0UL);
}
static inline uint32_t Cy_SCB_GetRxSrValid(CySCB_Type const *base)
{
    return (((uint32_t)((((CySCB_V1_Type*) (base))->RX_FIFO_STATUS)) & 0x8000UL) >> 15UL);
}
static inline void Cy_SCB_ClearRxFifo(CySCB_Type* base)
{
    (((CySCB_V1_Type*) (base))->RX_FIFO_CTRL) |= (uint32_t) 0x10000UL;
    (((CySCB_V1_Type*) (base))->RX_FIFO_CTRL) &= (uint32_t) ~0x10000UL;
    (void) (((CySCB_V1_Type*) (base))->RX_FIFO_CTRL);
}
__attribute__((always_inline)) static inline void Cy_SCB_WriteTxFifo(CySCB_Type* base, uint32_t data)
{
    (((CySCB_V1_Type*) (base))->TX_FIFO_WR) = data;
}
static inline void Cy_SCB_SetTxFifoLevel(CySCB_Type *base, uint32_t level)
{
    do { if(!(((level) < Cy_SCB_GetFifoSize(base)))) { CY_HALT(); } } while (0);
    (((((CySCB_V1_Type*) (base))->TX_FIFO_CTRL)) = (((((((CySCB_V1_Type*) (base))->TX_FIFO_CTRL))) & ((uint32_t)(~(0xFFUL)))) | ((((uint32_t)((level)) << 0UL) & 0xFFUL))));
}
static inline uint32_t Cy_SCB_GetNumInTxFifo(CySCB_Type const *base)
{
    return (((uint32_t)((((CySCB_V1_Type*) (base))->TX_FIFO_STATUS)) & 0x1FFUL) >> 0UL);
}
static inline uint32_t Cy_SCB_GetTxSrValid(CySCB_Type const *base)
{
    return (((uint32_t)((((CySCB_V1_Type*) (base))->TX_FIFO_STATUS)) & 0x8000UL) >> 15UL);
}
static inline _Bool Cy_SCB_IsTxComplete(CySCB_Type const *base)
{
     return (0UL == (Cy_SCB_GetNumInTxFifo(base) + Cy_SCB_GetTxSrValid(base)));
}
static inline void Cy_SCB_ClearTxFifo(CySCB_Type *base)
{
    (((CySCB_V1_Type*) (base))->TX_FIFO_CTRL) |= (uint32_t) 0x10000UL;
    (((CySCB_V1_Type*) (base))->TX_FIFO_CTRL) &= (uint32_t) ~0x10000UL;
    (void) (((CySCB_V1_Type*) (base))->TX_FIFO_CTRL);
}
static inline void Cy_SCB_SetByteMode(CySCB_Type *base, _Bool byteMode)
{
    if (byteMode)
    {
        (((CySCB_V1_Type*) (base))->CTRL) |= 0x800UL;
    }
    else
    {
        (((CySCB_V1_Type*) (base))->CTRL) &= ~0x800UL;
    }
}
static inline uint32_t Cy_SCB_GetInterruptCause(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_CAUSE));
}
static inline uint32_t Cy_SCB_GetRxInterruptStatus(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_RX) & (0x1UL | 0x4UL | 0x8UL | 0x20UL | 0x40UL | 0x100UL | 0x200UL | 0x800UL));
}
static inline void Cy_SCB_SetRxInterruptMask(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x4UL | 0x8UL | 0x20UL | 0x40UL | 0x100UL | 0x200UL | 0x800UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_RX_MASK) = interruptMask;
}
static inline uint32_t Cy_SCB_GetRxInterruptMask(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_RX_MASK));
}
static inline uint32_t Cy_SCB_GetRxInterruptStatusMasked(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_RX_MASKED));
}
static inline void Cy_SCB_ClearRxInterrupt(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x4UL | 0x8UL | 0x20UL | 0x40UL | 0x100UL | 0x200UL | 0x800UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_RX) = interruptMask;
    (void) (((CySCB_V1_Type*) (base))->INTR_RX);
}
static inline void Cy_SCB_SetRxInterrupt(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x4UL | 0x8UL | 0x20UL | 0x40UL | 0x100UL | 0x200UL | 0x800UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_RX_SET) = interruptMask;
}
static inline uint32_t Cy_SCB_GetTxInterruptStatus(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_TX) & (0x1UL | 0x2UL | 0x10UL | 0x20UL | 0x40UL | 0x200UL | 0x100UL | 0x400UL));
}
static inline void Cy_SCB_SetTxInterruptMask(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x2UL | 0x10UL | 0x20UL | 0x40UL | 0x200UL | 0x100UL | 0x400UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_TX_MASK) = interruptMask;
}
static inline uint32_t Cy_SCB_GetTxInterruptMask(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_TX_MASK));
}
static inline uint32_t Cy_SCB_GetTxInterruptStatusMasked(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_TX_MASKED));
}
static inline void Cy_SCB_ClearTxInterrupt(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x2UL | 0x10UL | 0x20UL | 0x40UL | 0x200UL | 0x100UL | 0x400UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_TX) = interruptMask;
    (void) (((CySCB_V1_Type*) (base))->INTR_TX);
}
static inline void Cy_SCB_SetTxInterrupt(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x2UL | 0x10UL | 0x20UL | 0x40UL | 0x200UL | 0x100UL | 0x400UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_TX_SET) = interruptMask;
}
static inline uint32_t Cy_SCB_GetMasterInterruptStatus(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_M) & (0x1UL | 0x2UL | 0x4UL | 0x10UL | 0x100UL | 0x200UL));
}
static inline void Cy_SCB_SetMasterInterruptMask(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x2UL | 0x4UL | 0x10UL | 0x100UL | 0x200UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_M_MASK) = interruptMask;
}
static inline uint32_t Cy_SCB_GetMasterInterruptMask(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_M_MASK));
}
static inline uint32_t Cy_SCB_GetMasterInterruptStatusMasked(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_M_MASKED));
}
static inline void Cy_SCB_ClearMasterInterrupt(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x2UL | 0x4UL | 0x10UL | 0x100UL | 0x200UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_M) = interruptMask;
    (void) (((CySCB_V1_Type*) (base))->INTR_M);
}
static inline void Cy_SCB_SetMasterInterrupt(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x2UL | 0x4UL | 0x10UL | 0x100UL | 0x200UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_M_SET) = interruptMask;
}
static inline uint32_t Cy_SCB_GetSlaveInterruptStatus(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_S) & (0x1UL | 0x2UL | 0x4UL | 0x8UL | 0x10UL | 0x20UL | 0x40UL | 0x80UL | 0x100UL | 0x800UL));
}
static inline void Cy_SCB_SetSlaveInterruptMask(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x2UL | 0x4UL | 0x8UL | 0x10UL | 0x20UL | 0x40UL | 0x80UL | 0x100UL | 0x800UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_S_MASK) = interruptMask;
}
static inline uint32_t Cy_SCB_GetSlaveInterruptMask(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_S_MASK));
}
static inline uint32_t Cy_SCB_GetSlaveInterruptStatusMasked(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_S_MASKED));
}
static inline void Cy_SCB_ClearSlaveInterrupt(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x2UL | 0x4UL | 0x8UL | 0x10UL | 0x20UL | 0x40UL | 0x80UL | 0x100UL | 0x800UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_S) = interruptMask;
    (void) (((CySCB_V1_Type*) (base))->INTR_S);
}
static inline void Cy_SCB_SetSlaveInterrupt(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~((0x1UL | 0x2UL | 0x4UL | 0x8UL | 0x10UL | 0x20UL | 0x40UL | 0x80UL | 0x100UL | 0x800UL)))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_S_SET) = interruptMask;
}
static inline uint32_t Cy_SCB_GetI2CInterruptStatus(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_I2C_EC) & 0x1UL);
}
static inline void Cy_SCB_SetI2CInterruptMask(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~(0x1UL))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_I2C_EC_MASK) = interruptMask;
}
static inline uint32_t Cy_SCB_GetI2CInterruptMask(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_I2C_EC_MASK));
}
static inline uint32_t Cy_SCB_GetI2CInterruptStatusMasked(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_I2C_EC_MASKED));
}
static inline void Cy_SCB_ClearI2CInterrupt(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~(0x1UL))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_I2C_EC) = interruptMask;
    (void) (((CySCB_V1_Type*) (base))->INTR_I2C_EC);
}
static inline uint32_t Cy_SCB_GetSpiInterruptStatus(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_SPI_EC) & 0x1UL);
}
static inline void Cy_SCB_SetSpiInterruptMask(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~(0x1UL))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_SPI_EC_MASK) = interruptMask;
}
static inline uint32_t Cy_SCB_GetSpiInterruptMask(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_SPI_EC_MASK));
}
static inline uint32_t Cy_SCB_GetSpiInterruptStatusMasked(CySCB_Type const *base)
{
    return ((((CySCB_V1_Type*) (base))->INTR_SPI_EC_MASKED));
}
static inline void Cy_SCB_ClearSpiInterrupt(CySCB_Type *base, uint32_t interruptMask)
{
    do { if(!(( 0UL == ((interruptMask) & ((uint32_t) ~(0x1UL))) ))) { CY_HALT(); } } while (0);
    (((CySCB_V1_Type*) (base))->INTR_SPI_EC) = interruptMask;
    (void) (((CySCB_V1_Type*) (base))->INTR_SPI_EC);
}
static inline uint32_t Cy_SCB_GetFifoSize(CySCB_Type const *base)
{
    {return (((((((CySCB_V1_Type*) (base))->CTRL)) & (0x800UL)) != 0UL) ? ((128UL)) : ((128UL) / 2UL));}
}
static inline _Bool Cy_SCB_IsRxDataWidthByte(CySCB_Type const *base)
{
    return ((((uint32_t)((((CySCB_V1_Type*) (base))->RX_CTRL)) & 0xFUL) >> 0UL) < (8UL));
}
static inline _Bool Cy_SCB_IsTxDataWidthByte(CySCB_Type const *base)
{
    return ((((uint32_t)((((CySCB_V1_Type*) (base))->TX_CTRL)) & 0xFUL) >> 0UL) < (8UL));
}
static inline void Cy_SCB_FwBlockReset(CySCB_Type *base)
{
    (((CySCB_V1_Type*) (base))->CTRL) &= (uint32_t) ~0x80000000UL;
    (((CySCB_V1_Type*) (base))->I2C_M_CMD) = 0UL;
    (((CySCB_V1_Type*) (base))->I2C_S_CMD) = 0UL;
    (((CySCB_V1_Type*) (base))->CTRL) |= (uint32_t) 0x80000000UL;
    (void) (((CySCB_V1_Type*) (base))->CTRL);
}
static inline uint32_t Cy_SCB_GetRxFifoLevel(CySCB_Type const *base)
{
    return (((uint32_t)((((CySCB_V1_Type*) (base))->RX_FIFO_CTRL)) & 0xFFUL) >> 0UL);
}
typedef enum
{
    CY_SCB_EZI2C_SUCCESS = 0U,
    CY_SCB_EZI2C_BAD_PARAM = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x0UL << (13UL)) | 1U),
} cy_en_scb_ezi2c_status_t;
typedef enum
{
    CY_SCB_EZI2C_ONE_ADDRESS,
    CY_SCB_EZI2C_TWO_ADDRESSES
} cy_en_scb_ezi2c_num_of_addr_t;
typedef enum
{
    CY_SCB_EZI2C_SUB_ADDR8_BITS,
    CY_SCB_EZI2C_SUB_ADDR16_BITS
} cy_en_scb_ezi2c_sub_addr_size_t;
typedef enum
{
    CY_SCB_EZI2C_STATE_IDLE,
    CY_SCB_EZI2C_STATE_ADDR,
    CY_SCB_EZI2C_STATE_RX_OFFSET_MSB,
    CY_SCB_EZI2C_STATE_RX_OFFSET_LSB,
    CY_SCB_EZI2C_STATE_RX_DATA0,
    CY_SCB_EZI2C_STATE_RX_DATA1,
    CY_SCB_EZI2C_STATE_TX_DATA
} cy_en_scb_ezi2c_state_t;
typedef struct cy_stc_scb_ezi2c_config
{
    cy_en_scb_ezi2c_num_of_addr_t numberOfAddresses;
    uint8_t slaveAddress1;
    uint8_t slaveAddress2;
    cy_en_scb_ezi2c_sub_addr_size_t subAddressSize;
    _Bool enableWakeFromSleep;
} cy_stc_scb_ezi2c_config_t;
typedef struct cy_stc_scb_ezi2c_context
{
    volatile cy_en_scb_ezi2c_state_t state;
    volatile uint32_t status;
    uint8_t address1;
    uint8_t address2;
    cy_en_scb_ezi2c_sub_addr_size_t subAddrSize;
    uint32_t idx;
    uint32_t baseAddr1;
    uint32_t baseAddr2;
    _Bool addr1Active;
    uint8_t *curBuf;
    uint32_t bufSize;
    uint8_t *buf1;
    uint32_t buf1Size;
    uint32_t buf1rwBondary;
    uint8_t *buf2;
    uint32_t buf2Size;
    uint32_t buf2rwBondary;
} cy_stc_scb_ezi2c_context_t;
cy_en_scb_ezi2c_status_t Cy_SCB_EZI2C_Init(CySCB_Type *base, cy_stc_scb_ezi2c_config_t const *config,
                                           cy_stc_scb_ezi2c_context_t *context);
void Cy_SCB_EZI2C_DeInit(CySCB_Type *base);
static inline void Cy_SCB_EZI2C_Enable(CySCB_Type *base);
void Cy_SCB_EZI2C_Disable(CySCB_Type *base, cy_stc_scb_ezi2c_context_t *context);
void Cy_SCB_EZI2C_SetAddress1(CySCB_Type *base, uint8_t addr, cy_stc_scb_ezi2c_context_t *context);
uint32_t Cy_SCB_EZI2C_GetAddress1(CySCB_Type const *base, cy_stc_scb_ezi2c_context_t const *context);
void Cy_SCB_EZI2C_SetAddress2(CySCB_Type *base, uint8_t addr, cy_stc_scb_ezi2c_context_t *context);
uint32_t Cy_SCB_EZI2C_GetAddress2(CySCB_Type const *base, cy_stc_scb_ezi2c_context_t const *context);
void Cy_SCB_EZI2C_SetBuffer1(CySCB_Type const *base, uint8_t *buffer, uint32_t size, uint32_t rwBoundary,
                             cy_stc_scb_ezi2c_context_t *context);
void Cy_SCB_EZI2C_SetBuffer2(CySCB_Type const *base, uint8_t *buffer, uint32_t size, uint32_t rwBoundary,
                             cy_stc_scb_ezi2c_context_t *context);
uint32_t Cy_SCB_EZI2C_GetActivity(CySCB_Type const *base, cy_stc_scb_ezi2c_context_t *context);
void Cy_SCB_EZI2C_Interrupt(CySCB_Type *base, cy_stc_scb_ezi2c_context_t *context);
cy_en_syspm_status_t Cy_SCB_EZI2C_DeepSleepCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
cy_en_syspm_status_t Cy_SCB_EZI2C_HibernateCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
static inline void Cy_SCB_EZI2C_Enable(CySCB_Type *base)
{
    (((CySCB_V1_Type*) (base))->CTRL) |= 0x80000000UL;
}
static inline void Cy_SCB_SetEzI2CMode(CySCB_Type *base, _Bool ezMode)
{
    if(ezMode)
    {
        (((CySCB_V1_Type*) (base))->CTRL) |= 0x400UL;
    }
    else
    {
        (((CySCB_V1_Type*) (base))->CTRL) &= ~(0x400UL);
    }
}
typedef enum
{
    CY_SCB_I2C_SUCCESS = 0U,
    CY_SCB_I2C_BAD_PARAM = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x1UL << (13UL)) | 1U),
    CY_SCB_I2C_MASTER_NOT_READY = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x1UL << (13UL)) | 2U),
    CY_SCB_I2C_MASTER_MANUAL_TIMEOUT = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x1UL << (13UL)) | 3U),
    CY_SCB_I2C_MASTER_MANUAL_ADDR_NAK = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x1UL << (13UL)) | 4U),
    CY_SCB_I2C_MASTER_MANUAL_NAK = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x1UL << (13UL)) | 5U),
    CY_SCB_I2C_MASTER_MANUAL_ARB_LOST = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x1UL << (13UL)) | 6U),
    CY_SCB_I2C_MASTER_MANUAL_BUS_ERR = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x1UL << (13UL)) | 7U),
    CY_SCB_I2C_MASTER_MANUAL_ABORT_START = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x1UL << (13UL)) | 8U)
} cy_en_scb_i2c_status_t;
typedef enum
{
    CY_SCB_I2C_SLAVE = 1U,
    CY_SCB_I2C_MASTER = 2U,
    CY_SCB_I2C_MASTER_SLAVE = 3U,
} cy_en_scb_i2c_mode_t;
typedef enum
{
    CY_SCB_I2C_WRITE_XFER = 0U,
    CY_SCB_I2C_READ_XFER = 1U,
} cy_en_scb_i2c_direction_t;
typedef enum
{
    CY_SCB_I2C_ACK,
    CY_SCB_I2C_NAK,
} cy_en_scb_i2c_command_t;
typedef void (* cy_cb_scb_i2c_handle_events_t)(uint32_t event);
typedef cy_en_scb_i2c_command_t (* cy_cb_scb_i2c_handle_addr_t)(uint32_t event);
typedef struct cy_stc_scb_i2c_config
{
    cy_en_scb_i2c_mode_t i2cMode;
    _Bool useRxFifo;
    _Bool useTxFifo;
    uint8_t slaveAddress;
    uint8_t slaveAddressMask;
    _Bool acceptAddrInFifo;
    _Bool ackGeneralAddr;
    _Bool enableWakeFromSleep;
    _Bool enableDigitalFilter;
    uint32_t lowPhaseDutyCycle;
    uint32_t highPhaseDutyCycle;
} cy_stc_scb_i2c_config_t;
typedef struct cy_stc_scb_i2c_context
{
    _Bool useRxFifo;
    _Bool useTxFifo;
    volatile uint32_t state;
    volatile uint32_t masterStatus;
    _Bool masterPause;
    _Bool masterRdDir;
    uint8_t *masterBuffer;
    uint32_t masterBufferSize;
    volatile uint32_t masterBufferIdx;
    volatile uint32_t masterNumBytes;
    volatile uint32_t slaveStatus;
    volatile _Bool slaveRdBufEmpty;
    uint8_t *slaveTxBuffer;
    uint32_t slaveTxBufferSize;
    volatile uint32_t slaveTxBufferIdx;
    volatile uint32_t slaveTxBufferCnt;
    uint8_t *slaveRxBuffer;
    uint32_t slaveRxBufferSize;
    volatile uint32_t slaveRxBufferIdx;
    cy_cb_scb_i2c_handle_events_t cbEvents;
    cy_cb_scb_i2c_handle_addr_t cbAddr;
} cy_stc_scb_i2c_context_t;
typedef struct cy_stc_scb_i2c_master_xfer_config
{
    uint8_t slaveAddress;
    uint8_t *buffer;
    uint32_t bufferSize;
    _Bool xferPending;
} cy_stc_scb_i2c_master_xfer_config_t;
cy_en_scb_i2c_status_t Cy_SCB_I2C_Init(CySCB_Type *base, cy_stc_scb_i2c_config_t const *config,
                                       cy_stc_scb_i2c_context_t *context);
void Cy_SCB_I2C_DeInit(CySCB_Type *base);
static inline void Cy_SCB_I2C_Enable(CySCB_Type *base);
void Cy_SCB_I2C_Disable(CySCB_Type *base, cy_stc_scb_i2c_context_t *context);
uint32_t Cy_SCB_I2C_SetDataRate(CySCB_Type *base, uint32_t dataRateHz, uint32_t scbClockHz);
uint32_t Cy_SCB_I2C_GetDataRate(CySCB_Type const *base, uint32_t scbClockHz);
static inline void Cy_SCB_I2C_SlaveSetAddress(CySCB_Type *base, uint8_t addr);
static inline uint32_t Cy_SCB_I2C_SlaveGetAddress(CySCB_Type const *base);
static inline void Cy_SCB_I2C_SlaveSetAddressMask(CySCB_Type *base, uint8_t addrMask);
static inline uint32_t Cy_SCB_I2C_SlaveGetAddressMask(CySCB_Type const *base);
static inline _Bool Cy_SCB_I2C_IsBusBusy(CySCB_Type const *base);
static inline void Cy_SCB_I2C_MasterSetLowPhaseDutyCycle (CySCB_Type *base, uint32_t clockCycles);
static inline void Cy_SCB_I2C_MasterSetHighPhaseDutyCycle(CySCB_Type *base, uint32_t clockCycles);
void Cy_SCB_I2C_SlaveConfigReadBuf (CySCB_Type const *base, uint8_t *buffer, uint32_t size,
                                    cy_stc_scb_i2c_context_t *context);
void Cy_SCB_I2C_SlaveAbortRead (CySCB_Type *base, cy_stc_scb_i2c_context_t *context);
void Cy_SCB_I2C_SlaveConfigWriteBuf(CySCB_Type const *base, uint8_t *buffer, uint32_t size,
                                    cy_stc_scb_i2c_context_t *context);
void Cy_SCB_I2C_SlaveAbortWrite (CySCB_Type *base, cy_stc_scb_i2c_context_t *context);
uint32_t Cy_SCB_I2C_SlaveGetStatus (CySCB_Type const *base, cy_stc_scb_i2c_context_t const *context);
uint32_t Cy_SCB_I2C_SlaveClearReadStatus (CySCB_Type const *base, cy_stc_scb_i2c_context_t *context);
uint32_t Cy_SCB_I2C_SlaveClearWriteStatus(CySCB_Type const *base, cy_stc_scb_i2c_context_t *context);
uint32_t Cy_SCB_I2C_SlaveGetReadTransferCount (CySCB_Type const *base, cy_stc_scb_i2c_context_t const *context);
uint32_t Cy_SCB_I2C_SlaveGetWriteTransferCount(CySCB_Type const *base, cy_stc_scb_i2c_context_t const *context);
cy_en_scb_i2c_status_t Cy_SCB_I2C_MasterWrite(CySCB_Type *base, cy_stc_scb_i2c_master_xfer_config_t *xferConfig,
                                              cy_stc_scb_i2c_context_t *context);
void Cy_SCB_I2C_MasterAbortWrite (CySCB_Type *base, cy_stc_scb_i2c_context_t *context);
cy_en_scb_i2c_status_t Cy_SCB_I2C_MasterRead (CySCB_Type *base, cy_stc_scb_i2c_master_xfer_config_t* xferConfig,
                                              cy_stc_scb_i2c_context_t *context);
void Cy_SCB_I2C_MasterAbortRead (CySCB_Type *base, cy_stc_scb_i2c_context_t *context);
uint32_t Cy_SCB_I2C_MasterGetStatus (CySCB_Type const *base, cy_stc_scb_i2c_context_t const *context);
uint32_t Cy_SCB_I2C_MasterGetTransferCount (CySCB_Type const *base, cy_stc_scb_i2c_context_t const *context);
cy_en_scb_i2c_status_t Cy_SCB_I2C_MasterSendStart (CySCB_Type *base, uint32_t address, cy_en_scb_i2c_direction_t bitRnW,
                                                    uint32_t timeoutMs, cy_stc_scb_i2c_context_t *context);
cy_en_scb_i2c_status_t Cy_SCB_I2C_MasterSendReStart(CySCB_Type *base, uint32_t address, cy_en_scb_i2c_direction_t bitRnW,
                                                    uint32_t timeoutMs, cy_stc_scb_i2c_context_t *context);
cy_en_scb_i2c_status_t Cy_SCB_I2C_MasterSendStop (CySCB_Type *base,uint32_t timeoutMs, cy_stc_scb_i2c_context_t *context);
cy_en_scb_i2c_status_t Cy_SCB_I2C_MasterReadByte (CySCB_Type *base, cy_en_scb_i2c_command_t ackNack, uint8_t *byte,
                                                    uint32_t timeoutMs, cy_stc_scb_i2c_context_t *context);
cy_en_scb_i2c_status_t Cy_SCB_I2C_MasterWriteByte (CySCB_Type *base, uint8_t byte, uint32_t timeoutMs,
                                                    cy_stc_scb_i2c_context_t *context);
void Cy_SCB_I2C_Interrupt (CySCB_Type *base, cy_stc_scb_i2c_context_t *context);
void Cy_SCB_I2C_SlaveInterrupt (CySCB_Type *base, cy_stc_scb_i2c_context_t *context);
void Cy_SCB_I2C_MasterInterrupt (CySCB_Type *base, cy_stc_scb_i2c_context_t *context);
static inline void Cy_SCB_I2C_RegisterEventCallback(CySCB_Type const *base, cy_cb_scb_i2c_handle_events_t callback,
                                                      cy_stc_scb_i2c_context_t *context);
static inline void Cy_SCB_I2C_RegisterAddrCallback (CySCB_Type const *base, cy_cb_scb_i2c_handle_addr_t callback,
                                                      cy_stc_scb_i2c_context_t *context);
cy_en_syspm_status_t Cy_SCB_I2C_DeepSleepCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
cy_en_syspm_status_t Cy_SCB_I2C_HibernateCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
static inline void Cy_SCB_I2C_Enable(CySCB_Type *base)
{
    (((CySCB_V1_Type*) (base))->CTRL) |= 0x80000000UL;
}
static inline _Bool Cy_SCB_I2C_IsBusBusy(CySCB_Type const *base)
{
    return ((((((CySCB_V1_Type*) (base))->I2C_STATUS)) & (0x1UL)) != 0UL);
}
static inline void Cy_SCB_I2C_SlaveSetAddress(CySCB_Type *base, uint8_t addr)
{
    do { if(!(( (0U == ((addr) & 0x80U)) ))) { CY_HALT(); } } while (0);
    (((((CySCB_V1_Type*) (base))->RX_MATCH)) = (((((((CySCB_V1_Type*) (base))->RX_MATCH))) & ((uint32_t)(~(0xFFUL)))) | ((((uint32_t)((((uint32_t)((uint32_t) addr << 1UL)))) << 0UL) & 0xFFUL))));
}
static inline uint32_t Cy_SCB_I2C_SlaveGetAddress(CySCB_Type const *base)
{
    return ((((uint32_t)((((CySCB_V1_Type*) (base))->RX_MATCH)) & 0xFFUL) >> 0UL) >> 1UL);
}
static inline void Cy_SCB_I2C_SlaveSetAddressMask(CySCB_Type *base, uint8_t addrMask)
{
    do { if(!(( (0U == ((addrMask) & 0x01U)) ))) { CY_HALT(); } } while (0);
    (((((CySCB_V1_Type*) (base))->RX_MATCH)) = (((((((CySCB_V1_Type*) (base))->RX_MATCH))) & ((uint32_t)(~(0xFF0000UL)))) | ((((uint32_t)((((uint32_t) addrMask))) << 16UL) & 0xFF0000UL))));
}
static inline uint32_t Cy_SCB_I2C_SlaveGetAddressMask(CySCB_Type const *base)
{
    return (((uint32_t)((((CySCB_V1_Type*) (base))->RX_MATCH)) & 0xFF0000UL) >> 16UL);
}
static inline void Cy_SCB_I2C_MasterSetLowPhaseDutyCycle(CySCB_Type *base, uint32_t clockCycles)
{
    do { if(!(( ((clockCycles) >= 7UL) && ((clockCycles) <= 16UL) ))) { CY_HALT(); } } while (0);
    (((((CySCB_V1_Type*) (base))->I2C_CTRL)) = (((((((CySCB_V1_Type*) (base))->I2C_CTRL))) & ((uint32_t)(~(0xF0UL)))) | ((((uint32_t)(((clockCycles - 1UL))) << 4UL) & 0xF0UL))));
}
static inline void Cy_SCB_I2C_MasterSetHighPhaseDutyCycle(CySCB_Type *base, uint32_t clockCycles)
{
    do { if(!(( ((clockCycles) >= 5UL) && ((clockCycles) <= 16UL) ))) { CY_HALT(); } } while (0);
    (((((CySCB_V1_Type*) (base))->I2C_CTRL)) = (((((((CySCB_V1_Type*) (base))->I2C_CTRL))) & ((uint32_t)(~(0xFUL)))) | ((((uint32_t)(((clockCycles - 1UL))) << 0UL) & 0xFUL))));
}
static inline void Cy_SCB_I2C_RegisterEventCallback(CySCB_Type const *base,
            cy_cb_scb_i2c_handle_events_t callback, cy_stc_scb_i2c_context_t *context)
{
    (void) base;
    context->cbEvents = callback;
}
static inline void Cy_SCB_I2C_RegisterAddrCallback(CySCB_Type const *base,
              cy_cb_scb_i2c_handle_addr_t callback, cy_stc_scb_i2c_context_t *context)
{
    (void) base;
    context->cbAddr = callback;
}
typedef enum
{
    CY_SCB_SPI_SUCCESS = 0U,
    CY_SCB_SPI_BAD_PARAM = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x2UL << (13UL)) | 1U),
    CY_SCB_SPI_TRANSFER_BUSY = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x2UL << (13UL)) | 2U)
} cy_en_scb_spi_status_t;
typedef enum
{
    CY_SCB_SPI_SLAVE,
    CY_SCB_SPI_MASTER,
} cy_en_scb_spi_mode_t;
typedef enum
{
    CY_SCB_SPI_MOTOROLA = 0x0U,
    CY_SCB_SPI_TI_COINCIDES = 0x01U,
    CY_SCB_SPI_NATIONAL = 0x02U,
    CY_SCB_SPI_TI_PRECEDES = 0x05U,
} cy_en_scb_spi_sub_mode_t;
typedef enum
{
    CY_SCB_SPI_CPHA0_CPOL0 = 0U,
    CY_SCB_SPI_CPHA1_CPOL0 = 1U,
    CY_SCB_SPI_CPHA0_CPOL1 = 2U,
    CY_SCB_SPI_CPHA1_CPOL1 = 3U,
} cy_en_scb_spi_sclk_mode_t;
typedef enum
{
    CY_SCB_SPI_SLAVE_SELECT0 = 0U,
    CY_SCB_SPI_SLAVE_SELECT1 = 1U,
    CY_SCB_SPI_SLAVE_SELECT2 = 2U,
    CY_SCB_SPI_SLAVE_SELECT3 = 3U,
} cy_en_scb_spi_slave_select_t;
typedef enum
{
    CY_SCB_SPI_ACTIVE_LOW = 0U,
    CY_SCB_SPI_ACTIVE_HIGH = 1U,
} cy_en_scb_spi_polarity_t;
typedef void (* cy_cb_scb_spi_handle_events_t)(uint32_t event);
typedef struct cy_stc_scb_spi_config
{
    cy_en_scb_spi_mode_t spiMode;
    cy_en_scb_spi_sub_mode_t subMode;
    cy_en_scb_spi_sclk_mode_t sclkMode;
    uint32_t oversample;
    uint32_t rxDataWidth;
    uint32_t txDataWidth;
    _Bool enableMsbFirst;
    _Bool enableFreeRunSclk;
    _Bool enableInputFilter;
    _Bool enableMisoLateSample;
    _Bool enableTransferSeperation;
    uint32_t ssPolarity;
    _Bool enableWakeFromSleep;
    uint32_t rxFifoTriggerLevel;
    uint32_t rxFifoIntEnableMask;
    uint32_t txFifoTriggerLevel;
    uint32_t txFifoIntEnableMask;
    uint32_t masterSlaveIntEnableMask;
}cy_stc_scb_spi_config_t;
typedef struct cy_stc_scb_spi_context
{
    uint32_t volatile status;
    void *rxBuf;
    uint32_t rxBufSize;
    uint32_t volatile rxBufIdx;
    void *txBuf;
    uint32_t txBufSize;
    uint32_t volatile txBufIdx;
    uint32_t volatile WriteFillSize;
    uint32_t volatile DiscardRxSize;
    uint32_t writeFill;
    cy_cb_scb_spi_handle_events_t cbEvents;
    uint32_t initKey;
} cy_stc_scb_spi_context_t;
cy_en_scb_spi_status_t Cy_SCB_SPI_Init(CySCB_Type *base, cy_stc_scb_spi_config_t const *config,
                                       cy_stc_scb_spi_context_t *context);
void Cy_SCB_SPI_DeInit (CySCB_Type *base);
static inline void Cy_SCB_SPI_Enable(CySCB_Type *base);
void Cy_SCB_SPI_Disable(CySCB_Type *base, cy_stc_scb_spi_context_t *context);
static inline void Cy_SCB_SPI_SetActiveSlaveSelect(CySCB_Type *base,
                                    cy_en_scb_spi_slave_select_t slaveSelect);
static inline void Cy_SCB_SPI_SetActiveSlaveSelectPolarity(CySCB_Type *base,
                                    cy_en_scb_spi_slave_select_t slaveSelect,
                                    cy_en_scb_spi_polarity_t polarity);
static inline _Bool Cy_SCB_SPI_IsBusBusy(CySCB_Type const *base);
cy_en_scb_spi_status_t Cy_SCB_SPI_Transfer(CySCB_Type *base, void *txBuffer, void *rxBuffer, uint32_t size,
                                           cy_stc_scb_spi_context_t *context);
cy_en_scb_spi_status_t Cy_SCB_SPI_Transfer_Buffer(CySCB_Type *base, void *txBuffer, void *rxBuffer,
                                                               uint32_t txSize, uint32_t rxSize, uint32_t writeFill,
                                                               cy_stc_scb_spi_context_t *context);
void Cy_SCB_SPI_AbortTransfer (CySCB_Type *base, cy_stc_scb_spi_context_t *context);
uint32_t Cy_SCB_SPI_GetTransferStatus(CySCB_Type const *base, cy_stc_scb_spi_context_t const *context);
uint32_t Cy_SCB_SPI_GetNumTransfered (CySCB_Type const *base, cy_stc_scb_spi_context_t const *context);
static inline uint32_t Cy_SCB_SPI_Read (CySCB_Type const *base);
static inline uint32_t Cy_SCB_SPI_ReadArray(CySCB_Type const *base, void *buffer, uint32_t size);
static inline uint32_t Cy_SCB_SPI_Write (CySCB_Type *base, uint32_t data);
static inline uint32_t Cy_SCB_SPI_WriteArray(CySCB_Type *base, void *buffer, uint32_t size);
static inline void Cy_SCB_SPI_WriteArrayBlocking(CySCB_Type *base, void *buffer, uint32_t size);
static inline uint32_t Cy_SCB_SPI_GetTxFifoStatus (CySCB_Type const *base);
static inline void Cy_SCB_SPI_ClearTxFifoStatus(CySCB_Type *base, uint32_t clearMask);
static inline uint32_t Cy_SCB_SPI_GetRxFifoStatus (CySCB_Type const *base);
static inline void Cy_SCB_SPI_ClearRxFifoStatus(CySCB_Type *base, uint32_t clearMask);
static inline uint32_t Cy_SCB_SPI_GetSlaveMasterStatus (CySCB_Type const *base);
static inline void Cy_SCB_SPI_ClearSlaveMasterStatus(CySCB_Type *base, uint32_t clearMask);
static inline uint32_t Cy_SCB_SPI_GetNumInTxFifo(CySCB_Type const *base);
static inline _Bool Cy_SCB_SPI_IsTxComplete (CySCB_Type const *base);
static inline uint32_t Cy_SCB_SPI_GetNumInRxFifo(CySCB_Type const *base);
static inline void Cy_SCB_SPI_ClearRxFifo(CySCB_Type *base);
static inline void Cy_SCB_SPI_ClearTxFifo(CySCB_Type *base);
void Cy_SCB_SPI_Interrupt(CySCB_Type *base, cy_stc_scb_spi_context_t *context);
static inline void Cy_SCB_SPI_RegisterCallback(CySCB_Type const *base, cy_cb_scb_spi_handle_events_t callback,
                                                 cy_stc_scb_spi_context_t *context);
cy_en_syspm_status_t Cy_SCB_SPI_DeepSleepCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
cy_en_syspm_status_t Cy_SCB_SPI_HibernateCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
static inline void Cy_SCB_SPI_Enable(CySCB_Type *base)
{
    (((CySCB_V1_Type*) (base))->CTRL) |= 0x80000000UL;
}
static inline _Bool Cy_SCB_SPI_IsBusBusy(CySCB_Type const *base)
{
    return ((((((CySCB_V1_Type*) (base))->SPI_STATUS)) & (0x1UL)) != 0UL);
}
static inline void Cy_SCB_SPI_SetActiveSlaveSelect(CySCB_Type *base, cy_en_scb_spi_slave_select_t slaveSelect)
{
    do { if(!(( (CY_SCB_SPI_SLAVE_SELECT0 == (slaveSelect)) || (CY_SCB_SPI_SLAVE_SELECT1 == (slaveSelect)) || (CY_SCB_SPI_SLAVE_SELECT2 == (slaveSelect)) || (CY_SCB_SPI_SLAVE_SELECT3 == (slaveSelect)) ))) { CY_HALT(); } } while (0);
    (((((CySCB_V1_Type*) (base))->SPI_CTRL)) = (((((((CySCB_V1_Type*) (base))->SPI_CTRL))) & ((uint32_t)(~(0xC000000UL)))) | ((((uint32_t)(((uint32_t) slaveSelect)) << 26UL) & 0xC000000UL))));
}
static inline void Cy_SCB_SPI_SetActiveSlaveSelectPolarity(CySCB_Type *base,
                                cy_en_scb_spi_slave_select_t slaveSelect,
                                cy_en_scb_spi_polarity_t polarity)
{
    uint32_t mask = (((uint32_t)((0x01UL << ((uint32_t)slaveSelect))) << 8UL) & (0x100UL | 0x200UL | 0x400UL | 0x800UL));
    do { if(!(( (CY_SCB_SPI_SLAVE_SELECT0 == (slaveSelect)) || (CY_SCB_SPI_SLAVE_SELECT1 == (slaveSelect)) || (CY_SCB_SPI_SLAVE_SELECT2 == (slaveSelect)) || (CY_SCB_SPI_SLAVE_SELECT3 == (slaveSelect)) ))) { CY_HALT(); } } while (0);
    do { if(!(( (CY_SCB_SPI_ACTIVE_LOW == (polarity)) || (CY_SCB_SPI_ACTIVE_HIGH == (polarity)) ))) { CY_HALT(); } } while (0);
    if (CY_SCB_SPI_ACTIVE_HIGH == polarity)
    {
        (((CySCB_V1_Type*) (base))->SPI_CTRL) |= (uint32_t) mask;
    }
    else
    {
        (((CySCB_V1_Type*) (base))->SPI_CTRL) &= (uint32_t) ~mask;
    }
}
static inline uint32_t Cy_SCB_SPI_GetRxFifoStatus(CySCB_Type const *base)
{
    return (Cy_SCB_GetRxInterruptStatus(base) & ((0x1UL) | (0x4UL) | (0x8UL) | (0x20UL) | (0x40UL)));
}
static inline void Cy_SCB_SPI_ClearRxFifoStatus(CySCB_Type *base, uint32_t clearMask)
{
    do { if(!(( 0UL == ((clearMask) & ((uint32_t) ~(((0x1UL) | (0x4UL) | (0x8UL) | (0x20UL) | (0x40UL))))) ))) { CY_HALT(); } } while (0);
    Cy_SCB_ClearRxInterrupt(base, clearMask);
}
static inline uint32_t Cy_SCB_SPI_GetNumInRxFifo(CySCB_Type const *base)
{
    return Cy_SCB_GetNumInRxFifo(base);
}
static inline void Cy_SCB_SPI_ClearRxFifo(CySCB_Type *base)
{
    Cy_SCB_ClearRxFifo(base);
}
static inline uint32_t Cy_SCB_SPI_GetTxFifoStatus(CySCB_Type const *base)
{
    return (Cy_SCB_GetTxInterruptStatus(base) & ((0x1UL) | (0x2UL) | (0x10UL) | (0x20UL) | (0x40UL)));
}
static inline void Cy_SCB_SPI_ClearTxFifoStatus(CySCB_Type *base, uint32_t clearMask)
{
    do { if(!(( 0UL == ((clearMask) & ((uint32_t) ~(((0x1UL) | (0x2UL) | (0x10UL) | (0x20UL) | (0x40UL))))) ))) { CY_HALT(); } } while (0);
    Cy_SCB_ClearTxInterrupt(base, clearMask);
}
static inline uint32_t Cy_SCB_SPI_GetNumInTxFifo(CySCB_Type const *base)
{
    return Cy_SCB_GetNumInTxFifo(base);
}
static inline _Bool Cy_SCB_SPI_IsTxComplete(CySCB_Type const *base)
{
    return Cy_SCB_IsTxComplete(base);
}
static inline void Cy_SCB_SPI_ClearTxFifo(CySCB_Type *base)
{
    Cy_SCB_ClearTxFifo(base);
}
static inline uint32_t Cy_SCB_SPI_GetSlaveMasterStatus(CySCB_Type const *base)
{
    uint32_t retStatus;
    if (((((((CySCB_V1_Type*) (base))->SPI_CTRL)) & (0x80000000UL)) != 0UL))
    {
        retStatus = (Cy_SCB_GetMasterInterruptStatus(base) & 0x200UL);
    }
    else
    {
        retStatus = (Cy_SCB_GetSlaveInterruptStatus(base) & 0x800UL);
    }
    return (retStatus);
}
static inline void Cy_SCB_SPI_ClearSlaveMasterStatus(CySCB_Type *base, uint32_t clearMask)
{
    if (((((((CySCB_V1_Type*) (base))->SPI_CTRL)) & (0x80000000UL)) != 0UL))
    {
        do { if(!(( 0UL == ((clearMask) & ((uint32_t) ~(0x200UL))) ))) { CY_HALT(); } } while (0);
        Cy_SCB_ClearMasterInterrupt(base, clearMask);
    }
    else
    {
        do { if(!(( 0UL == ((clearMask) & ((uint32_t) ~(0x800UL))) ))) { CY_HALT(); } } while (0);
        Cy_SCB_ClearSlaveInterrupt(base, clearMask);
    }
}
static inline uint32_t Cy_SCB_SPI_Read(CySCB_Type const *base)
{
    return Cy_SCB_ReadRxFifo(base);
}
static inline uint32_t Cy_SCB_SPI_ReadArray(CySCB_Type const *base, void *buffer, uint32_t size)
{
    do { if(!(( (((void *)0) != (buffer)) && ((size) > 0UL) ))) { CY_HALT(); } } while (0);
    return Cy_SCB_ReadArray(base, buffer, size);
}
static inline uint32_t Cy_SCB_SPI_Write(CySCB_Type *base, uint32_t data)
{
    return Cy_SCB_Write(base, data);
}
static inline uint32_t Cy_SCB_SPI_WriteArray(CySCB_Type *base, void *buffer, uint32_t size)
{
    do { if(!(( (((void *)0) != (buffer)) && ((size) > 0UL) ))) { CY_HALT(); } } while (0);
    return Cy_SCB_WriteArray(base, buffer, size);
}
static inline void Cy_SCB_SPI_WriteArrayBlocking(CySCB_Type *base, void *buffer, uint32_t size)
{
    do { if(!(( (((void *)0) != (buffer)) && ((size) > 0UL) ))) { CY_HALT(); } } while (0);
    Cy_SCB_WriteArrayBlocking(base, buffer, size);
}
static inline void Cy_SCB_SPI_RegisterCallback(CySCB_Type const *base,
            cy_cb_scb_spi_handle_events_t callback, cy_stc_scb_spi_context_t *context)
{
    (void) base;
    context->cbEvents = callback;
}
static inline uint32_t CY_SCB_SPI_GetSclkMode(cy_en_scb_spi_sub_mode_t subMode , cy_en_scb_spi_sclk_mode_t sclkMode)
{
    uint32_t retVal;
    switch (subMode)
    {
        case CY_SCB_SPI_TI_PRECEDES:
        case CY_SCB_SPI_TI_COINCIDES:
            retVal = (uint32_t) CY_SCB_SPI_CPHA1_CPOL0;
            break;
        case CY_SCB_SPI_NATIONAL:
            retVal = (uint32_t) CY_SCB_SPI_CPHA0_CPOL0;
            break;
        case CY_SCB_SPI_MOTOROLA:
            retVal = (uint32_t) sclkMode;
            break;
        default:
            retVal = (uint32_t) sclkMode;
            break;
    }
    return retVal;
}
typedef enum
{
    CY_SCB_UART_SUCCESS = 0U,
    CY_SCB_UART_BAD_PARAM = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x3UL << (13UL)) | 1U),
    CY_SCB_UART_RECEIVE_BUSY = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x3UL << (13UL)) | 2U),
    CY_SCB_UART_TRANSMIT_BUSY = (((uint32_t)((uint32_t)((0x2AU) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | (0x3UL << (13UL)) | 3U)
} cy_en_scb_uart_status_t;
typedef enum
{
    CY_SCB_UART_STANDARD = 0U,
    CY_SCB_UART_SMARTCARD = 1U,
    CY_SCB_UART_IRDA = 2U,
} cy_en_scb_uart_mode_t;
typedef enum
{
    CY_SCB_UART_STOP_BITS_1 = 2U,
    CY_SCB_UART_STOP_BITS_1_5 = 3U,
    CY_SCB_UART_STOP_BITS_2 = 4U,
    CY_SCB_UART_STOP_BITS_2_5 = 5U,
    CY_SCB_UART_STOP_BITS_3 = 6U,
    CY_SCB_UART_STOP_BITS_3_5 = 7U,
    CY_SCB_UART_STOP_BITS_4 = 8U,
} cy_en_scb_uart_stop_bits_t;
typedef enum
{
    CY_SCB_UART_PARITY_NONE = 0U,
    CY_SCB_UART_PARITY_EVEN = 2U,
    CY_SCB_UART_PARITY_ODD = 3U,
} cy_en_scb_uart_parity_t;
typedef enum
{
    CY_SCB_UART_ACTIVE_LOW = 0U,
    CY_SCB_UART_ACTIVE_HIGH = 1U,
} cy_en_scb_uart_polarity_t;
typedef void (* cy_cb_scb_uart_handle_events_t)(uint32_t event);
typedef struct stc_scb_uart_config
{
    cy_en_scb_uart_mode_t uartMode;
    uint32_t oversample;
    uint32_t dataWidth;
    _Bool enableMsbFirst;
    cy_en_scb_uart_stop_bits_t stopBits;
    cy_en_scb_uart_parity_t parity;
    _Bool enableInputFilter;
    _Bool dropOnParityError;
    _Bool dropOnFrameError;
    _Bool enableMutliProcessorMode;
    uint32_t receiverAddress;
    uint32_t receiverAddressMask;
    _Bool acceptAddrInFifo;
    _Bool irdaInvertRx;
    _Bool irdaEnableLowPowerReceiver;
    _Bool smartCardRetryOnNack;
    _Bool enableCts;
    cy_en_scb_uart_polarity_t ctsPolarity;
    uint32_t rtsRxFifoLevel;
    cy_en_scb_uart_polarity_t rtsPolarity;
    uint32_t breakWidth;
    uint32_t rxFifoTriggerLevel;
    uint32_t rxFifoIntEnableMask;
    uint32_t txFifoTriggerLevel;
    uint32_t txFifoIntEnableMask;
} cy_stc_scb_uart_config_t;
typedef struct cy_stc_scb_uart_context
{
    uint32_t volatile txStatus;
    uint32_t volatile rxStatus;
    void *rxRingBuf;
    uint32_t rxRingBufSize;
    uint32_t volatile rxRingBufHead;
    uint32_t volatile rxRingBufTail;
    void *rxBuf;
    uint32_t rxBufSize;
    uint32_t volatile rxBufIdx;
    void *txBuf;
    uint32_t txBufSize;
    uint32_t volatile txLeftToTransmit;
    _Bool irdaEnableLowPowerReceiver;
    cy_cb_scb_uart_handle_events_t cbEvents;
    uint32_t initKey;
} cy_stc_scb_uart_context_t;
cy_en_scb_uart_status_t Cy_SCB_UART_Init(CySCB_Type *base, cy_stc_scb_uart_config_t const *config,
                                         cy_stc_scb_uart_context_t *context);
void Cy_SCB_UART_DeInit (CySCB_Type *base);
static inline void Cy_SCB_UART_Enable(CySCB_Type *base);
void Cy_SCB_UART_Disable(CySCB_Type *base, cy_stc_scb_uart_context_t *context);
static inline void Cy_SCB_UART_EnableCts (CySCB_Type *base);
static inline void Cy_SCB_UART_DisableCts (CySCB_Type *base);
static inline void Cy_SCB_UART_SetRtsFifoLevel(CySCB_Type *base, uint32_t level);
static inline uint32_t Cy_SCB_UART_GetRtsFifoLevel(CySCB_Type const *base);
static inline void Cy_SCB_UART_EnableSkipStart (CySCB_Type *base);
static inline void Cy_SCB_UART_DisableSkipStart(CySCB_Type *base);
void Cy_SCB_UART_StartRingBuffer (CySCB_Type *base, void *buffer, uint32_t size,
                                        cy_stc_scb_uart_context_t *context);
void Cy_SCB_UART_StopRingBuffer (CySCB_Type *base, cy_stc_scb_uart_context_t *context);
uint32_t Cy_SCB_UART_GetNumInRingBuffer(CySCB_Type const *base, cy_stc_scb_uart_context_t const *context);
void Cy_SCB_UART_ClearRingBuffer (CySCB_Type const *base, cy_stc_scb_uart_context_t *context);
cy_en_scb_uart_status_t Cy_SCB_UART_Receive(CySCB_Type *base, void *buffer, uint32_t size,
                                            cy_stc_scb_uart_context_t *context);
void Cy_SCB_UART_AbortReceive (CySCB_Type *base, cy_stc_scb_uart_context_t *context);
uint32_t Cy_SCB_UART_GetReceiveStatus(CySCB_Type const *base, cy_stc_scb_uart_context_t const *context);
uint32_t Cy_SCB_UART_GetNumReceived (CySCB_Type const *base, cy_stc_scb_uart_context_t const *context);
cy_en_scb_uart_status_t Cy_SCB_UART_Transmit(CySCB_Type *base, void *buffer, uint32_t size,
                                             cy_stc_scb_uart_context_t *context);
void Cy_SCB_UART_AbortTransmit (CySCB_Type *base, cy_stc_scb_uart_context_t *context);
uint32_t Cy_SCB_UART_GetTransmitStatus (CySCB_Type const *base, cy_stc_scb_uart_context_t const *context);
uint32_t Cy_SCB_UART_GetNumLeftToTransmit(CySCB_Type const *base, cy_stc_scb_uart_context_t const *context);
static inline uint32_t Cy_SCB_UART_Put (CySCB_Type *base, uint32_t data);
static inline uint32_t Cy_SCB_UART_PutArray (CySCB_Type *base, void *buffer, uint32_t size);
static inline void Cy_SCB_UART_PutArrayBlocking(CySCB_Type *base, void *buffer, uint32_t size);
static inline void Cy_SCB_UART_PutString (CySCB_Type *base, char_t const string[]);
void Cy_SCB_UART_SendBreakBlocking(CySCB_Type *base, uint32_t breakWidth);
static inline uint32_t Cy_SCB_UART_Get (CySCB_Type const *base);
static inline uint32_t Cy_SCB_UART_GetArray (CySCB_Type const *base, void *buffer, uint32_t size);
static inline void Cy_SCB_UART_GetArrayBlocking(CySCB_Type const *base, void *buffer, uint32_t size);
static inline uint32_t Cy_SCB_UART_GetTxFifoStatus (CySCB_Type const *base);
static inline void Cy_SCB_UART_ClearTxFifoStatus(CySCB_Type *base, uint32_t clearMask);
static inline uint32_t Cy_SCB_UART_GetRxFifoStatus (CySCB_Type const *base);
static inline void Cy_SCB_UART_ClearRxFifoStatus(CySCB_Type *base, uint32_t clearMask);
static inline uint32_t Cy_SCB_UART_GetNumInTxFifo (CySCB_Type const *base);
static inline _Bool Cy_SCB_UART_IsTxComplete (CySCB_Type const *base);
static inline uint32_t Cy_SCB_UART_GetNumInRxFifo (CySCB_Type const *base);
static inline void Cy_SCB_UART_ClearRxFifo (CySCB_Type *base);
static inline void Cy_SCB_UART_ClearTxFifo (CySCB_Type *base);
static inline uint32_t Cy_SCB_UART_GetOverSample(CySCB_Type const *base);
cy_en_scb_uart_status_t Cy_SCB_UART_SetOverSample(CySCB_Type *base, uint32_t overSample, cy_stc_scb_uart_context_t *context);
static inline uint32_t Cy_SCB_UART_GetDataWidth(CySCB_Type const *base);
void Cy_SCB_UART_SetDataWidth(CySCB_Type *base, uint32_t dataWidth);
static inline uint32_t Cy_SCB_UART_GetParity(CySCB_Type const *base);
void Cy_SCB_UART_SetParity(CySCB_Type *base, cy_en_scb_uart_parity_t parity);
static inline uint32_t Cy_SCB_UART_GetStopBits(CySCB_Type const *base);
void Cy_SCB_UART_SetStopBits(CySCB_Type *base, cy_en_scb_uart_stop_bits_t stopBits);
static inline _Bool Cy_SCB_UART_GetDropOnParityError(CySCB_Type const *base);
void Cy_SCB_UART_SetDropOnParityError(CySCB_Type *base, _Bool dropOnParityError);
static inline _Bool Cy_SCB_UART_GetEnableMsbFirst(CySCB_Type const *base);
void Cy_SCB_UART_SetEnableMsbFirst(CySCB_Type *base, _Bool enableMsbFirst);
void Cy_SCB_UART_Interrupt(CySCB_Type *base, cy_stc_scb_uart_context_t *context);
static inline void Cy_SCB_UART_RegisterCallback(CySCB_Type const *base, cy_cb_scb_uart_handle_events_t callback,
                                                  cy_stc_scb_uart_context_t *context);
cy_en_syspm_status_t Cy_SCB_UART_DeepSleepCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
cy_en_syspm_status_t Cy_SCB_UART_HibernateCallback(cy_stc_syspm_callback_params_t *callbackParams, cy_en_syspm_callback_mode_t mode);
static inline void Cy_SCB_UART_Enable(CySCB_Type *base)
{
    (((CySCB_V1_Type*) (base))->CTRL) |= 0x80000000UL;
}
static inline void Cy_SCB_UART_EnableCts(CySCB_Type *base)
{
    (((CySCB_V1_Type*) (base))->UART_FLOW_CTRL) |= 0x2000000UL;
}
static inline void Cy_SCB_UART_DisableCts(CySCB_Type *base)
{
    (((CySCB_V1_Type*) (base))->UART_FLOW_CTRL) &= (uint32_t) ~0x2000000UL;
}
static inline void Cy_SCB_UART_SetRtsFifoLevel(CySCB_Type *base, uint32_t level)
{
    do { if(!(((level) < Cy_SCB_GetFifoSize(base)))) { CY_HALT(); } } while (0);
    (((((CySCB_V1_Type*) (base))->UART_FLOW_CTRL)) = (((((((CySCB_V1_Type*) (base))->UART_FLOW_CTRL))) & ((uint32_t)(~(0xFFUL)))) | ((((uint32_t)((level)) << 0UL) & 0xFFUL))));
}
static inline uint32_t Cy_SCB_UART_GetRtsFifoLevel(CySCB_Type const *base)
{
    return (((uint32_t)((((CySCB_V1_Type*) (base))->UART_FLOW_CTRL)) & 0xFFUL) >> 0UL);
}
static inline void Cy_SCB_UART_EnableSkipStart(CySCB_Type *base)
{
    (((CySCB_V1_Type*) (base))->UART_RX_CTRL) |= 0x2000UL;
}
static inline void Cy_SCB_UART_DisableSkipStart(CySCB_Type *base)
{
    (((CySCB_V1_Type*) (base))->UART_RX_CTRL) &= (uint32_t) ~0x2000UL;
}
static inline uint32_t Cy_SCB_UART_GetOverSample(CySCB_Type const *base)
{
    return ((((uint32_t)((((CySCB_V1_Type*) (base))->CTRL)) & 0xFUL) >> 0UL)+1UL);
}
static inline uint32_t Cy_SCB_UART_GetDataWidth(CySCB_Type const *base)
{
    return ((((uint32_t)((((CySCB_V1_Type*) (base))->TX_CTRL)) & 0xFUL) >> 0UL)+1UL);
}
static inline uint32_t Cy_SCB_UART_GetParity(CySCB_Type const *base)
{
    return (((uint32_t)((((CySCB_V1_Type*) (base))->UART_TX_CTRL)) & (0x20UL | 0x10UL)) >> 4UL);
}
static inline uint32_t Cy_SCB_UART_GetStopBits(CySCB_Type const *base)
{
    return ((((uint32_t)((((CySCB_V1_Type*) (base))->UART_TX_CTRL)) & 0x7UL) >> 0UL)+1UL);
}
static inline _Bool Cy_SCB_UART_GetDropOnParityError(CySCB_Type const *base)
{
    return ((((((CySCB_V1_Type*) (base))->UART_RX_CTRL)) & (0x100UL)) != 0UL);
}
static inline _Bool Cy_SCB_UART_GetEnableMsbFirst(CySCB_Type const *base)
{
    return ((((((CySCB_V1_Type*) (base))->TX_CTRL)) & (0x100UL)) != 0UL);
}
static inline uint32_t Cy_SCB_UART_Get(CySCB_Type const *base)
{
    return Cy_SCB_ReadRxFifo(base);
}
static inline uint32_t Cy_SCB_UART_GetArray(CySCB_Type const *base, void *buffer, uint32_t size)
{
    do { if(!(( (((void *)0) != (buffer)) && ((size) > 0UL) ))) { CY_HALT(); } } while (0);
    return Cy_SCB_ReadArray(base, buffer, size);
}
static inline void Cy_SCB_UART_GetArrayBlocking(CySCB_Type const *base, void *buffer, uint32_t size)
{
    do { if(!(( (((void *)0) != (buffer)) && ((size) > 0UL) ))) { CY_HALT(); } } while (0);
    Cy_SCB_ReadArrayBlocking(base, buffer, size);
}
static inline uint32_t Cy_SCB_UART_GetRxFifoStatus(CySCB_Type const *base)
{
    return (Cy_SCB_GetRxInterruptStatus(base) & ((0x1UL) | (0x4UL) | (0x8UL) | (0x20UL) | (0x40UL) | (0x100UL) | (0x200UL) | (0x800UL)));
}
static inline void Cy_SCB_UART_ClearRxFifoStatus(CySCB_Type *base, uint32_t clearMask)
{
    do { if(!(( 0UL == ((clearMask) & ((uint32_t) ~(((0x1UL) | (0x4UL) | (0x8UL) | (0x20UL) | (0x40UL) | (0x100UL) | (0x200UL) | (0x800UL))))) ))) { CY_HALT(); } } while (0);
    Cy_SCB_ClearRxInterrupt(base, clearMask);
}
static inline uint32_t Cy_SCB_UART_GetNumInRxFifo(CySCB_Type const *base)
{
    return Cy_SCB_GetNumInRxFifo(base);
}
static inline void Cy_SCB_UART_ClearRxFifo(CySCB_Type *base)
{
    Cy_SCB_ClearRxFifo(base);
}
static inline uint32_t Cy_SCB_UART_Put(CySCB_Type *base, uint32_t data)
{
    return Cy_SCB_Write(base, data);
}
static inline uint32_t Cy_SCB_UART_PutArray(CySCB_Type *base, void *buffer, uint32_t size)
{
    do { if(!(( (((void *)0) != (buffer)) && ((size) > 0UL) ))) { CY_HALT(); } } while (0);
    return Cy_SCB_WriteArray(base, buffer, size);
}
static inline void Cy_SCB_UART_PutArrayBlocking(CySCB_Type *base, void *buffer, uint32_t size)
{
    do { if(!(( (((void *)0) != (buffer)) && ((size) > 0UL) ))) { CY_HALT(); } } while (0);
    Cy_SCB_WriteArrayBlocking(base, buffer, size);
}
static inline void Cy_SCB_UART_PutString(CySCB_Type *base, char_t const string[])
{
    do { if(!(( (((void *)0) != (string)) && ((1UL) > 0UL) ))) { CY_HALT(); } } while (0);
    Cy_SCB_WriteString(base, string);
}
static inline uint32_t Cy_SCB_UART_GetTxFifoStatus(CySCB_Type const *base)
{
    return (Cy_SCB_GetTxInterruptStatus(base) & ((0x1UL) | (0x2UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x200UL) | (0x100UL) | (0x400UL)));
}
static inline void Cy_SCB_UART_ClearTxFifoStatus(CySCB_Type *base, uint32_t clearMask)
{
    do { if(!(( 0UL == ((clearMask) & ((uint32_t) ~(((0x1UL) | (0x2UL) | (0x10UL) | (0x20UL) | (0x40UL) | (0x200UL) | (0x100UL) | (0x400UL))))) ))) { CY_HALT(); } } while (0);
    Cy_SCB_ClearTxInterrupt(base, clearMask);
}
static inline uint32_t Cy_SCB_UART_GetNumInTxFifo(CySCB_Type const *base)
{
    return Cy_SCB_GetNumInTxFifo(base);
}
static inline _Bool Cy_SCB_UART_IsTxComplete(CySCB_Type const *base)
{
    return Cy_SCB_IsTxComplete(base);
}
static inline void Cy_SCB_UART_ClearTxFifo(CySCB_Type *base)
{
    Cy_SCB_ClearTxFifo(base);
}
static inline void Cy_SCB_UART_RegisterCallback(CySCB_Type const *base,
          cy_cb_scb_uart_handle_events_t callback, cy_stc_scb_uart_context_t *context)
{
    (void) base;
    context->cbEvents = callback;
}
typedef enum
{
    CY_SEGLCD_SUCCESS = 0x0UL,
    CY_SEGLCD_BAD_PARAM = (((uint32_t)((uint32_t)((0x40u) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01UL,
    CY_SEGLCD_BAD_PIXEL = (((uint32_t)((uint32_t)((0x40u) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02UL,
    CY_SEGLCD_BAD_CHAR = (((uint32_t)((uint32_t)((0x40u) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x04UL,
    CY_SEGLCD_EXCEED = (((uint32_t)((uint32_t)((0x40u) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_WARNING << ((16U))) | 0x08UL,
    CY_SEGLCD_CUSTOM = (((uint32_t)((uint32_t)((0x40u) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_INFO << ((16U))) | 0x10UL,
} cy_en_seglcd_status_t;
typedef enum
{
    CY_SEGLCD_SPEED_LOW = 0x0UL,
    CY_SEGLCD_SPEED_HIGH = 0x1UL
} cy_en_seglcd_speed_t;
typedef enum
{
    CY_SEGLCD_LSCLK_LF = 0x0UL,
    CY_SEGLCD_LSCLK_MF = 0x1UL
} cy_en_seglcd_lsclk_t;
typedef enum
{
    CY_SEGLCD_TYPE_A = 0x0UL,
    CY_SEGLCD_TYPE_B = 0x1UL
} cy_en_seglcd_wave_t;
typedef enum
{
    CY_SEGLCD_PWM = 0x0UL,
    CY_SEGLCD_CORRELATION = 0x1UL
} cy_en_seglcd_drive_t;
typedef enum
{
    CY_SEGLCD_BIAS_HALF = 0x0UL,
    CY_SEGLCD_BIAS_THIRD = 0x1UL,
    CY_SEGLCD_BIAS_FOURTH = 0x2UL,
    CY_SEGLCD_BIAS_FIFTH = 0x3UL,
} cy_en_seglcd_bias_t;
typedef enum
{
    CY_SEGLCD_BAR = 1U,
    CY_SEGLCD_7SEG = 7U,
    CY_SEGLCD_14SEG = 14U,
    CY_SEGLCD_16SEG = 16U,
    CY_SEGLCD_5X8DM = 40U
} cy_en_seglcd_disp_t;
typedef struct
{
    cy_en_seglcd_speed_t speed;
    cy_en_seglcd_wave_t wave;
    cy_en_seglcd_drive_t drive;
    cy_en_seglcd_bias_t bias;
    cy_en_seglcd_lsclk_t lsClk;
    uint8_t comNum;
    uint8_t frRate;
    uint8_t contrast;
    uint32_t clkFreq;
} cy_stc_seglcd_config_t;
typedef struct
{
    char_t first;
    char_t last;
    _Bool ascii;
    uint8_t const * fontMap;
} cy_stc_seglcd_font_t;
typedef struct
{
    uint16_t type;
    uint16_t symNum;
    _Bool invert;
    uint32_t const * pixMap;
    cy_stc_seglcd_font_t const * font;
} cy_stc_seglcd_disp_t;
extern const cy_stc_seglcd_font_t cy_segLCD_7SegFont;
extern const cy_stc_seglcd_font_t cy_segLCD_14SegFont;
extern const cy_stc_seglcd_font_t cy_segLCD_16SegFont;
extern const cy_stc_seglcd_font_t cy_segLCD_5x8DmFont;
cy_en_seglcd_status_t Cy_SegLCD_Init (LCD_Type * base, cy_stc_seglcd_config_t const * config);
cy_en_seglcd_status_t Cy_SegLCD_Contrast(LCD_Type * base, uint32_t contrast, cy_stc_seglcd_config_t * config);
                 void Cy_SegLCD_Deinit (LCD_Type * base);
                 void Cy_SegLCD_Enable (LCD_Type * base);
                 void Cy_SegLCD_Disable (LCD_Type * base);
cy_en_seglcd_status_t Cy_SegLCD_WriteChar (LCD_Type * base, char_t character, uint32_t position, cy_stc_seglcd_disp_t const * display);
cy_en_seglcd_status_t Cy_SegLCD_WriteString(LCD_Type * base, char_t const * string, uint32_t position, cy_stc_seglcd_disp_t const * display);
cy_en_seglcd_status_t Cy_SegLCD_WriteNumber(LCD_Type * base, uint32_t value, uint32_t position, cy_stc_seglcd_disp_t const * display, _Bool zeroes, _Bool hex);
cy_en_seglcd_status_t Cy_SegLCD_BarGraph (LCD_Type * base, uint32_t value, uint32_t position, cy_stc_seglcd_disp_t const * display);
                cy_en_seglcd_status_t Cy_SegLCD_ClrFrame (LCD_Type * base, uint32_t const * commons);
                cy_en_seglcd_status_t Cy_SegLCD_InvFrame (LCD_Type * base, uint32_t const * commons);
                cy_en_seglcd_status_t Cy_SegLCD_WritePixel(LCD_Type * base, uint32_t pixel, _Bool value);
                                 _Bool Cy_SegLCD_ReadPixel (LCD_Type * base, uint32_t pixel);
static inline cy_en_seglcd_status_t Cy_SegLCD_SetPixel (LCD_Type * base, uint32_t pixel);
static inline cy_en_seglcd_status_t Cy_SegLCD_ClrPixel (LCD_Type * base, uint32_t pixel);
static inline cy_en_seglcd_status_t Cy_SegLCD_InvPixel (LCD_Type * base, uint32_t pixel);
static inline cy_en_seglcd_status_t Cy_SegLCD_SetPixel(LCD_Type * base, uint32_t pixel)
{
    return (Cy_SegLCD_WritePixel(base, pixel, 1));
}
static inline cy_en_seglcd_status_t Cy_SegLCD_ClrPixel(LCD_Type * base, uint32_t pixel)
{
    return (Cy_SegLCD_WritePixel(base, pixel, 0));
}
static inline cy_en_seglcd_status_t Cy_SegLCD_InvPixel(LCD_Type * base, uint32_t pixel)
{
    return (Cy_SegLCD_WritePixel(base, pixel, !Cy_SegLCD_ReadPixel(base, pixel)));
}

typedef enum
{
    CY_SMARTIO_SUCCESS = 0x00u,
    CY_SMARTIO_BAD_PARAM = ((uint32_t)((uint32_t)((0x42u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01u,
    CY_SMARTIO_LOCKED = ((uint32_t)((uint32_t)((0x42u) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02u,
} cy_en_smartio_status_t;
typedef enum {
    CY_SMARTIO_CLK_IO0 = 0,
    CY_SMARTIO_CLK_IO1 = 1,
    CY_SMARTIO_CLK_IO2 = 2,
    CY_SMARTIO_CLK_IO3 = 3,
    CY_SMARTIO_CLK_IO4 = 4,
    CY_SMARTIO_CLK_IO5 = 5,
    CY_SMARTIO_CLK_IO6 = 6,
    CY_SMARTIO_CLK_IO7 = 7,
    CY_SMARTIO_CLK_CHIP0 = 8,
    CY_SMARTIO_CLK_CHIP1 = 9,
    CY_SMARTIO_CLK_CHIP2 = 10,
    CY_SMARTIO_CLK_CHIP3 = 11,
    CY_SMARTIO_CLK_CHIP4 = 12,
    CY_SMARTIO_CLK_CHIP5 = 13,
    CY_SMARTIO_CLK_CHIP6 = 14,
    CY_SMARTIO_CLK_CHIP7 = 15,
    CY_SMARTIO_CLK_DIVACT = 16,
    CY_SMARTIO_CLK_DIVDS = 17,
    CY_SMARTIO_CLK_DIVHIB = 18,
    CY_SMARTIO_CLK_LFCLK = 19,
    CY_SMARTIO_CLK_GATED = 20,
    CY_SMARTIO_CLK_ASYNC = 31,
}cy_en_smartio_clksrc_t;
typedef enum {
    CY_SMARTIO_LUT0 = 0,
    CY_SMARTIO_LUT1 = 1,
    CY_SMARTIO_LUT2 = 2,
    CY_SMARTIO_LUT3 = 3,
    CY_SMARTIO_LUT4 = 4,
    CY_SMARTIO_LUT5 = 5,
    CY_SMARTIO_LUT6 = 6,
    CY_SMARTIO_LUT7 = 7,
}cy_en_smartio_lutnum_t;
typedef enum {
    CY_SMARTIO_TR0 = 0,
    CY_SMARTIO_TR1 = 1,
    CY_SMARTIO_TR2 = 2,
}cy_en_smartio_trnum_t;
typedef enum {
    CY_SMARTIO_DATA0 = 0,
    CY_SMARTIO_DATA1 = 1,
}cy_en_smartio_datanum_t;
typedef enum {
    CY_SMARTIO_LUTTR_DU_OUT = 0,
    CY_SMARTIO_LUTTR_LUT0_OUT = 0,
    CY_SMARTIO_LUTTR_LUT1_OUT = 1,
    CY_SMARTIO_LUTTR_LUT2_OUT = 2,
    CY_SMARTIO_LUTTR_LUT3_OUT = 3,
    CY_SMARTIO_LUTTR_LUT4_OUT = 4,
    CY_SMARTIO_LUTTR_LUT5_OUT = 5,
    CY_SMARTIO_LUTTR_LUT6_OUT = 6,
    CY_SMARTIO_LUTTR_LUT7_OUT = 7,
    CY_SMARTIO_LUTTR_CHIP0 = 8,
    CY_SMARTIO_LUTTR_CHIP4 = 8,
    CY_SMARTIO_LUTTR_CHIP1 = 9,
    CY_SMARTIO_LUTTR_CHIP5 = 9,
    CY_SMARTIO_LUTTR_CHIP2 = 10,
    CY_SMARTIO_LUTTR_CHIP6 = 10,
    CY_SMARTIO_LUTTR_CHIP3 = 11,
    CY_SMARTIO_LUTTR_CHIP7 = 11,
    CY_SMARTIO_LUTTR_IO0 = 12,
    CY_SMARTIO_LUTTR_IO4 = 12,
    CY_SMARTIO_LUTTR_IO1 = 13,
    CY_SMARTIO_LUTTR_IO5 = 13,
    CY_SMARTIO_LUTTR_IO2 = 14,
    CY_SMARTIO_LUTTR_IO6 = 14,
    CY_SMARTIO_LUTTR_IO3 = 15,
    CY_SMARTIO_LUTTR_IO7 = 15,
    CY_SMARTIO_LUTTR_INVALID = 255,
}cy_en_smartio_luttr_t;
typedef enum {
    CY_SMARTIO_LUTOPC_COMB = 0,
    CY_SMARTIO_LUTOPC_GATED_TR2 = 1,
    CY_SMARTIO_LUTOPC_GATED_OUT = 2,
    CY_SMARTIO_LUTOPC_ASYNC_SR = 3,
}cy_en_smartio_lutopc_t;
typedef enum {
    CY_SMARTIO_DUTR_ZERO = 0,
    CY_SMARTIO_DUTR_ONE = 1,
    CY_SMARTIO_DUTR_DU_OUT = 2,
    CY_SMARTIO_DUTR_LUT0_OUT = 3,
    CY_SMARTIO_DUTR_LUT1_OUT = 4,
    CY_SMARTIO_DUTR_LUT2_OUT = 5,
    CY_SMARTIO_DUTR_LUT3_OUT = 6,
    CY_SMARTIO_DUTR_LUT4_OUT = 7,
    CY_SMARTIO_DUTR_LUT5_OUT = 8,
    CY_SMARTIO_DUTR_LUT6_OUT = 9,
    CY_SMARTIO_DUTR_LUT7_OUT = 10,
    CY_SMARTIO_DUTR_INVALID = 255,
}cy_en_smartio_dutr_t;
typedef enum {
    CY_SMARTIO_DUDATA_ZERO = 0,
    CY_SMARTIO_DUDATA_CHIP = 1,
    CY_SMARTIO_DUDATA_IO = 2,
    CY_SMARTIO_DUDATA_DATAREG = 3,
}cy_en_smartio_dudata_t;
typedef enum {
    CY_SMARTIO_DUOPC_INCR = 1,
    CY_SMARTIO_DUOPC_DECR = 2,
    CY_SMARTIO_DUOPC_INCR_WRAP = 3,
    CY_SMARTIO_DUOPC_DECR_WRAP = 4,
    CY_SMARTIO_DUOPC_INCR_DECR = 5,
    CY_SMARTIO_DUOPC_INCR_DECR_WRAP = 6,
    CY_SMARTIO_DUOPC_ROR = 7,
    CY_SMARTIO_DUOPC_SHR = 8,
    CY_SMARTIO_DUOPC_AND_OR = 9,
    CY_SMARTIO_DUOPC_SHR_MAJ3 = 10,
    CY_SMARTIO_DUOPC_SHR_EQL = 11,
}cy_en_smartio_duopc_t;
typedef enum {
    CY_SMARTIO_DUSIZE_1 = 0,
    CY_SMARTIO_DUSIZE_2 = 1,
    CY_SMARTIO_DUSIZE_3 = 2,
    CY_SMARTIO_DUSIZE_4 = 3,
    CY_SMARTIO_DUSIZE_5 = 4,
    CY_SMARTIO_DUSIZE_6 = 5,
    CY_SMARTIO_DUSIZE_7 = 6,
    CY_SMARTIO_DUSIZE_8 = 7,
}cy_en_smartio_dusize_t;
typedef struct {
    cy_en_smartio_luttr_t tr0;
    cy_en_smartio_luttr_t tr1;
    cy_en_smartio_luttr_t tr2;
    cy_en_smartio_lutopc_t opcode;
    uint8_t lutMap;
}cy_stc_smartio_lutcfg_t;
typedef struct {
    cy_en_smartio_dutr_t tr0;
    cy_en_smartio_dutr_t tr1;
    cy_en_smartio_dutr_t tr2;
    cy_en_smartio_dudata_t data0;
    cy_en_smartio_dudata_t data1;
    cy_en_smartio_duopc_t opcode;
    cy_en_smartio_dusize_t size;
    uint8_t dataReg;
}cy_stc_smartio_ducfg_t;
typedef struct {
    cy_en_smartio_clksrc_t clkSrc;
    uint8_t bypassMask;
    uint8_t ioSyncEn;
    uint8_t chipSyncEn;
    const cy_stc_smartio_lutcfg_t* lutCfg0;
    const cy_stc_smartio_lutcfg_t* lutCfg1;
    const cy_stc_smartio_lutcfg_t* lutCfg2;
    const cy_stc_smartio_lutcfg_t* lutCfg3;
    const cy_stc_smartio_lutcfg_t* lutCfg4;
    const cy_stc_smartio_lutcfg_t* lutCfg5;
    const cy_stc_smartio_lutcfg_t* lutCfg6;
    const cy_stc_smartio_lutcfg_t* lutCfg7;
    const cy_stc_smartio_ducfg_t* duCfg;
    _Bool hldOvr;
}cy_stc_smartio_config_t;
cy_en_smartio_status_t Cy_SmartIO_Init(SMARTIO_PRT_Type* base, const cy_stc_smartio_config_t* config);
void Cy_SmartIO_Deinit(SMARTIO_PRT_Type* base);
void Cy_SmartIO_Enable(SMARTIO_PRT_Type* base);
void Cy_SmartIO_Disable(SMARTIO_PRT_Type* base);
static inline uint8_t Cy_SmartIO_GetChBypass(SMARTIO_PRT_Type* base);
cy_en_smartio_status_t Cy_SmartIO_SetChBypass(SMARTIO_PRT_Type* base, uint8_t bypassMask);
static inline cy_en_smartio_clksrc_t Cy_SmartIO_GetClock(SMARTIO_PRT_Type* base);
cy_en_smartio_status_t Cy_SmartIO_SetClock(SMARTIO_PRT_Type* base, cy_en_smartio_clksrc_t clkSrc);
static inline uint8_t Cy_SmartIO_GetIoSync(SMARTIO_PRT_Type* base);
cy_en_smartio_status_t Cy_SmartIO_SetIoSync(SMARTIO_PRT_Type* base, uint8_t ioSyncEn);
static inline uint8_t Cy_SmartIO_GetChipSync(SMARTIO_PRT_Type* base);
cy_en_smartio_status_t Cy_SmartIO_SetChipSync(SMARTIO_PRT_Type* base, uint8_t chipSyncEn);
cy_en_smartio_status_t Cy_SmartIO_HoldOverride(SMARTIO_PRT_Type* base, _Bool hldOvr);
cy_en_smartio_luttr_t Cy_SmartIO_GetLutTr(SMARTIO_PRT_Type* base, cy_en_smartio_lutnum_t lutNum, cy_en_smartio_trnum_t trNum);
cy_en_smartio_status_t Cy_SmartIO_SetLutTr(SMARTIO_PRT_Type* base, cy_en_smartio_lutnum_t lutNum, cy_en_smartio_trnum_t trNum, cy_en_smartio_luttr_t trSrc);
cy_en_smartio_status_t Cy_SmartIO_SetLutTrAll(SMARTIO_PRT_Type* base, cy_en_smartio_lutnum_t lutNum, cy_en_smartio_luttr_t trSrc);
static inline cy_en_smartio_lutopc_t Cy_SmartIO_GetLutOpcode(SMARTIO_PRT_Type* base, cy_en_smartio_lutnum_t lutNum);
cy_en_smartio_status_t Cy_SmartIO_SetLutOpcode(SMARTIO_PRT_Type* base, cy_en_smartio_lutnum_t lutNum, cy_en_smartio_lutopc_t opcode);
static inline uint8_t Cy_SmartIO_GetLutMap(SMARTIO_PRT_Type* base, cy_en_smartio_lutnum_t lutNum);
cy_en_smartio_status_t Cy_SmartIO_SetLutMap(SMARTIO_PRT_Type* base, cy_en_smartio_lutnum_t lutNum, uint8_t lutMap);
cy_en_smartio_dutr_t Cy_SmartIO_GetDuTr(SMARTIO_PRT_Type* base, cy_en_smartio_trnum_t trNum);
cy_en_smartio_status_t Cy_SmartIO_SetDuTr(SMARTIO_PRT_Type* base, cy_en_smartio_trnum_t trNum, cy_en_smartio_dutr_t trSrc);
cy_en_smartio_status_t Cy_SmartIO_SetDuTrAll(SMARTIO_PRT_Type* base, cy_en_smartio_dutr_t trSrc);
static inline cy_en_smartio_dudata_t Cy_SmartIO_GetDuData(SMARTIO_PRT_Type* base, cy_en_smartio_datanum_t dataNum);
cy_en_smartio_status_t Cy_SmartIO_SetDuData(SMARTIO_PRT_Type* base, cy_en_smartio_datanum_t dataNum, cy_en_smartio_dudata_t dataSrc);
static inline cy_en_smartio_duopc_t Cy_SmartIO_GetDuOpc(SMARTIO_PRT_Type* base);
static inline cy_en_smartio_dusize_t Cy_SmartIO_GetDuSize(SMARTIO_PRT_Type* base);
cy_en_smartio_status_t Cy_SmartIO_SetDuOperation(SMARTIO_PRT_Type* base, cy_en_smartio_duopc_t opcode, cy_en_smartio_dusize_t size);
static inline uint8_t Cy_SmartIO_GetDataReg(SMARTIO_PRT_Type* base);
cy_en_smartio_status_t Cy_SmartIO_SetDataReg(SMARTIO_PRT_Type* base, uint8_t dataReg);
static inline uint8_t Cy_SmartIO_GetChBypass(SMARTIO_PRT_Type* base)
{
    return((uint8_t)(((uint32_t)((((SMARTIO_PRT_Type *)(base))->CTL)) & 0xFFUL) >> 0UL));
}
static inline cy_en_smartio_clksrc_t Cy_SmartIO_GetClock(SMARTIO_PRT_Type* base)
{
    return((cy_en_smartio_clksrc_t)(((uint32_t)((((SMARTIO_PRT_Type *)(base))->CTL)) & 0x1F00UL) >> 8UL));
}
static inline uint8_t Cy_SmartIO_GetIoSync(SMARTIO_PRT_Type* base)
{
    return((uint8_t)(((uint32_t)((((SMARTIO_PRT_Type *)(base))->SYNC_CTL)) & 0xFFUL) >> 0UL));
}
static inline uint8_t Cy_SmartIO_GetChipSync(SMARTIO_PRT_Type* base)
{
    return((uint8_t)(((uint32_t)((((SMARTIO_PRT_Type *)(base))->SYNC_CTL)) & 0xFF00UL) >> 8UL));
}
static inline cy_en_smartio_lutopc_t Cy_SmartIO_GetLutOpcode(SMARTIO_PRT_Type* base, cy_en_smartio_lutnum_t lutNum)
{
    return((cy_en_smartio_lutopc_t)((((uint32_t)((((SMARTIO_PRT_Type *)(base))->LUT_CTL[lutNum])) & 0x300UL) >> 8UL)));
}
static inline uint8_t Cy_SmartIO_GetLutMap(SMARTIO_PRT_Type* base, cy_en_smartio_lutnum_t lutNum)
{
   return((uint8_t)((((uint32_t)((((SMARTIO_PRT_Type *)(base))->LUT_CTL[lutNum])) & 0xFFUL) >> 0UL)));
}
static inline cy_en_smartio_dudata_t Cy_SmartIO_GetDuData(SMARTIO_PRT_Type* base, cy_en_smartio_datanum_t dataNum)
{
    return ((dataNum == CY_SMARTIO_DATA0) ?
                (cy_en_smartio_dudata_t)(((uint32_t)((((SMARTIO_PRT_Type *)(base))->DU_SEL)) & 0x3000000UL) >> 24UL) :
                (cy_en_smartio_dudata_t)(((uint32_t)((((SMARTIO_PRT_Type *)(base))->DU_SEL)) & 0x30000000UL) >> 28UL));
}
static inline cy_en_smartio_duopc_t Cy_SmartIO_GetDuOpc(SMARTIO_PRT_Type* base)
{
    return ((cy_en_smartio_duopc_t)(((uint32_t)((((SMARTIO_PRT_Type *)(base))->DU_CTL)) & 0xF00UL) >> 8UL));
}
static inline cy_en_smartio_dusize_t Cy_SmartIO_GetDuSize(SMARTIO_PRT_Type* base)
{
    return ((cy_en_smartio_dusize_t)(((uint32_t)((((SMARTIO_PRT_Type *)(base))->DU_CTL)) & 0x7UL) >> 0UL));
}
static inline uint8_t Cy_SmartIO_GetDataReg(SMARTIO_PRT_Type* base)
{
    return ((uint8_t)((((SMARTIO_PRT_Type *)(base))->DATA)));
}

typedef enum
{
    CY_TCPWM_INPUT_TR_START = 0x00U,
    CY_TCPWM_INPUT_TR_RELOAD_OR_INDEX = 0x01U,
    CY_TCPWM_INPUT_TR_STOP_OR_KILL = 0x02U,
    CY_TCPWM_INPUT_TR_COUNT = 0x03U,
    CY_TCPWM_INPUT_TR_INDEX_OR_SWAP = 0x04U,
    CY_TCPWM_INPUT_TR_CAPTURE0 = 0x04U,
    CY_TCPWM_INPUT_TR_CAPTURE1 = 0x05U
} cy_en_tcpwm_trigselect_t;
typedef enum
{
    CY_TCPWM_OUTPUT_TR_OVERFLOW = 0x00U,
    CY_TCPWM_OUTPUT_TR_UNDERFLOW = 0x01U,
    CY_TCPWM_OUTPUT_TR_TC_EVENT = 0x02U,
    CY_TCPWM_OUTPUT_TR_CC0_MATCH = 0x03U,
    CY_TCPWM_OUTPUT_TR_CC1_MATCH = 0x04U,
    CY_TCPWM_OUTPUT_TR_LINE_OUT = 0x05U,
    CY_TCPWM_OUTPUT_TR_DISABLED = 0x07U
} cy_en_tcpwm_output_trigselect_t;
typedef enum
{
    CY_TCPWM_SUCCESS = 0x00U,
    CY_TCPWM_BAD_PARAM = (((uint32_t)((uint32_t)((0x2DU) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x01U,
    CY_TCPWM_UNSUPPORTED_FEATURE = (((uint32_t)((uint32_t)((0x2DU) & (((1UL << ((14U))) - 1U))) << ((18U))))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x02U,
} cy_en_tcpwm_status_t;
static inline void Cy_TCPWM_Enable_Multiple(TCPWM_Type *base, uint32_t counters);
static inline void Cy_TCPWM_Disable_Multiple(TCPWM_Type *base, uint32_t counters);
static inline void Cy_TCPWM_TriggerStart(TCPWM_Type *base, uint32_t counters);
static inline void Cy_TCPWM_TriggerReloadOrIndex(TCPWM_Type *base, uint32_t counters);
static inline void Cy_TCPWM_TriggerStopOrKill(TCPWM_Type *base, uint32_t counters);
static inline void Cy_TCPWM_TriggerCaptureOrSwap(TCPWM_Type *base, uint32_t counters);
static inline void Cy_TCPWM_Enable_Single(TCPWM_Type *base, uint32_t cntNum);
static inline void Cy_TCPWM_Disable_Single(TCPWM_Type *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_GetInterruptStatus(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_ClearInterrupt(TCPWM_Type *base, uint32_t cntNum, uint32_t source);
static inline void Cy_TCPWM_SetInterrupt(TCPWM_Type *base, uint32_t cntNum, uint32_t source);
static inline void Cy_TCPWM_SetInterruptMask(TCPWM_Type *base, uint32_t cntNum, uint32_t mask);
static inline uint32_t Cy_TCPWM_GetInterruptMask(TCPWM_Type const *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_GetInterruptStatusMasked(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_TriggerStart_Single(TCPWM_Type *base, uint32_t cntNum);
static inline void Cy_TCPWM_TriggerReloadOrIndex_Single(TCPWM_Type *base, uint32_t cntNum);
static inline void Cy_TCPWM_TriggerStopOrKill_Single(TCPWM_Type *base, uint32_t cntNum);
static inline void Cy_TCPWM_TriggerCaptureOrSwap_Single(TCPWM_Type *base, uint32_t cntNum);
static inline void Cy_TCPWM_TriggerCapture0(TCPWM_Type *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_Block_GetCC0Val(TCPWM_Type const *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_Block_GetCC0BufVal(TCPWM_Type const *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_Block_GetCounter(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_Block_SetCounter(TCPWM_Type *base, uint32_t cntNum, uint32_t count);
static inline void Cy_TCPWM_Block_SetPeriod(TCPWM_Type *base, uint32_t cntNum, uint32_t period);
static inline uint32_t Cy_TCPWM_Block_GetPeriod(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_Block_SetCC0BufVal(TCPWM_Type *base, uint32_t cntNum, uint32_t compare1);
static inline void Cy_TCPWM_Block_SetCC0Val(TCPWM_Type *base, uint32_t cntNum, uint32_t compare0);
static inline void Cy_TCPWM_Block_EnableCompare0Swap(TCPWM_Type *base, uint32_t cntNum, _Bool enable);
static inline uint32_t Cy_TCPWM_Block_GetCC0Val(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t result;
        result = ((((TCPWM_V1_Type *)(base))->CNT[cntNum].CC));
    return result;
}
static inline uint32_t Cy_TCPWM_Block_GetCC0BufVal(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t result;
        result = ((((TCPWM_V1_Type *)(base))->CNT[cntNum].CC_BUFF));
    return result;
}
static inline uint32_t Cy_TCPWM_Block_GetCounter(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t result;
        result = (((TCPWM_V1_Type *)(base))->CNT[cntNum].COUNTER);
    return result;
}
static inline void Cy_TCPWM_Block_SetCounter(TCPWM_Type *base, uint32_t cntNum, uint32_t count)
{
        (((TCPWM_V1_Type *)(base))->CNT[cntNum].COUNTER) = count;
}
static inline void Cy_TCPWM_Block_SetPeriod(TCPWM_Type *base, uint32_t cntNum, uint32_t period)
{
        (((TCPWM_V1_Type *)(base))->CNT[cntNum].PERIOD) = period;
}
static inline uint32_t Cy_TCPWM_Block_GetPeriod(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t result;
        result = (((TCPWM_V1_Type *)(base))->CNT[cntNum].PERIOD);
    return result;
}
static inline void Cy_TCPWM_Block_SetCC0BufVal(TCPWM_Type *base, uint32_t cntNum, uint32_t compare1)
{
        (((TCPWM_V1_Type *)(base))->CNT[cntNum].CC_BUFF) = compare1;
}
static inline void Cy_TCPWM_Block_SetCC0Val(TCPWM_Type *base, uint32_t cntNum, uint32_t compare0)
{
        (((TCPWM_V1_Type *)(base))->CNT[cntNum].CC) = compare0;
}
static inline void Cy_TCPWM_Block_EnableCompare0Swap(TCPWM_Type *base, uint32_t cntNum, _Bool enable)
{
        if (enable)
        {
            (((TCPWM_V1_Type *)(base))->CNT[cntNum].CTRL) |= 0x1UL;
        }
        else
        {
            (((TCPWM_V1_Type *)(base))->CNT[cntNum].CTRL) &= ~0x1UL;
        }
}
static inline void Cy_TCPWM_Enable_Multiple(TCPWM_Type *base, uint32_t counters)
{
    (((TCPWM_V1_Type *)(base))->CTRL_SET) = counters;
}
static inline void Cy_TCPWM_Disable_Multiple(TCPWM_Type *base, uint32_t counters)
{
    (((TCPWM_V1_Type *)(base))->CTRL_CLR) = counters;
}
static inline void Cy_TCPWM_TriggerStart(TCPWM_Type *base, uint32_t counters)
{
    (((TCPWM_V1_Type *)(base))->CMD_START) = counters;
}
static inline void Cy_TCPWM_TriggerReloadOrIndex(TCPWM_Type *base, uint32_t counters)
{
    (((TCPWM_V1_Type *)(base))->CMD_RELOAD) = counters;
}
static inline void Cy_TCPWM_TriggerStopOrKill(TCPWM_Type *base, uint32_t counters)
{
    (((TCPWM_V1_Type *)(base))->CMD_STOP) = counters;
}
static inline void Cy_TCPWM_TriggerCaptureOrSwap(TCPWM_Type *base, uint32_t counters)
{
    (((TCPWM_V1_Type *)(base))->CMD_CAPTURE) = counters;
}
static inline void Cy_TCPWM_Enable_Single(TCPWM_Type *base, uint32_t cntNum)
{
    (((TCPWM_V1_Type *)(base))->CTRL_SET) = (1UL << cntNum);
}
static inline void Cy_TCPWM_Disable_Single(TCPWM_Type *base, uint32_t cntNum)
{
        (((TCPWM_V1_Type *)(base))->CTRL_CLR) = (1UL << cntNum);
}
static inline uint32_t Cy_TCPWM_GetInterruptStatus(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t result;
        result = (((TCPWM_V1_Type *)(base))->CNT[cntNum].INTR);
    return result;
}
static inline void Cy_TCPWM_ClearInterrupt(TCPWM_Type *base, uint32_t cntNum, uint32_t source)
{
        (((TCPWM_V1_Type *)(base))->CNT[cntNum].INTR) = source;
        (void)(((TCPWM_V1_Type *)(base))->CNT[cntNum].INTR);
}
static inline void Cy_TCPWM_SetInterrupt(TCPWM_Type *base, uint32_t cntNum, uint32_t source)
{
        (((TCPWM_V1_Type *)(base))->CNT[cntNum].INTR_SET) = source;
}
static inline void Cy_TCPWM_SetInterruptMask(TCPWM_Type *base, uint32_t cntNum, uint32_t mask)
{
        (((TCPWM_V1_Type *)(base))->CNT[cntNum].INTR_MASK) = mask;
}
static inline uint32_t Cy_TCPWM_GetInterruptMask(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t mask;
        mask = (((TCPWM_V1_Type *)(base))->CNT[cntNum].INTR_MASK);
    return mask;
}
static inline uint32_t Cy_TCPWM_GetInterruptStatusMasked(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t status;
        status = (((TCPWM_V1_Type *)(base))->CNT[cntNum].INTR_MASKED);
    return status;
}
static inline void Cy_TCPWM_TriggerStart_Single(TCPWM_Type *base, uint32_t cntNum)
{
        (((TCPWM_V1_Type *)(base))->CMD_START) = (1UL << cntNum);
}
static inline void Cy_TCPWM_TriggerReloadOrIndex_Single(TCPWM_Type *base, uint32_t cntNum)
{
        (((TCPWM_V1_Type *)(base))->CMD_RELOAD) = (1UL << cntNum);
}
static inline void Cy_TCPWM_TriggerStopOrKill_Single(TCPWM_Type *base, uint32_t cntNum)
{
        (((TCPWM_V1_Type *)(base))->CMD_STOP) = (1UL << cntNum);
}
static inline void Cy_TCPWM_TriggerCaptureOrSwap_Single(TCPWM_Type *base, uint32_t cntNum)
{
        (((TCPWM_V1_Type *)(base))->CMD_CAPTURE) = (1UL << cntNum);
}
static inline void Cy_TCPWM_TriggerCapture0(TCPWM_Type *base, uint32_t cntNum)
{
    Cy_TCPWM_TriggerCaptureOrSwap_Single(base, cntNum);
}
typedef struct cy_stc_tcpwm_counter_config
{
    uint32_t period;
    uint32_t clockPrescaler;
    uint32_t runMode;
    uint32_t countDirection;
    uint32_t compareOrCapture;
    uint32_t compare0;
    uint32_t compare1;
    _Bool enableCompareSwap;
    uint32_t interruptSources;
    uint32_t captureInputMode;
    uint32_t captureInput;
    uint32_t reloadInputMode;
    uint32_t reloadInput;
    uint32_t startInputMode;
    uint32_t startInput;
    uint32_t stopInputMode;
    uint32_t stopInput;
    uint32_t countInputMode;
    uint32_t countInput;
}cy_stc_tcpwm_counter_config_t;
cy_en_tcpwm_status_t Cy_TCPWM_Counter_Init(TCPWM_Type *base, uint32_t cntNum,
                                           cy_stc_tcpwm_counter_config_t const *config);
void Cy_TCPWM_Counter_DeInit(TCPWM_Type *base, uint32_t cntNum, cy_stc_tcpwm_counter_config_t const *config);
static inline void Cy_TCPWM_Counter_Enable(TCPWM_Type *base, uint32_t cntNum);
static inline void Cy_TCPWM_Counter_Disable(TCPWM_Type *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_Counter_GetStatus(TCPWM_Type const *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_Counter_GetCapture0Val(TCPWM_Type const *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_Counter_GetCapture0BufVal(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_Counter_SetCompare0Val(TCPWM_Type *base, uint32_t cntNum, uint32_t compare0);
static inline uint32_t Cy_TCPWM_Counter_GetCompare0Val(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_Counter_SetCompare0BufVal(TCPWM_Type *base, uint32_t cntNum, uint32_t compare1);
static inline uint32_t Cy_TCPWM_Counter_GetCompare0BufVal(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_Counter_EnableCompare0Swap(TCPWM_Type *base, uint32_t cntNum, _Bool enable);
static inline void Cy_TCPWM_Counter_SetCounter(TCPWM_Type *base, uint32_t cntNum, uint32_t count);
static inline uint32_t Cy_TCPWM_Counter_GetCounter(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_Counter_SetPeriod(TCPWM_Type *base, uint32_t cntNum, uint32_t period);
static inline uint32_t Cy_TCPWM_Counter_GetPeriod(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_Counter_Enable(TCPWM_Type *base, uint32_t cntNum)
{
    Cy_TCPWM_Enable_Single(base, cntNum);
}
static inline void Cy_TCPWM_Counter_Disable(TCPWM_Type *base, uint32_t cntNum)
{
    Cy_TCPWM_Disable_Single(base, cntNum);
}
static inline uint32_t Cy_TCPWM_Counter_GetStatus(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t status;
        status = (((TCPWM_V1_Type *)(base))->CNT[cntNum].STATUS);
        status &= ~(0x2UL);
        status |= ((~status & (0x1UL) & (status >> 31UL)) <<
               (0x1U));
    return(status);
}
static inline uint32_t Cy_TCPWM_Counter_GetCapture0Val(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCC0Val(base, cntNum);
}
static inline uint32_t Cy_TCPWM_Counter_GetCapture0BufVal(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCC0BufVal(base, cntNum);
}
static inline void Cy_TCPWM_Counter_SetCompare0Val(TCPWM_Type *base, uint32_t cntNum, uint32_t compare0)
{
    Cy_TCPWM_Block_SetCC0Val(base, cntNum, compare0);
}
static inline uint32_t Cy_TCPWM_Counter_GetCompare0Val(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCC0Val(base, cntNum);
}
static inline void Cy_TCPWM_Counter_SetCompare0BufVal(TCPWM_Type *base, uint32_t cntNum, uint32_t compare1)
{
    Cy_TCPWM_Block_SetCC0BufVal(base, cntNum, compare1);
}
static inline uint32_t Cy_TCPWM_Counter_GetCompare0BufVal(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCC0BufVal(base, cntNum);
}
static inline void Cy_TCPWM_Counter_EnableCompare0Swap(TCPWM_Type *base, uint32_t cntNum, _Bool enable)
{
    Cy_TCPWM_Block_EnableCompare0Swap(base, cntNum, enable);
}
static inline void Cy_TCPWM_Counter_SetCounter(TCPWM_Type *base, uint32_t cntNum, uint32_t count)
{
    Cy_TCPWM_Block_SetCounter(base, cntNum, count);
}
static inline uint32_t Cy_TCPWM_Counter_GetCounter(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCounter(base, cntNum);
}
static inline void Cy_TCPWM_Counter_SetPeriod(TCPWM_Type *base, uint32_t cntNum, uint32_t period)
{
    Cy_TCPWM_Block_SetPeriod(base, cntNum, period);
}
static inline uint32_t Cy_TCPWM_Counter_GetPeriod(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetPeriod(base, cntNum);
}
typedef struct cy_stc_tcpwm_pwm_config
{
    uint32_t pwmMode;
    uint32_t clockPrescaler;
    uint32_t pwmAlignment;
    uint32_t deadTimeClocks;
    uint32_t runMode;
    uint32_t period0;
    uint32_t period1;
    _Bool enablePeriodSwap;
    uint32_t compare0;
    uint32_t compare1;
    _Bool enableCompareSwap;
    uint32_t interruptSources;
    uint32_t invertPWMOut;
    uint32_t invertPWMOutN;
    uint32_t killMode;
    uint32_t swapInputMode;
    uint32_t swapInput;
    uint32_t reloadInputMode;
    uint32_t reloadInput;
    uint32_t startInputMode;
    uint32_t startInput;
    uint32_t killInputMode;
    uint32_t killInput;
    uint32_t countInputMode;
    uint32_t countInput;
    _Bool swapOverflowUnderflow;
}cy_stc_tcpwm_pwm_config_t;
cy_en_tcpwm_status_t Cy_TCPWM_PWM_Init(TCPWM_Type *base, uint32_t cntNum, cy_stc_tcpwm_pwm_config_t const *config);
void Cy_TCPWM_PWM_DeInit(TCPWM_Type *base, uint32_t cntNum, cy_stc_tcpwm_pwm_config_t const *config);
static inline void Cy_TCPWM_PWM_Enable(TCPWM_Type *base, uint32_t cntNum);
static inline void Cy_TCPWM_PWM_Disable(TCPWM_Type *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_PWM_GetStatus(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_PWM_SetCompare0Val(TCPWM_Type *base, uint32_t cntNum, uint32_t compare0);
static inline uint32_t Cy_TCPWM_PWM_GetCompare0Val(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_PWM_SetCompare0BufVal(TCPWM_Type *base, uint32_t cntNum, uint32_t compareBuf0);
static inline uint32_t Cy_TCPWM_PWM_GetCompare0BufVal(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_PWM_EnableCompare0Swap(TCPWM_Type *base, uint32_t cntNum, _Bool enable);
static inline void Cy_TCPWM_PWM_SetCounter(TCPWM_Type *base, uint32_t cntNum, uint32_t count);
static inline uint32_t Cy_TCPWM_PWM_GetCounter(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_PWM_SetPeriod0(TCPWM_Type *base, uint32_t cntNum, uint32_t period0);
static inline uint32_t Cy_TCPWM_PWM_GetPeriod0(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_PWM_SetPeriod1(TCPWM_Type *base, uint32_t cntNum, uint32_t period1);
static inline uint32_t Cy_TCPWM_PWM_GetPeriod1(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_PWM_EnablePeriodSwap(TCPWM_Type *base, uint32_t cntNum, _Bool enable);
static inline void Cy_TCPWM_PWM_PWMDeadTime (TCPWM_Type const *base, uint32_t cntNum, uint32_t deadTime);
static inline void Cy_TCPWM_PWM_Enable(TCPWM_Type *base, uint32_t cntNum)
{
    Cy_TCPWM_Enable_Single(base, cntNum);
}
static inline void Cy_TCPWM_PWM_Disable(TCPWM_Type *base, uint32_t cntNum)
{
    Cy_TCPWM_Disable_Single(base, cntNum);
}
static inline uint32_t Cy_TCPWM_PWM_GetStatus(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t status;
        status = (((TCPWM_V1_Type *)(base))->CNT[cntNum].STATUS);
        status &= ~(0x2UL);
        status |= ((~status & (0x1UL) & (status >> 31UL)) <<
                   (0x1U));
    return(status);
}
static inline void Cy_TCPWM_PWM_SetCompare0Val(TCPWM_Type *base, uint32_t cntNum, uint32_t compare0)
{
    Cy_TCPWM_Block_SetCC0Val(base, cntNum, compare0);
}
static inline uint32_t Cy_TCPWM_PWM_GetCompare0Val(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCC0Val(base, cntNum);
}
static inline void Cy_TCPWM_PWM_SetCompare0BufVal(TCPWM_Type *base, uint32_t cntNum, uint32_t compareBuf0)
{
    Cy_TCPWM_Block_SetCC0BufVal(base, cntNum, compareBuf0);
}
static inline uint32_t Cy_TCPWM_PWM_GetCompare0BufVal(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCC0BufVal(base, cntNum);
}
static inline void Cy_TCPWM_PWM_EnableCompare0Swap(TCPWM_Type *base, uint32_t cntNum, _Bool enable)
{
     Cy_TCPWM_Block_EnableCompare0Swap(base, cntNum, enable);
}
static inline void Cy_TCPWM_PWM_SetCounter(TCPWM_Type *base, uint32_t cntNum, uint32_t count)
{
    Cy_TCPWM_Block_SetCounter(base, cntNum, count);
}
static inline uint32_t Cy_TCPWM_PWM_GetCounter(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCounter(base, cntNum);
}
static inline void Cy_TCPWM_PWM_SetPeriod0(TCPWM_Type *base, uint32_t cntNum, uint32_t period0)
{
    Cy_TCPWM_Block_SetPeriod(base, cntNum, period0);
}
static inline uint32_t Cy_TCPWM_PWM_GetPeriod0(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetPeriod(base, cntNum);
}
static inline void Cy_TCPWM_PWM_SetPeriod1(TCPWM_Type *base, uint32_t cntNum, uint32_t period1)
{
        (((TCPWM_V1_Type *)(base))->CNT[cntNum].PERIOD_BUFF) = period1;
}
static inline uint32_t Cy_TCPWM_PWM_GetPeriod1(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t result;
        result = (((TCPWM_V1_Type *)(base))->CNT[cntNum].PERIOD_BUFF);
    return result;
}
static inline void Cy_TCPWM_PWM_EnablePeriodSwap(TCPWM_Type *base, uint32_t cntNum, _Bool enable)
{
        if (enable)
        {
            (((TCPWM_V1_Type *)(base))->CNT[cntNum].CTRL) |= 0x2UL;
        }
        else
        {
            (((TCPWM_V1_Type *)(base))->CNT[cntNum].CTRL) &= ~0x2UL;
        }
}
static inline void Cy_TCPWM_PWM_PWMDeadTime (TCPWM_Type const *base, uint32_t cntNum, uint32_t deadTime)
{
    uint32_t result;
        result = (((TCPWM_V1_Type *)(base))->CNT[cntNum].CTRL);
        result &= ~(0xFF00UL);
        (((TCPWM_V1_Type *)(base))->CNT[cntNum].CTRL) = result | (((uint32_t)(deadTime) << 8UL) & 0xFF00UL);
}
typedef struct cy_stc_tcpwm_quaddec_config
{
    uint32_t resolution;
    uint32_t interruptSources;
    uint32_t indexInputMode;
    uint32_t indexInput;
    uint32_t stopInputMode;
    uint32_t stopInput;
    uint32_t phiAInput;
    uint32_t phiBInput;
}cy_stc_tcpwm_quaddec_config_t;
cy_en_tcpwm_status_t Cy_TCPWM_QuadDec_Init(TCPWM_Type *base, uint32_t cntNum,
                                           cy_stc_tcpwm_quaddec_config_t const *config);
void Cy_TCPWM_QuadDec_DeInit(TCPWM_Type *base, uint32_t cntNum, cy_stc_tcpwm_quaddec_config_t const *config);
static inline void Cy_TCPWM_QuadDec_Enable(TCPWM_Type *base, uint32_t cntNum);
static inline void Cy_TCPWM_QuadDec_Disable(TCPWM_Type *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_QuadDec_GetStatus(TCPWM_Type const *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_QuadDec_GetCapture0Val(TCPWM_Type const *base, uint32_t cntNum);
static inline uint32_t Cy_TCPWM_QuadDec_GetCapture0BufVal(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_QuadDec_SetCompare0Val(TCPWM_Type *base, uint32_t cntNum, uint32_t compare0);
static inline uint32_t Cy_TCPWM_QuadDec_GetCompare0Val(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_QuadDec_SetCompare0BufVal(TCPWM_Type *base, uint32_t cntNum, uint32_t compareBuf0);
static inline uint32_t Cy_TCPWM_QuadDec_GetCompare0BufVal(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_QuadDec_EnableCompare0Swap(TCPWM_Type *base, uint32_t cntNum, _Bool enable);
static inline void Cy_TCPWM_QuadDec_SetCounter(TCPWM_Type *base, uint32_t cntNum, uint32_t count);
static inline uint32_t Cy_TCPWM_QuadDec_GetCounter(TCPWM_Type const *base, uint32_t cntNum);
static inline void Cy_TCPWM_QuadDec_Enable(TCPWM_Type *base, uint32_t cntNum)
{
    Cy_TCPWM_Enable_Single(base, cntNum);
}
static inline void Cy_TCPWM_QuadDec_Disable(TCPWM_Type *base, uint32_t cntNum)
{
    Cy_TCPWM_Disable_Single(base, cntNum);
}
static inline uint32_t Cy_TCPWM_QuadDec_GetStatus(TCPWM_Type const *base, uint32_t cntNum)
{
    uint32_t status;
        status = (((TCPWM_V1_Type *)(base))->CNT[cntNum].STATUS);
        status &= ~(0x2UL);
        status |= ((~status & (0x1UL) & (status >> 31UL)) <<
                   (0x1U));
    return(status);
}
static inline uint32_t Cy_TCPWM_QuadDec_GetCapture0Val(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCC0Val(base, cntNum);
}
static inline uint32_t Cy_TCPWM_QuadDec_GetCapture0BufVal(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCC0BufVal(base, cntNum);
}
static inline void Cy_TCPWM_QuadDec_SetCompare0Val(TCPWM_Type *base, uint32_t cntNum, uint32_t compare0)
{
    Cy_TCPWM_Block_SetCC0Val(base, cntNum, compare0);
}
static inline uint32_t Cy_TCPWM_QuadDec_GetCompare0Val(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCC0Val(base, cntNum);
}
static inline void Cy_TCPWM_QuadDec_SetCompare0BufVal(TCPWM_Type *base, uint32_t cntNum, uint32_t compareBuf0)
{
    Cy_TCPWM_Block_SetCC0BufVal(base, cntNum, compareBuf0);
}
static inline uint32_t Cy_TCPWM_QuadDec_GetCompare0BufVal(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCC0BufVal(base, cntNum);
}
static inline void Cy_TCPWM_QuadDec_EnableCompare0Swap(TCPWM_Type *base, uint32_t cntNum, _Bool enable)
{
    Cy_TCPWM_Block_EnableCompare0Swap(base, cntNum, enable);
}
static inline void Cy_TCPWM_QuadDec_SetCounter(TCPWM_Type *base, uint32_t cntNum, uint32_t count)
{
    Cy_TCPWM_Block_SetCounter(base, cntNum, count);
}
static inline uint32_t Cy_TCPWM_QuadDec_GetCounter(TCPWM_Type const *base, uint32_t cntNum)
{
    return Cy_TCPWM_Block_GetCounter(base, cntNum);
}
typedef struct cy_stc_tcpwm_shiftreg_config cy_stc_tcpwm_shiftreg_config_t;
cy_en_tcpwm_status_t Cy_TCPWM_ShiftReg_Init(TCPWM_Type const *base, uint32_t cntNum, cy_stc_tcpwm_shiftreg_config_t const *config);
void Cy_TCPWM_ShiftReg_DeInit(TCPWM_Type const *base, uint32_t cntNum, cy_stc_tcpwm_shiftreg_config_t const *config);

typedef enum
{
    CY_TRIGMUX_SUCCESS = 0x0UL,
    CY_TRIGMUX_BAD_PARAM = ((uint32_t)((uint32_t)((0x33UL) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x1UL,
    CY_TRIGMUX_INVALID_STATE = ((uint32_t)((uint32_t)((0x33UL) & (((1UL << ((14U))) - 1U))) << ((18U)))) | ((uint32_t)CY_RSLT_TYPE_ERROR << ((16U))) | 0x2UL
} cy_en_trigmux_status_t;
cy_en_trigmux_status_t Cy_TrigMux_Connect(uint32_t inTrig, uint32_t outTrig, _Bool invert, en_trig_type_t trigType);
static inline cy_en_trigmux_status_t Cy_TrigMux_SwTrigger(uint32_t trigLine, uint32_t cycles);
cy_en_trigmux_status_t Cy_TrigMux_Select(uint32_t outTrig, _Bool invert, en_trig_type_t trigType);
cy_en_trigmux_status_t Cy_TrigMux_Deselect(uint32_t outTrig);
cy_en_trigmux_status_t Cy_TrigMux_SetDebugFreeze(uint32_t outTrig, _Bool enable);
static inline cy_en_trigmux_status_t Cy_TrigMux_SwTrigger(uint32_t trigLine, uint32_t cycles)
{
    cy_en_trigmux_status_t retVal = CY_TRIGMUX_INVALID_STATE;
    do { if(!((0U == ((trigLine) & (uint32_t)~(0x40000000UL | ((uint32_t)cy_device->periTrCmdGrSelMsk) | ((uint32_t)((uint32_t)cy_device->periTrGrSize / sizeof(uint32_t)) - 1UL)))))) { CY_HALT(); } } while (0);
    do { if(!(((((uint32_t)(0x20U > cy_device->periVersion)) && ((255UL) >= (cycles))) || (((0UL) == (cycles)) || ((2UL) == (cycles)) || ((255UL) == (cycles)))))) { CY_HALT(); } } while (0);
    if ((0UL) != cycles)
    {
        if (0x80000000UL != ((*(volatile uint32_t*)((uint32_t)cy_device->periBase + (uint32_t)cy_device->periTrCmdOffset)) & 0x80000000UL))
        {
            uint32_t trCmd = (trigLine & (0xFFUL |
                                          0x40000000UL |
                                       ((uint32_t)cy_device->periTrCmdGrSelMsk))) |
                                          0x80000000UL;
            retVal = CY_TRIGMUX_SUCCESS;
            if (((uint32_t)(0x20U > cy_device->periVersion)) != 0U)
            {
                (*(volatile uint32_t*)((uint32_t)cy_device->periBase + (uint32_t)cy_device->periTrCmdOffset)) = trCmd | (((uint32_t)(cycles) << 16UL) & 0xFF0000UL);
            }
            else if ((2UL) == cycles)
            {
                (*(volatile uint32_t*)((uint32_t)cy_device->periBase + (uint32_t)cy_device->periTrCmdOffset)) = trCmd | 0x20000000UL;
            }
            else if ((255UL) == cycles)
            {
                (*(volatile uint32_t*)((uint32_t)cy_device->periBase + (uint32_t)cy_device->periTrCmdOffset)) = trCmd;
            }
            else
            {
                retVal = CY_TRIGMUX_BAD_PARAM;
            }
        }
    }
    else
    {
        if (0x80000000UL == ((*(volatile uint32_t*)((uint32_t)cy_device->periBase + (uint32_t)cy_device->periTrCmdOffset)) & 0x80000000UL))
        {
            (*(volatile uint32_t*)((uint32_t)cy_device->periBase + (uint32_t)cy_device->periTrCmdOffset)) = 0UL;
            retVal = CY_TRIGMUX_SUCCESS;
        }
    }
    return retVal;
}

void Cy_WDT_Init(void);
void Cy_WDT_Lock(void);
void Cy_WDT_Unlock(void);
_Bool Cy_WDT_Locked(void);
void Cy_WDT_ClearInterrupt(void);
void Cy_WDT_ClearWatchdog(void);
static inline void Cy_WDT_Enable(void);
static inline void Cy_WDT_Disable(void);
static inline _Bool Cy_WDT_IsEnabled(void);
static inline uint32_t Cy_WDT_GetCount(void);
static inline void Cy_WDT_ResetCounter(void);
static inline void Cy_WDT_MaskInterrupt(void);
static inline void Cy_WDT_UnmaskInterrupt(void);
void Cy_WDT_SetMatch(uint32_t match);
void Cy_WDT_SetIgnoreBits(uint32_t bitsNum);
static inline uint32_t Cy_WDT_GetMatch(void);
static inline uint32_t Cy_WDT_GetIgnoreBits(void);
static inline void Cy_WDT_Enable(void)
{
    (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->WDT_CTL) |= (((uint32_t)(1U) << 0UL) & 0x1UL);
    Cy_WDT_ClearInterrupt();
}
static inline void Cy_WDT_Disable(void)
{
    (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->WDT_CTL) &= ((uint32_t) ~((((uint32_t)(1U) << 0UL) & 0x1UL)));
}
static inline _Bool Cy_WDT_IsEnabled(void)
{
    return ((((((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->WDT_CTL)) & (0x1UL)) != 0UL);
}
static inline uint32_t Cy_WDT_GetMatch(void)
{
    return ((uint32_t) (((uint32_t)((((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->WDT_MATCH)) & 0xFFFFUL) >> 0UL));
}
static inline uint32_t Cy_WDT_GetIgnoreBits(void)
{
    return((uint32_t) (((uint32_t)((((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->WDT_MATCH)) & 0xF0000UL) >> 16UL));
}
static inline uint32_t Cy_WDT_GetCount(void)
{
    return ((uint32_t) (((uint32_t)((((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->WDT_CNT)) & 0xFFFFUL) >> 0UL));
}
static inline void Cy_WDT_ResetCounter(void)
{
    (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->WDT_CNT) = 0x0U;
}
static inline void Cy_WDT_MaskInterrupt(void)
{
        (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR_MASK) &= (uint32_t)(~ (((uint32_t)(1U) << 0UL) & 0x1UL));
}
static inline void Cy_WDT_UnmaskInterrupt(void)
{
        (((SRSS_V1_Type *) ((SRSS_Type*) 0x40260000UL))->SRSS_INTR_MASK) |= (((uint32_t)(1U) << 0UL) & 0x1UL);
}

enum cyhal_rslt_module_chip
{
    CYHAL_RSLT_MODULE_ADC = (0x01),
    CYHAL_RSLT_MODULE_CLOCK = (0x02),
    CYHAL_RSLT_MODULE_COMP = (0x03),
    CYHAL_RSLT_MODULE_CRC = (0x04),
    CYHAL_RSLT_MODULE_DAC = (0x05),
    CYHAL_RSLT_MODULE_DMA = (0x06),
    CYHAL_RSLT_MODULE_EZI2C = (0x07),
    CYHAL_RSLT_MODULE_GPIO = (0x08),
    CYHAL_RSLT_MODULE_I2C = (0x09),
    CYHAL_RSLT_MODULE_I2S = (0x0A),
    CYHAL_RSLT_MODULE_IPC = (0x0B),
    CYHAL_RSLT_MODULE_INTERCONNECT = (0x0C),
    CYHAL_RSLT_MODULE_HWMGR = (0x0D),
    CYHAL_RSLT_MODULE_KEYSCAN = (0x0E),
    CYHAL_RSLT_MODULE_LPTIMER = (0x0F),
    CYHAL_RSLT_MODULE_NVM = (0x10),
    CYHAL_RSLT_MODULE_OPAMP = (0x11),
    CYHAL_RSLT_MODULE_PDMPCM = (0x12),
    CYHAL_RSLT_MODULE_PWM = (0x13),
    CYHAL_RSLT_MODULE_QSPI = (0x14),
    CYHAL_RSLT_MODULE_QUADDEC = (0x15),
    CYHAL_RSLT_MODULE_RTC = (0x16),
    CYHAL_RSLT_MODULE_SDHC = (0x17),
    CYHAL_RSLT_MODULE_SDIO = (0x18),
    CYHAL_RSLT_MODULE_SPI = (0x19),
    CYHAL_RSLT_MODULE_SYSPM = (0x1A),
    CYHAL_RSLT_MODULE_SYSTEM = (0x1B),
    CYHAL_RSLT_MODULE_TDM = (0x1C),
    CYHAL_RSLT_MODULE_TIMER = (0x1D),
    CYHAL_RSLT_MODULE_TRNG = (0x1E),
    CYHAL_RSLT_MODULE_UART = (0x1F),
    CYHAL_RSLT_MODULE_USB = (0x20),
    CYHAL_RSLT_MODULE_WDT = (0x21),
    CYHAL_RSLT_MODULE_IMPL_TCPWM = (0x22),
    CYHAL_RSLT_MODULE_IMPL_SCB = (0x23),
    CYHAL_RSLT_MODULE_T2TIMER = (0x24),
};
typedef enum {
    CYHAL_ASYNC_DMA,
    CYHAL_ASYNC_SW,
} cyhal_async_mode_t;
typedef enum
{
    CYHAL_EDGE_TYPE_RISING_EDGE,
    CYHAL_EDGE_TYPE_FALLING_EDGE,
    CYHAL_EDGE_TYPE_BOTH_EDGES,
    CYHAL_EDGE_TYPE_LEVEL,
} cyhal_edge_type_t;
typedef enum
{
    CYHAL_POWER_LEVEL_OFF,
    CYHAL_POWER_LEVEL_LOW,
    CYHAL_POWER_LEVEL_MEDIUM,
    CYHAL_POWER_LEVEL_HIGH,
    CYHAL_POWER_LEVEL_DEFAULT
} cyhal_power_level_t;
typedef enum
{
    CYHAL_SIGNAL_TYPE_LEVEL = 0,
    CYHAL_SIGNAL_TYPE_EDGE = 1,
} cyhal_signal_type_t;
typedef enum
{
    CYHAL_SYSPM_CB_CPU_SLEEP = 0x01U,
    CYHAL_SYSPM_CB_CPU_DEEPSLEEP = 0x02U,
    CYHAL_SYSPM_CB_CPU_DEEPSLEEP_RAM = 0x04U,
    CYHAL_SYSPM_CB_SYSTEM_HIBERNATE = 0x08U,
    CYHAL_SYSPM_CB_SYSTEM_NORMAL = 0x10U,
    CYHAL_SYSPM_CB_SYSTEM_LOW = 0x20U,
} cyhal_syspm_callback_state_t;
typedef enum
{
    CYHAL_SYSPM_CHECK_READY = 0x01U,
    CYHAL_SYSPM_CHECK_FAIL = 0x02U,
    CYHAL_SYSPM_BEFORE_TRANSITION = 0x04U,
    CYHAL_SYSPM_AFTER_TRANSITION = 0x08U,
    CYHAL_SYSPM_AFTER_DS_WFI_TRANSITION = 0x10U,
} cyhal_syspm_callback_mode_t;
typedef _Bool (*cyhal_syspm_callback_t)(cyhal_syspm_callback_state_t state, cyhal_syspm_callback_mode_t mode, void* callback_arg);
typedef struct cyhal_syspm_callback_data
{
    cyhal_syspm_callback_t callback;
    cyhal_syspm_callback_state_t states;
    cyhal_syspm_callback_mode_t ignore_modes;
    void *args;
    struct cyhal_syspm_callback_data *next;
} cyhal_syspm_callback_data_t;
typedef enum
{
    CYHAL_TOLERANCE_HZ,
    CYHAL_TOLERANCE_PPM,
    CYHAL_TOLERANCE_PERCENT,
} cyhal_clock_tolerance_unit_t;
typedef struct
{
    cyhal_clock_tolerance_unit_t type;
    uint32_t value;
} cyhal_clock_tolerance_t;

typedef enum
{
    CYHAL_RSC_ADC,
    CYHAL_RSC_ADCMIC,
    CYHAL_RSC_BLESS,
    CYHAL_RSC_CAN,
    CYHAL_RSC_CLKPATH,
    CYHAL_RSC_CLOCK,
    CYHAL_RSC_CRYPTO,
    CYHAL_RSC_DAC,
    CYHAL_RSC_DMA,
    CYHAL_RSC_DW,
    CYHAL_RSC_ETH,
    CYHAL_RSC_GPIO,
    CYHAL_RSC_I2S,
    CYHAL_RSC_I3C,
    CYHAL_RSC_KEYSCAN,
    CYHAL_RSC_LCD,
    CYHAL_RSC_LIN,
    CYHAL_RSC_LPCOMP,
    CYHAL_RSC_LPTIMER,
    CYHAL_RSC_OPAMP,
    CYHAL_RSC_PDM,
    CYHAL_RSC_SMIF,
    CYHAL_RSC_RTC,
    CYHAL_RSC_SCB,
    CYHAL_RSC_SDHC,
    CYHAL_RSC_SDIODEV,
    CYHAL_RSC_TCPWM,
    CYHAL_RSC_TDM,
    CYHAL_RSC_UDB,
    CYHAL_RSC_USB,
    CYHAL_RSC_INVALID,
} cyhal_resource_t;
typedef enum
{
    CYHAL_CLOCK_BLOCK_PERIPHERAL_8BIT = CY_SYSCLK_DIV_8_BIT,
    CYHAL_CLOCK_BLOCK_PERIPHERAL_16BIT = CY_SYSCLK_DIV_16_BIT,
    CYHAL_CLOCK_BLOCK_PERIPHERAL_16_5BIT = CY_SYSCLK_DIV_16_5_BIT,
    CYHAL_CLOCK_BLOCK_PERIPHERAL_24_5BIT = CY_SYSCLK_DIV_24_5_BIT,
    CYHAL_CLOCK_BLOCK_IMO,
    CYHAL_CLOCK_BLOCK_ECO,
    CYHAL_CLOCK_BLOCK_EXT,
    CYHAL_CLOCK_BLOCK_ALTHF,
    CYHAL_CLOCK_BLOCK_ALTLF,
    CYHAL_CLOCK_BLOCK_ILO,
    CYHAL_CLOCK_BLOCK_PILO,
    CYHAL_CLOCK_BLOCK_WCO,
    CYHAL_CLOCK_BLOCK_MFO,
    CYHAL_CLOCK_BLOCK_PATHMUX,
    CYHAL_CLOCK_BLOCK_FLL,
    CYHAL_CLOCK_BLOCK_PLL,
    CYHAL_CLOCK_BLOCK_LF,
    CYHAL_CLOCK_BLOCK_MF,
    CYHAL_CLOCK_BLOCK_HF,
    CYHAL_CLOCK_BLOCK_PUMP,
    CYHAL_CLOCK_BLOCK_BAK,
    CYHAL_CLOCK_BLOCK_TIMER,
    CYHAL_CLOCK_BLOCK_ALT_SYS_TICK,
    CYHAL_CLOCK_BLOCK_FAST,
    CYHAL_CLOCK_BLOCK_PERI,
    CYHAL_CLOCK_BLOCK_SLOW,
} cyhal_clock_block_t;
typedef struct
{
    cyhal_clock_block_t block;
    uint8_t channel;
    _Bool reserved;
    const void* funcs;
} cyhal_clock_t;
typedef struct
{
    cyhal_resource_t type;
    uint8_t block_num;
    uint8_t channel_num;
} cyhal_resource_inst_t;

typedef enum {
    CYHAL_PORT_0 = 0x00,
    CYHAL_PORT_1 = 0x01,
    CYHAL_PORT_2 = 0x02,
    CYHAL_PORT_3 = 0x03,
    CYHAL_PORT_4 = 0x04,
    CYHAL_PORT_5 = 0x05,
    CYHAL_PORT_6 = 0x06,
    CYHAL_PORT_7 = 0x07,
    CYHAL_PORT_8 = 0x08,
    CYHAL_PORT_9 = 0x09,
    CYHAL_PORT_10 = 0x0A,
    CYHAL_PORT_11 = 0x0B,
    CYHAL_PORT_12 = 0x0C,
    CYHAL_PORT_13 = 0x0D,
    CYHAL_PORT_14 = 0x0E,
    CYHAL_PORT_15 = 0x0F,
    CYHAL_PORT_16 = 0x10,
    CYHAL_PORT_17 = 0x11,
    CYHAL_PORT_18 = 0x12,
    CYHAL_PORT_19 = 0x13,
    CYHAL_PORT_20 = 0x14,
    CYHAL_PORT_21 = 0x15,
    CYHAL_PORT_22 = 0x16,
    CYHAL_PORT_23 = 0x17,
    CYHAL_PORT_24 = 0x18,
    CYHAL_PORT_25 = 0x19,
    CYHAL_PORT_26 = 0x1A,
    CYHAL_PORT_27 = 0x1B,
    CYHAL_PORT_28 = 0x1C,
    CYHAL_PORT_29 = 0x1D,
    CYHAL_PORT_30 = 0x1E,
    CYHAL_PORT_31 = 0x1F,
    CYHAL_PORT_32 = 0x20,
    CYHAL_PORT_33 = 0x21,
    CYHAL_PORT_34 = 0x22,
} cyhal_port_t;
typedef uint16_t cyhal_gpio_mapping_cfg_t;
typedef enum {
    NC = 0xFF,
    P0_0 = ((((uint8_t)(CYHAL_PORT_0)) << 3U) + ((uint8_t)(0))),
    P0_1 = ((((uint8_t)(CYHAL_PORT_0)) << 3U) + ((uint8_t)(1))),
    P0_2 = ((((uint8_t)(CYHAL_PORT_0)) << 3U) + ((uint8_t)(2))),
    P0_3 = ((((uint8_t)(CYHAL_PORT_0)) << 3U) + ((uint8_t)(3))),
    P0_4 = ((((uint8_t)(CYHAL_PORT_0)) << 3U) + ((uint8_t)(4))),
    P0_5 = ((((uint8_t)(CYHAL_PORT_0)) << 3U) + ((uint8_t)(5))),
    P1_0 = ((((uint8_t)(CYHAL_PORT_1)) << 3U) + ((uint8_t)(0))),
    P1_1 = ((((uint8_t)(CYHAL_PORT_1)) << 3U) + ((uint8_t)(1))),
    P1_2 = ((((uint8_t)(CYHAL_PORT_1)) << 3U) + ((uint8_t)(2))),
    P1_3 = ((((uint8_t)(CYHAL_PORT_1)) << 3U) + ((uint8_t)(3))),
    P1_4 = ((((uint8_t)(CYHAL_PORT_1)) << 3U) + ((uint8_t)(4))),
    P1_5 = ((((uint8_t)(CYHAL_PORT_1)) << 3U) + ((uint8_t)(5))),
    P5_0 = ((((uint8_t)(CYHAL_PORT_5)) << 3U) + ((uint8_t)(0))),
    P5_1 = ((((uint8_t)(CYHAL_PORT_5)) << 3U) + ((uint8_t)(1))),
    P5_2 = ((((uint8_t)(CYHAL_PORT_5)) << 3U) + ((uint8_t)(2))),
    P5_3 = ((((uint8_t)(CYHAL_PORT_5)) << 3U) + ((uint8_t)(3))),
    P5_4 = ((((uint8_t)(CYHAL_PORT_5)) << 3U) + ((uint8_t)(4))),
    P5_5 = ((((uint8_t)(CYHAL_PORT_5)) << 3U) + ((uint8_t)(5))),
    P5_6 = ((((uint8_t)(CYHAL_PORT_5)) << 3U) + ((uint8_t)(6))),
    P6_0 = ((((uint8_t)(CYHAL_PORT_6)) << 3U) + ((uint8_t)(0))),
    P6_1 = ((((uint8_t)(CYHAL_PORT_6)) << 3U) + ((uint8_t)(1))),
    P6_2 = ((((uint8_t)(CYHAL_PORT_6)) << 3U) + ((uint8_t)(2))),
    P6_3 = ((((uint8_t)(CYHAL_PORT_6)) << 3U) + ((uint8_t)(3))),
    P6_4 = ((((uint8_t)(CYHAL_PORT_6)) << 3U) + ((uint8_t)(4))),
    P6_5 = ((((uint8_t)(CYHAL_PORT_6)) << 3U) + ((uint8_t)(5))),
    P6_6 = ((((uint8_t)(CYHAL_PORT_6)) << 3U) + ((uint8_t)(6))),
    P6_7 = ((((uint8_t)(CYHAL_PORT_6)) << 3U) + ((uint8_t)(7))),
    P7_0 = ((((uint8_t)(CYHAL_PORT_7)) << 3U) + ((uint8_t)(0))),
    P7_1 = ((((uint8_t)(CYHAL_PORT_7)) << 3U) + ((uint8_t)(1))),
    P7_2 = ((((uint8_t)(CYHAL_PORT_7)) << 3U) + ((uint8_t)(2))),
    P7_3 = ((((uint8_t)(CYHAL_PORT_7)) << 3U) + ((uint8_t)(3))),
    P7_4 = ((((uint8_t)(CYHAL_PORT_7)) << 3U) + ((uint8_t)(4))),
    P7_5 = ((((uint8_t)(CYHAL_PORT_7)) << 3U) + ((uint8_t)(5))),
    P7_6 = ((((uint8_t)(CYHAL_PORT_7)) << 3U) + ((uint8_t)(6))),
    P7_7 = ((((uint8_t)(CYHAL_PORT_7)) << 3U) + ((uint8_t)(7))),
    P8_0 = ((((uint8_t)(CYHAL_PORT_8)) << 3U) + ((uint8_t)(0))),
    P8_1 = ((((uint8_t)(CYHAL_PORT_8)) << 3U) + ((uint8_t)(1))),
    P8_2 = ((((uint8_t)(CYHAL_PORT_8)) << 3U) + ((uint8_t)(2))),
    P8_3 = ((((uint8_t)(CYHAL_PORT_8)) << 3U) + ((uint8_t)(3))),
    P8_4 = ((((uint8_t)(CYHAL_PORT_8)) << 3U) + ((uint8_t)(4))),
    P8_5 = ((((uint8_t)(CYHAL_PORT_8)) << 3U) + ((uint8_t)(5))),
    P8_6 = ((((uint8_t)(CYHAL_PORT_8)) << 3U) + ((uint8_t)(6))),
    P8_7 = ((((uint8_t)(CYHAL_PORT_8)) << 3U) + ((uint8_t)(7))),
    P9_0 = ((((uint8_t)(CYHAL_PORT_9)) << 3U) + ((uint8_t)(0))),
    P9_1 = ((((uint8_t)(CYHAL_PORT_9)) << 3U) + ((uint8_t)(1))),
    P9_2 = ((((uint8_t)(CYHAL_PORT_9)) << 3U) + ((uint8_t)(2))),
    P9_3 = ((((uint8_t)(CYHAL_PORT_9)) << 3U) + ((uint8_t)(3))),
    P9_4 = ((((uint8_t)(CYHAL_PORT_9)) << 3U) + ((uint8_t)(4))),
    P9_5 = ((((uint8_t)(CYHAL_PORT_9)) << 3U) + ((uint8_t)(5))),
    P9_6 = ((((uint8_t)(CYHAL_PORT_9)) << 3U) + ((uint8_t)(6))),
    P9_7 = ((((uint8_t)(CYHAL_PORT_9)) << 3U) + ((uint8_t)(7))),
    P10_0 = ((((uint8_t)(CYHAL_PORT_10)) << 3U) + ((uint8_t)(0))),
    P10_1 = ((((uint8_t)(CYHAL_PORT_10)) << 3U) + ((uint8_t)(1))),
    P10_2 = ((((uint8_t)(CYHAL_PORT_10)) << 3U) + ((uint8_t)(2))),
    P10_3 = ((((uint8_t)(CYHAL_PORT_10)) << 3U) + ((uint8_t)(3))),
    P10_4 = ((((uint8_t)(CYHAL_PORT_10)) << 3U) + ((uint8_t)(4))),
    P10_5 = ((((uint8_t)(CYHAL_PORT_10)) << 3U) + ((uint8_t)(5))),
    P10_6 = ((((uint8_t)(CYHAL_PORT_10)) << 3U) + ((uint8_t)(6))),
    P11_0 = ((((uint8_t)(CYHAL_PORT_11)) << 3U) + ((uint8_t)(0))),
    P11_1 = ((((uint8_t)(CYHAL_PORT_11)) << 3U) + ((uint8_t)(1))),
    P11_2 = ((((uint8_t)(CYHAL_PORT_11)) << 3U) + ((uint8_t)(2))),
    P11_3 = ((((uint8_t)(CYHAL_PORT_11)) << 3U) + ((uint8_t)(3))),
    P11_4 = ((((uint8_t)(CYHAL_PORT_11)) << 3U) + ((uint8_t)(4))),
    P11_5 = ((((uint8_t)(CYHAL_PORT_11)) << 3U) + ((uint8_t)(5))),
    P11_6 = ((((uint8_t)(CYHAL_PORT_11)) << 3U) + ((uint8_t)(6))),
    P11_7 = ((((uint8_t)(CYHAL_PORT_11)) << 3U) + ((uint8_t)(7))),
    P12_0 = ((((uint8_t)(CYHAL_PORT_12)) << 3U) + ((uint8_t)(0))),
    P12_1 = ((((uint8_t)(CYHAL_PORT_12)) << 3U) + ((uint8_t)(1))),
    P12_2 = ((((uint8_t)(CYHAL_PORT_12)) << 3U) + ((uint8_t)(2))),
    P12_3 = ((((uint8_t)(CYHAL_PORT_12)) << 3U) + ((uint8_t)(3))),
    P12_4 = ((((uint8_t)(CYHAL_PORT_12)) << 3U) + ((uint8_t)(4))),
    P12_5 = ((((uint8_t)(CYHAL_PORT_12)) << 3U) + ((uint8_t)(5))),
    P12_6 = ((((uint8_t)(CYHAL_PORT_12)) << 3U) + ((uint8_t)(6))),
    P12_7 = ((((uint8_t)(CYHAL_PORT_12)) << 3U) + ((uint8_t)(7))),
    P13_0 = ((((uint8_t)(CYHAL_PORT_13)) << 3U) + ((uint8_t)(0))),
    P13_1 = ((((uint8_t)(CYHAL_PORT_13)) << 3U) + ((uint8_t)(1))),
    P13_6 = ((((uint8_t)(CYHAL_PORT_13)) << 3U) + ((uint8_t)(6))),
    P13_7 = ((((uint8_t)(CYHAL_PORT_13)) << 3U) + ((uint8_t)(7))),
} cyhal_gpio_psoc6_01_116_bga_ble_t;
typedef cyhal_gpio_psoc6_01_116_bga_ble_t cyhal_gpio_t;
typedef struct
{
    uint8_t block_num;
    uint8_t channel_num;
    cyhal_gpio_t pin;
    en_hsiom_sel_t hsiom;
} cyhal_resource_pin_mapping_t;
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_audioss_clk_i2s_if[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_audioss_pdm_clk[2];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_audioss_pdm_data[2];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_audioss_rx_sck[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_audioss_rx_sdi[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_audioss_rx_ws[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_audioss_tx_sck[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_audioss_tx_sdo[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_audioss_tx_ws[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_ext_lna_rx_ctl_out[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_ext_pa_lna_chip_en_out[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_ext_pa_tx_ctl_out[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_act_bpktctl[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_act_dbus_rx_en[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_act_dbus_tx_en[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_act_txd_rxd[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_act_ldo_en[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_buck_en[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_clk_en[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_dig_ldo_en[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_isolate_n[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_mxd_clk_out[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_rcb_clk[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_rcb_data[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_rcb_le[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_reset_n[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_ret_ldo_ol_hv[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_ret_switch_hv[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_bless_mxd_dpslp_xtal_en[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_cpuss_clk_fm_pump[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_cpuss_fault_out[2];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_cpuss_swj_swclk_tclk[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_cpuss_swj_swdio_tms[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_cpuss_swj_swdoe_tdi[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_cpuss_swj_swo_tdo[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_cpuss_swj_trstn[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_cpuss_trace_clock[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_cpuss_trace_data[12];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_dac_ctdac_voutsw[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_lpcomp_dsi_comp[2];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_lpcomp_inn_comp[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_lpcomp_inp_comp[2];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_opamp_dsi_ctb_cmp[2];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_opamp_out_10x[2];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_opamp_vin_m[2];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_opamp_vin_p0[2];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_opamp_vin_p1[2];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_pass_sarmux_pads[7];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_peri_tr_io_input[22];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_peri_tr_io_output[6];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_i2c_scl[14];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_i2c_sda[14];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_m_clk[13];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_m_miso[14];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_m_mosi[14];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_m_select0[13];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_m_select1[10];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_m_select2[10];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_m_select3[8];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_s_clk[13];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_s_miso[14];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_s_mosi[14];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_s_select0[13];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_s_select1[10];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_s_select2[10];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_spi_s_select3[8];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_uart_cts[11];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_uart_rts[11];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_uart_rx[12];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_scb_uart_tx[12];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_clk[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_data0[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_data1[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_data2[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_data3[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_data4[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_data5[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_data6[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_data7[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_select0[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_select1[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_select2[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_smif_spi_select3[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_tcpwm_line[78];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_tcpwm_line_compl[74];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_usb_usb_dm_pad[1];
extern const cyhal_resource_pin_mapping_t cyhal_pin_map_usb_usb_dp_pad[1];

typedef enum
{
    _CYHAL_TRIGGER_CPUSS_ZERO = 0,
    _CYHAL_TRIGGER_AUDIOSS_TR_I2S_RX_REQ = 1,
    _CYHAL_TRIGGER_AUDIOSS_TR_I2S_TX_REQ = 2,
    _CYHAL_TRIGGER_AUDIOSS_TR_PDM_RX_REQ = 3,
    _CYHAL_TRIGGER_CPUSS_CTI_TR_OUT0 = 4,
    _CYHAL_TRIGGER_CPUSS_CTI_TR_OUT1 = 5,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT0 = 6,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT1 = 7,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT2 = 8,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT3 = 9,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT4 = 10,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT5 = 11,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT6 = 12,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT7 = 13,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT8 = 14,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT9 = 15,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT10 = 16,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT11 = 17,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT12 = 18,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT13 = 19,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT14 = 20,
    _CYHAL_TRIGGER_CPUSS_DW0_TR_OUT15 = 21,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT0 = 22,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT1 = 23,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT2 = 24,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT3 = 25,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT4 = 26,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT5 = 27,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT6 = 28,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT7 = 29,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT8 = 30,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT9 = 31,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT10 = 32,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT11 = 33,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT12 = 34,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT13 = 35,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT14 = 36,
    _CYHAL_TRIGGER_CPUSS_DW1_TR_OUT15 = 37,
    _CYHAL_TRIGGER_CPUSS_TR_FAULT0 = 38,
    _CYHAL_TRIGGER_CPUSS_TR_FAULT1 = 39,
    _CYHAL_TRIGGER_CSD_DSI_SENSE_OUT = 40,
    _CYHAL_TRIGGER_CSD_TR_ADC_DONE = 41,
    _CYHAL_TRIGGER_LPCOMP_DSI_COMP0 = 42,
    _CYHAL_TRIGGER_LPCOMP_DSI_COMP1 = 43,
    _CYHAL_TRIGGER_PASS_DSI_CTB_CMP0 = 44,
    _CYHAL_TRIGGER_PASS_DSI_CTB_CMP1 = 45,
    _CYHAL_TRIGGER_PASS_TR_CTDAC_EMPTY = 46,
    _CYHAL_TRIGGER_PASS_TR_SAR_OUT = 47,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT0 = 48,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT1 = 49,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT2 = 50,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT3 = 51,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT4 = 52,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT5 = 53,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT6 = 54,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT7 = 55,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT8 = 56,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT9 = 57,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT10 = 58,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT11 = 59,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT12 = 60,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT13 = 61,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT14 = 62,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT15 = 63,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT16 = 64,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT17 = 65,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT18 = 66,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT19 = 67,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT20 = 68,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT21 = 69,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT22 = 70,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT23 = 71,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT24 = 72,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT25 = 73,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT26 = 74,
    _CYHAL_TRIGGER_PERI_TR_IO_INPUT27 = 75,
    _CYHAL_TRIGGER_SCB0_TR_I2C_SCL_FILTERED = 76,
    _CYHAL_TRIGGER_SCB1_TR_I2C_SCL_FILTERED = 77,
    _CYHAL_TRIGGER_SCB2_TR_I2C_SCL_FILTERED = 78,
    _CYHAL_TRIGGER_SCB3_TR_I2C_SCL_FILTERED = 79,
    _CYHAL_TRIGGER_SCB4_TR_I2C_SCL_FILTERED = 80,
    _CYHAL_TRIGGER_SCB5_TR_I2C_SCL_FILTERED = 81,
    _CYHAL_TRIGGER_SCB6_TR_I2C_SCL_FILTERED = 82,
    _CYHAL_TRIGGER_SCB7_TR_I2C_SCL_FILTERED = 83,
    _CYHAL_TRIGGER_SCB8_TR_I2C_SCL_FILTERED = 84,
    _CYHAL_TRIGGER_SCB0_TR_RX_REQ = 85,
    _CYHAL_TRIGGER_SCB1_TR_RX_REQ = 86,
    _CYHAL_TRIGGER_SCB2_TR_RX_REQ = 87,
    _CYHAL_TRIGGER_SCB3_TR_RX_REQ = 88,
    _CYHAL_TRIGGER_SCB4_TR_RX_REQ = 89,
    _CYHAL_TRIGGER_SCB5_TR_RX_REQ = 90,
    _CYHAL_TRIGGER_SCB6_TR_RX_REQ = 91,
    _CYHAL_TRIGGER_SCB7_TR_RX_REQ = 92,
    _CYHAL_TRIGGER_SCB8_TR_RX_REQ = 93,
    _CYHAL_TRIGGER_SCB0_TR_TX_REQ = 94,
    _CYHAL_TRIGGER_SCB1_TR_TX_REQ = 95,
    _CYHAL_TRIGGER_SCB2_TR_TX_REQ = 96,
    _CYHAL_TRIGGER_SCB3_TR_TX_REQ = 97,
    _CYHAL_TRIGGER_SCB4_TR_TX_REQ = 98,
    _CYHAL_TRIGGER_SCB5_TR_TX_REQ = 99,
    _CYHAL_TRIGGER_SCB6_TR_TX_REQ = 100,
    _CYHAL_TRIGGER_SCB7_TR_TX_REQ = 101,
    _CYHAL_TRIGGER_SCB8_TR_TX_REQ = 102,
    _CYHAL_TRIGGER_SMIF_TR_RX_REQ = 103,
    _CYHAL_TRIGGER_SMIF_TR_TX_REQ = 104,
    _CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH0 = 105,
    _CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH1 = 106,
    _CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH2 = 107,
    _CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH3 = 108,
    _CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH4 = 109,
    _CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH5 = 110,
    _CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH6 = 111,
    _CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH7 = 112,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH0 = 113,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH1 = 114,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH2 = 115,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH3 = 116,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH4 = 117,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH5 = 118,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH6 = 119,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH7 = 120,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH8 = 121,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH9 = 122,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH10 = 123,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH11 = 124,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH12 = 125,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH13 = 126,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH14 = 127,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH15 = 128,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH16 = 129,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH17 = 130,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH18 = 131,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH19 = 132,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH20 = 133,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH21 = 134,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH22 = 135,
    _CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH23 = 136,
    _CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW0 = 137,
    _CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW1 = 138,
    _CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW2 = 139,
    _CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW3 = 140,
    _CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW4 = 141,
    _CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW5 = 142,
    _CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW6 = 143,
    _CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW7 = 144,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW0 = 145,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW1 = 146,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW2 = 147,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW3 = 148,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW4 = 149,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW5 = 150,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW6 = 151,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW7 = 152,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW8 = 153,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW9 = 154,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW10 = 155,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW11 = 156,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW12 = 157,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW13 = 158,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW14 = 159,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW15 = 160,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW16 = 161,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW17 = 162,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW18 = 163,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW19 = 164,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW20 = 165,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW21 = 166,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW22 = 167,
    _CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW23 = 168,
    _CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW0 = 169,
    _CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW1 = 170,
    _CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW2 = 171,
    _CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW3 = 172,
    _CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW4 = 173,
    _CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW5 = 174,
    _CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW6 = 175,
    _CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW7 = 176,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW0 = 177,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW1 = 178,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW2 = 179,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW3 = 180,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW4 = 181,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW5 = 182,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW6 = 183,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW7 = 184,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW8 = 185,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW9 = 186,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW10 = 187,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW11 = 188,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW12 = 189,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW13 = 190,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW14 = 191,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW15 = 192,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW16 = 193,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW17 = 194,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW18 = 195,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW19 = 196,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW20 = 197,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW21 = 198,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW22 = 199,
    _CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW23 = 200,
    _CYHAL_TRIGGER_TR_GROUP10_OUTPUT0 = 201,
    _CYHAL_TRIGGER_TR_GROUP10_OUTPUT1 = 202,
    _CYHAL_TRIGGER_TR_GROUP10_OUTPUT2 = 203,
    _CYHAL_TRIGGER_TR_GROUP10_OUTPUT3 = 204,
    _CYHAL_TRIGGER_TR_GROUP10_OUTPUT4 = 205,
    _CYHAL_TRIGGER_TR_GROUP10_OUTPUT5 = 206,
    _CYHAL_TRIGGER_TR_GROUP10_OUTPUT6 = 207,
    _CYHAL_TRIGGER_TR_GROUP10_OUTPUT7 = 208,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT0 = 209,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT1 = 210,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT2 = 211,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT3 = 212,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT4 = 213,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT5 = 214,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT6 = 215,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT7 = 216,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT8 = 217,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT9 = 218,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT10 = 219,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT11 = 220,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT12 = 221,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT13 = 222,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT14 = 223,
    _CYHAL_TRIGGER_TR_GROUP11_OUTPUT15 = 224,
    _CYHAL_TRIGGER_TR_GROUP12_OUTPUT0 = 225,
    _CYHAL_TRIGGER_TR_GROUP12_OUTPUT1 = 226,
    _CYHAL_TRIGGER_TR_GROUP12_OUTPUT2 = 227,
    _CYHAL_TRIGGER_TR_GROUP12_OUTPUT3 = 228,
    _CYHAL_TRIGGER_TR_GROUP12_OUTPUT4 = 229,
    _CYHAL_TRIGGER_TR_GROUP12_OUTPUT5 = 230,
    _CYHAL_TRIGGER_TR_GROUP12_OUTPUT6 = 231,
    _CYHAL_TRIGGER_TR_GROUP12_OUTPUT7 = 232,
    _CYHAL_TRIGGER_TR_GROUP12_OUTPUT8 = 233,
    _CYHAL_TRIGGER_TR_GROUP12_OUTPUT9 = 234,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT0 = 235,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT1 = 236,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT2 = 237,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT3 = 238,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT4 = 239,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT5 = 240,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT6 = 241,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT7 = 242,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT8 = 243,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT9 = 244,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT10 = 245,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT11 = 246,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT12 = 247,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT13 = 248,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT14 = 249,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT15 = 250,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT16 = 251,
    _CYHAL_TRIGGER_TR_GROUP13_OUTPUT17 = 252,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT0 = 253,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT1 = 254,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT2 = 255,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT3 = 256,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT4 = 257,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT5 = 258,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT6 = 259,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT7 = 260,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT8 = 261,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT9 = 262,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT10 = 263,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT11 = 264,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT12 = 265,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT13 = 266,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT14 = 267,
    _CYHAL_TRIGGER_TR_GROUP14_OUTPUT15 = 268,
    _CYHAL_TRIGGER_UDB_DSI_OUT_TR0 = 269,
    _CYHAL_TRIGGER_UDB_DSI_OUT_TR1 = 270,
    _CYHAL_TRIGGER_UDB_TR_UDB0 = 271,
    _CYHAL_TRIGGER_UDB_TR_UDB1 = 272,
    _CYHAL_TRIGGER_UDB_TR_UDB2 = 273,
    _CYHAL_TRIGGER_UDB_TR_UDB3 = 274,
    _CYHAL_TRIGGER_UDB_TR_UDB4 = 275,
    _CYHAL_TRIGGER_UDB_TR_UDB5 = 276,
    _CYHAL_TRIGGER_UDB_TR_UDB6 = 277,
    _CYHAL_TRIGGER_UDB_TR_UDB7 = 278,
    _CYHAL_TRIGGER_UDB_TR_UDB8 = 279,
    _CYHAL_TRIGGER_UDB_TR_UDB9 = 280,
    _CYHAL_TRIGGER_UDB_TR_UDB10 = 281,
    _CYHAL_TRIGGER_UDB_TR_UDB11 = 282,
    _CYHAL_TRIGGER_UDB_TR_UDB12 = 283,
    _CYHAL_TRIGGER_UDB_TR_UDB13 = 284,
    _CYHAL_TRIGGER_UDB_TR_UDB14 = 285,
    _CYHAL_TRIGGER_UDB_TR_UDB15 = 286,
    _CYHAL_TRIGGER_USB_DMA_REQ0 = 287,
    _CYHAL_TRIGGER_USB_DMA_REQ1 = 288,
    _CYHAL_TRIGGER_USB_DMA_REQ2 = 289,
    _CYHAL_TRIGGER_USB_DMA_REQ3 = 290,
    _CYHAL_TRIGGER_USB_DMA_REQ4 = 291,
    _CYHAL_TRIGGER_USB_DMA_REQ5 = 292,
    _CYHAL_TRIGGER_USB_DMA_REQ6 = 293,
    _CYHAL_TRIGGER_USB_DMA_REQ7 = 294,
} _cyhal_trigger_source_psoc6_01_t;
typedef _cyhal_trigger_source_psoc6_01_t cyhal_internal_source_t;
typedef enum
{
    CYHAL_TRIGGER_CPUSS_ZERO_EDGE = ((_CYHAL_TRIGGER_CPUSS_ZERO) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_ZERO_LEVEL = ((_CYHAL_TRIGGER_CPUSS_ZERO) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_AUDIOSS_TR_I2S_RX_REQ = ((_CYHAL_TRIGGER_AUDIOSS_TR_I2S_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_AUDIOSS_TR_I2S_TX_REQ = ((_CYHAL_TRIGGER_AUDIOSS_TR_I2S_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_AUDIOSS_TR_PDM_RX_REQ = ((_CYHAL_TRIGGER_AUDIOSS_TR_PDM_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_CPUSS_CTI_TR_OUT0 = ((_CYHAL_TRIGGER_CPUSS_CTI_TR_OUT0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_CTI_TR_OUT1 = ((_CYHAL_TRIGGER_CPUSS_CTI_TR_OUT1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT0 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT1 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT2 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT3 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT4 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT5 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT6 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT7 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT8 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT9 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT10 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT10) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT11 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT11) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT12 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT12) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT13 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT13) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT14 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT14) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW0_TR_OUT15 = ((_CYHAL_TRIGGER_CPUSS_DW0_TR_OUT15) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT0 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT1 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT2 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT3 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT4 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT5 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT6 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT7 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT8 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT9 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT10 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT10) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT11 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT11) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT12 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT12) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT13 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT13) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT14 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT14) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_DW1_TR_OUT15 = ((_CYHAL_TRIGGER_CPUSS_DW1_TR_OUT15) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_TR_FAULT0 = ((_CYHAL_TRIGGER_CPUSS_TR_FAULT0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CPUSS_TR_FAULT1 = ((_CYHAL_TRIGGER_CPUSS_TR_FAULT1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CSD_DSI_SENSE_OUT_EDGE = ((_CYHAL_TRIGGER_CSD_DSI_SENSE_OUT) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CSD_DSI_SENSE_OUT_LEVEL = ((_CYHAL_TRIGGER_CSD_DSI_SENSE_OUT) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_CSD_TR_ADC_DONE_EDGE = ((_CYHAL_TRIGGER_CSD_TR_ADC_DONE) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_CSD_TR_ADC_DONE_LEVEL = ((_CYHAL_TRIGGER_CSD_TR_ADC_DONE) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_LPCOMP_DSI_COMP0 = ((_CYHAL_TRIGGER_LPCOMP_DSI_COMP0) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_LPCOMP_DSI_COMP1 = ((_CYHAL_TRIGGER_LPCOMP_DSI_COMP1) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PASS_DSI_CTB_CMP0_EDGE = ((_CYHAL_TRIGGER_PASS_DSI_CTB_CMP0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PASS_DSI_CTB_CMP0_LEVEL = ((_CYHAL_TRIGGER_PASS_DSI_CTB_CMP0) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PASS_DSI_CTB_CMP1_EDGE = ((_CYHAL_TRIGGER_PASS_DSI_CTB_CMP1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PASS_DSI_CTB_CMP1_LEVEL = ((_CYHAL_TRIGGER_PASS_DSI_CTB_CMP1) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PASS_TR_CTDAC_EMPTY = ((_CYHAL_TRIGGER_PASS_TR_CTDAC_EMPTY) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PASS_TR_SAR_OUT = ((_CYHAL_TRIGGER_PASS_TR_SAR_OUT) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT0_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT0_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT0) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT1_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT1_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT1) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT2_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT2_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT2) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT3_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT3_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT3) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT4_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT4_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT4) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT5_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT5_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT5) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT6_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT6_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT6) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT7_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT7_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT7) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT8_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT8_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT8) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT9_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT9_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT9) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT10_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT10) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT10_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT10) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT11_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT11) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT11_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT11) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT12_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT12) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT12_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT12) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT13_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT13) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT13_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT13) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT14_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT14) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT14_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT14) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT15_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT15) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT15_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT15) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT16_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT16) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT16_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT16) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT17_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT17) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT17_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT17) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT18_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT18) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT18_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT18) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT19_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT19) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT19_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT19) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT20_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT20) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT20_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT20) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT21_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT21) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT21_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT21) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT22_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT22) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT22_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT22) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT23_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT23) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT23_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT23) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT24_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT24) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT24_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT24) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT25_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT25) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT25_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT25) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT26_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT26) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT26_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT26) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT27_EDGE = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT27) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_PERI_TR_IO_INPUT27_LEVEL = ((_CYHAL_TRIGGER_PERI_TR_IO_INPUT27) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB0_TR_I2C_SCL_FILTERED = ((_CYHAL_TRIGGER_SCB0_TR_I2C_SCL_FILTERED) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB1_TR_I2C_SCL_FILTERED = ((_CYHAL_TRIGGER_SCB1_TR_I2C_SCL_FILTERED) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB2_TR_I2C_SCL_FILTERED = ((_CYHAL_TRIGGER_SCB2_TR_I2C_SCL_FILTERED) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB3_TR_I2C_SCL_FILTERED = ((_CYHAL_TRIGGER_SCB3_TR_I2C_SCL_FILTERED) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB4_TR_I2C_SCL_FILTERED = ((_CYHAL_TRIGGER_SCB4_TR_I2C_SCL_FILTERED) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB5_TR_I2C_SCL_FILTERED = ((_CYHAL_TRIGGER_SCB5_TR_I2C_SCL_FILTERED) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB6_TR_I2C_SCL_FILTERED = ((_CYHAL_TRIGGER_SCB6_TR_I2C_SCL_FILTERED) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB7_TR_I2C_SCL_FILTERED = ((_CYHAL_TRIGGER_SCB7_TR_I2C_SCL_FILTERED) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB8_TR_I2C_SCL_FILTERED = ((_CYHAL_TRIGGER_SCB8_TR_I2C_SCL_FILTERED) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB0_TR_RX_REQ = ((_CYHAL_TRIGGER_SCB0_TR_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB1_TR_RX_REQ = ((_CYHAL_TRIGGER_SCB1_TR_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB2_TR_RX_REQ = ((_CYHAL_TRIGGER_SCB2_TR_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB3_TR_RX_REQ = ((_CYHAL_TRIGGER_SCB3_TR_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB4_TR_RX_REQ = ((_CYHAL_TRIGGER_SCB4_TR_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB5_TR_RX_REQ = ((_CYHAL_TRIGGER_SCB5_TR_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB6_TR_RX_REQ = ((_CYHAL_TRIGGER_SCB6_TR_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB7_TR_RX_REQ = ((_CYHAL_TRIGGER_SCB7_TR_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB8_TR_RX_REQ = ((_CYHAL_TRIGGER_SCB8_TR_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB0_TR_TX_REQ = ((_CYHAL_TRIGGER_SCB0_TR_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB1_TR_TX_REQ = ((_CYHAL_TRIGGER_SCB1_TR_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB2_TR_TX_REQ = ((_CYHAL_TRIGGER_SCB2_TR_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB3_TR_TX_REQ = ((_CYHAL_TRIGGER_SCB3_TR_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB4_TR_TX_REQ = ((_CYHAL_TRIGGER_SCB4_TR_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB5_TR_TX_REQ = ((_CYHAL_TRIGGER_SCB5_TR_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB6_TR_TX_REQ = ((_CYHAL_TRIGGER_SCB6_TR_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB7_TR_TX_REQ = ((_CYHAL_TRIGGER_SCB7_TR_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SCB8_TR_TX_REQ = ((_CYHAL_TRIGGER_SCB8_TR_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SMIF_TR_RX_REQ = ((_CYHAL_TRIGGER_SMIF_TR_RX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_SMIF_TR_TX_REQ = ((_CYHAL_TRIGGER_SMIF_TR_TX_REQ) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH0 = ((_CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH1 = ((_CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH2 = ((_CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH3 = ((_CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH4 = ((_CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH5 = ((_CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH6 = ((_CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH7 = ((_CYHAL_TRIGGER_TCPWM0_TR_COMPARE_MATCH7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH0 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH1 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH2 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH3 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH4 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH5 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH6 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH7 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH8 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH9 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH10 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH10) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH11 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH11) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH12 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH12) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH13 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH13) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH14 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH14) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH15 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH15) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH16 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH16) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH17 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH17) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH18 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH18) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH19 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH19) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH20 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH20) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH21 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH21) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH22 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH22) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH23 = ((_CYHAL_TRIGGER_TCPWM1_TR_COMPARE_MATCH23) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW0 = ((_CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW1 = ((_CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW2 = ((_CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW3 = ((_CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW4 = ((_CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW5 = ((_CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW6 = ((_CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW7 = ((_CYHAL_TRIGGER_TCPWM0_TR_OVERFLOW7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW0 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW1 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW2 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW3 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW4 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW5 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW6 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW7 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW8 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW9 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW10 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW10) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW11 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW11) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW12 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW12) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW13 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW13) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW14 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW14) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW15 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW15) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW16 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW16) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW17 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW17) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW18 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW18) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW19 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW19) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW20 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW20) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW21 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW21) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW22 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW22) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW23 = ((_CYHAL_TRIGGER_TCPWM1_TR_OVERFLOW23) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW0 = ((_CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW1 = ((_CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW2 = ((_CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW3 = ((_CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW4 = ((_CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW5 = ((_CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW6 = ((_CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW7 = ((_CYHAL_TRIGGER_TCPWM0_TR_UNDERFLOW7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW0 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW1 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW2 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW3 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW4 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW5 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW6 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW7 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW8 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW9 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW10 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW10) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW11 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW11) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW12 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW12) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW13 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW13) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW14 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW14) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW15 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW15) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW16 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW16) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW17 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW17) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW18 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW18) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW19 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW19) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW20 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW20) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW21 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW21) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW22 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW22) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW23 = ((_CYHAL_TRIGGER_TCPWM1_TR_UNDERFLOW23) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT0_EDGE = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT0_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT0) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT1_EDGE = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT1_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT1) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT2_EDGE = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT2_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT2) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT3_EDGE = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT3_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT3) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT4_EDGE = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT4_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT4) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT5_EDGE = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT5_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT5) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT6_EDGE = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT6_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT6) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT7_EDGE = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP10_OUTPUT7_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP10_OUTPUT7) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT0_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT0_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT0) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT1_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT1_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT1) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT2_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT2_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT2) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT3_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT3_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT3) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT4_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT4_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT4) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT5_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT5_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT5) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT6_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT6_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT6) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT7_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT7_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT7) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT8_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT8_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT8) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT9_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT9_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT9) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT10_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT10) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT10_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT10) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT11_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT11) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT11_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT11) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT12_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT12) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT12_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT12) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT13_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT13) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT13_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT13) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT14_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT14) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT14_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT14) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT15_EDGE = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT15) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP11_OUTPUT15_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP11_OUTPUT15) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT0_EDGE = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT0_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT0) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT1_EDGE = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT1_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT1) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT2_EDGE = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT2_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT2) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT3_EDGE = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT3_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT3) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT4_EDGE = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT4_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT4) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT5_EDGE = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT5_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT5) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT6_EDGE = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT6_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT6) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT7_EDGE = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT7_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT7) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT8_EDGE = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT8_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT8) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT9_EDGE = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP12_OUTPUT9_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP12_OUTPUT9) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT0_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT0_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT0) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT1_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT1_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT1) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT2_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT2_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT2) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT3_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT3_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT3) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT4_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT4_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT4) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT5_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT5_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT5) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT6_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT6_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT6) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT7_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT7_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT7) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT8_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT8_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT8) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT9_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT9_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT9) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT10_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT10) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT10_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT10) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT11_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT11) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT11_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT11) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT12_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT12) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT12_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT12) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT13_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT13) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT13_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT13) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT14_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT14) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT14_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT14) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT15_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT15) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT15_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT15) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT16_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT16) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT16_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT16) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT17_EDGE = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT17) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP13_OUTPUT17_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP13_OUTPUT17) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT0_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT0_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT0) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT1_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT1_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT1) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT2_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT2_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT2) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT3_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT3_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT3) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT4_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT4_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT4) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT5_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT5_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT5) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT6_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT6_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT6) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT7_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT7_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT7) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT8_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT8_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT8) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT9_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT9_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT9) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT10_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT10) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT10_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT10) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT11_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT11) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT11_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT11) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT12_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT12) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT12_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT12) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT13_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT13) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT13_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT13) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT14_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT14) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT14_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT14) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT15_EDGE = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT15) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_TR_GROUP14_OUTPUT15_LEVEL = ((_CYHAL_TRIGGER_TR_GROUP14_OUTPUT15) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_DSI_OUT_TR0_EDGE = ((_CYHAL_TRIGGER_UDB_DSI_OUT_TR0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_DSI_OUT_TR0_LEVEL = ((_CYHAL_TRIGGER_UDB_DSI_OUT_TR0) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_DSI_OUT_TR1_EDGE = ((_CYHAL_TRIGGER_UDB_DSI_OUT_TR1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_DSI_OUT_TR1_LEVEL = ((_CYHAL_TRIGGER_UDB_DSI_OUT_TR1) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB0_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB0_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB0) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB1_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB1_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB1) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB2_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB2_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB2) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB3_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB3_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB3) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB4_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB4_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB4) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB5_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB5_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB5) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB6_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB6_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB6) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB7_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB7_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB7) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB8_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB8) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB8_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB8) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB9_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB9) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB9_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB9) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB10_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB10) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB10_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB10) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB11_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB11) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB11_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB11) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB12_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB12) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB12_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB12) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB13_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB13) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB13_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB13) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB14_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB14) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB14_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB14) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_UDB_TR_UDB15_EDGE = ((_CYHAL_TRIGGER_UDB_TR_UDB15) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_UDB_TR_UDB15_LEVEL = ((_CYHAL_TRIGGER_UDB_TR_UDB15) << 1 | (CYHAL_SIGNAL_TYPE_LEVEL)),
    CYHAL_TRIGGER_USB_DMA_REQ0 = ((_CYHAL_TRIGGER_USB_DMA_REQ0) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_USB_DMA_REQ1 = ((_CYHAL_TRIGGER_USB_DMA_REQ1) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_USB_DMA_REQ2 = ((_CYHAL_TRIGGER_USB_DMA_REQ2) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_USB_DMA_REQ3 = ((_CYHAL_TRIGGER_USB_DMA_REQ3) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_USB_DMA_REQ4 = ((_CYHAL_TRIGGER_USB_DMA_REQ4) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_USB_DMA_REQ5 = ((_CYHAL_TRIGGER_USB_DMA_REQ5) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_USB_DMA_REQ6 = ((_CYHAL_TRIGGER_USB_DMA_REQ6) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
    CYHAL_TRIGGER_USB_DMA_REQ7 = ((_CYHAL_TRIGGER_USB_DMA_REQ7) << 1 | (CYHAL_SIGNAL_TYPE_EDGE)),
} cyhal_trigger_source_psoc6_01_t;
typedef cyhal_trigger_source_psoc6_01_t cyhal_source_t;
typedef enum
{
    CYHAL_TRIGGER_CPUSS_CTI_TR_IN0 = 0,
    CYHAL_TRIGGER_CPUSS_CTI_TR_IN1 = 1,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN0 = 2,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN1 = 3,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN2 = 4,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN3 = 5,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN4 = 6,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN5 = 7,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN6 = 8,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN7 = 9,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN8 = 10,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN9 = 11,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN10 = 12,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN11 = 13,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN12 = 14,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN13 = 15,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN14 = 16,
    CYHAL_TRIGGER_CPUSS_DW0_TR_IN15 = 17,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN0 = 18,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN1 = 19,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN2 = 20,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN3 = 21,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN4 = 22,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN5 = 23,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN6 = 24,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN7 = 25,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN8 = 26,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN9 = 27,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN10 = 28,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN11 = 29,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN12 = 30,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN13 = 31,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN14 = 32,
    CYHAL_TRIGGER_CPUSS_DW1_TR_IN15 = 33,
    CYHAL_TRIGGER_PASS_TR_SAR_IN = 34,
    CYHAL_TRIGGER_PERI_TR_IO_OUTPUT0 = 35,
    CYHAL_TRIGGER_PERI_TR_IO_OUTPUT1 = 36,
    CYHAL_TRIGGER_PROFILE_TR_START = 37,
    CYHAL_TRIGGER_PROFILE_TR_STOP = 38,
    CYHAL_TRIGGER_TCPWM0_TR_IN0 = 39,
    CYHAL_TRIGGER_TCPWM0_TR_IN1 = 40,
    CYHAL_TRIGGER_TCPWM0_TR_IN2 = 41,
    CYHAL_TRIGGER_TCPWM0_TR_IN3 = 42,
    CYHAL_TRIGGER_TCPWM0_TR_IN4 = 43,
    CYHAL_TRIGGER_TCPWM0_TR_IN5 = 44,
    CYHAL_TRIGGER_TCPWM0_TR_IN6 = 45,
    CYHAL_TRIGGER_TCPWM0_TR_IN7 = 46,
    CYHAL_TRIGGER_TCPWM0_TR_IN8 = 47,
    CYHAL_TRIGGER_TCPWM0_TR_IN9 = 48,
    CYHAL_TRIGGER_TCPWM0_TR_IN10 = 49,
    CYHAL_TRIGGER_TCPWM0_TR_IN11 = 50,
    CYHAL_TRIGGER_TCPWM0_TR_IN12 = 51,
    CYHAL_TRIGGER_TCPWM0_TR_IN13 = 52,
    CYHAL_TRIGGER_TCPWM1_TR_IN0 = 53,
    CYHAL_TRIGGER_TCPWM1_TR_IN1 = 54,
    CYHAL_TRIGGER_TCPWM1_TR_IN2 = 55,
    CYHAL_TRIGGER_TCPWM1_TR_IN3 = 56,
    CYHAL_TRIGGER_TCPWM1_TR_IN4 = 57,
    CYHAL_TRIGGER_TCPWM1_TR_IN5 = 58,
    CYHAL_TRIGGER_TCPWM1_TR_IN6 = 59,
    CYHAL_TRIGGER_TCPWM1_TR_IN7 = 60,
    CYHAL_TRIGGER_TCPWM1_TR_IN8 = 61,
    CYHAL_TRIGGER_TCPWM1_TR_IN9 = 62,
    CYHAL_TRIGGER_TCPWM1_TR_IN10 = 63,
    CYHAL_TRIGGER_TCPWM1_TR_IN11 = 64,
    CYHAL_TRIGGER_TCPWM1_TR_IN12 = 65,
    CYHAL_TRIGGER_TCPWM1_TR_IN13 = 66,
    CYHAL_TRIGGER_TR_GROUP0_INPUT1 = 67,
    CYHAL_TRIGGER_TR_GROUP0_INPUT2 = 68,
    CYHAL_TRIGGER_TR_GROUP0_INPUT3 = 69,
    CYHAL_TRIGGER_TR_GROUP0_INPUT4 = 70,
    CYHAL_TRIGGER_TR_GROUP0_INPUT5 = 71,
    CYHAL_TRIGGER_TR_GROUP0_INPUT6 = 72,
    CYHAL_TRIGGER_TR_GROUP0_INPUT7 = 73,
    CYHAL_TRIGGER_TR_GROUP0_INPUT8 = 74,
    CYHAL_TRIGGER_TR_GROUP0_INPUT9 = 75,
    CYHAL_TRIGGER_TR_GROUP0_INPUT10 = 76,
    CYHAL_TRIGGER_TR_GROUP0_INPUT11 = 77,
    CYHAL_TRIGGER_TR_GROUP0_INPUT12 = 78,
    CYHAL_TRIGGER_TR_GROUP0_INPUT13 = 79,
    CYHAL_TRIGGER_TR_GROUP0_INPUT14 = 80,
    CYHAL_TRIGGER_TR_GROUP0_INPUT15 = 81,
    CYHAL_TRIGGER_TR_GROUP0_INPUT16 = 82,
    CYHAL_TRIGGER_TR_GROUP0_INPUT17 = 83,
    CYHAL_TRIGGER_TR_GROUP0_INPUT18 = 84,
    CYHAL_TRIGGER_TR_GROUP0_INPUT19 = 85,
    CYHAL_TRIGGER_TR_GROUP0_INPUT20 = 86,
    CYHAL_TRIGGER_TR_GROUP0_INPUT21 = 87,
    CYHAL_TRIGGER_TR_GROUP0_INPUT22 = 88,
    CYHAL_TRIGGER_TR_GROUP0_INPUT23 = 89,
    CYHAL_TRIGGER_TR_GROUP0_INPUT24 = 90,
    CYHAL_TRIGGER_TR_GROUP0_INPUT25 = 91,
    CYHAL_TRIGGER_TR_GROUP0_INPUT26 = 92,
    CYHAL_TRIGGER_TR_GROUP0_INPUT27 = 93,
    CYHAL_TRIGGER_TR_GROUP0_INPUT28 = 94,
    CYHAL_TRIGGER_TR_GROUP0_INPUT29 = 95,
    CYHAL_TRIGGER_TR_GROUP0_INPUT30 = 96,
    CYHAL_TRIGGER_TR_GROUP0_INPUT31 = 97,
    CYHAL_TRIGGER_TR_GROUP0_INPUT32 = 98,
    CYHAL_TRIGGER_TR_GROUP0_INPUT33 = 99,
    CYHAL_TRIGGER_TR_GROUP0_INPUT34 = 100,
    CYHAL_TRIGGER_TR_GROUP0_INPUT35 = 101,
    CYHAL_TRIGGER_TR_GROUP0_INPUT36 = 102,
    CYHAL_TRIGGER_TR_GROUP0_INPUT37 = 103,
    CYHAL_TRIGGER_TR_GROUP0_INPUT38 = 104,
    CYHAL_TRIGGER_TR_GROUP0_INPUT39 = 105,
    CYHAL_TRIGGER_TR_GROUP0_INPUT40 = 106,
    CYHAL_TRIGGER_TR_GROUP0_INPUT41 = 107,
    CYHAL_TRIGGER_TR_GROUP0_INPUT42 = 108,
    CYHAL_TRIGGER_TR_GROUP0_INPUT43 = 109,
    CYHAL_TRIGGER_TR_GROUP0_INPUT44 = 110,
    CYHAL_TRIGGER_TR_GROUP0_INPUT45 = 111,
    CYHAL_TRIGGER_TR_GROUP0_INPUT46 = 112,
    CYHAL_TRIGGER_TR_GROUP0_INPUT47 = 113,
    CYHAL_TRIGGER_TR_GROUP0_INPUT48 = 114,
    CYHAL_TRIGGER_TR_GROUP0_INPUT49 = 115,
    CYHAL_TRIGGER_TR_GROUP0_INPUT50 = 116,
    CYHAL_TRIGGER_TR_GROUP1_INPUT1 = 117,
    CYHAL_TRIGGER_TR_GROUP1_INPUT2 = 118,
    CYHAL_TRIGGER_TR_GROUP1_INPUT3 = 119,
    CYHAL_TRIGGER_TR_GROUP1_INPUT4 = 120,
    CYHAL_TRIGGER_TR_GROUP1_INPUT5 = 121,
    CYHAL_TRIGGER_TR_GROUP1_INPUT6 = 122,
    CYHAL_TRIGGER_TR_GROUP1_INPUT7 = 123,
    CYHAL_TRIGGER_TR_GROUP1_INPUT8 = 124,
    CYHAL_TRIGGER_TR_GROUP1_INPUT9 = 125,
    CYHAL_TRIGGER_TR_GROUP1_INPUT10 = 126,
    CYHAL_TRIGGER_TR_GROUP1_INPUT11 = 127,
    CYHAL_TRIGGER_TR_GROUP1_INPUT12 = 128,
    CYHAL_TRIGGER_TR_GROUP1_INPUT13 = 129,
    CYHAL_TRIGGER_TR_GROUP1_INPUT14 = 130,
    CYHAL_TRIGGER_TR_GROUP1_INPUT15 = 131,
    CYHAL_TRIGGER_TR_GROUP1_INPUT16 = 132,
    CYHAL_TRIGGER_TR_GROUP1_INPUT17 = 133,
    CYHAL_TRIGGER_TR_GROUP1_INPUT18 = 134,
    CYHAL_TRIGGER_TR_GROUP1_INPUT19 = 135,
    CYHAL_TRIGGER_TR_GROUP1_INPUT20 = 136,
    CYHAL_TRIGGER_TR_GROUP1_INPUT21 = 137,
    CYHAL_TRIGGER_TR_GROUP1_INPUT22 = 138,
    CYHAL_TRIGGER_TR_GROUP1_INPUT23 = 139,
    CYHAL_TRIGGER_TR_GROUP1_INPUT24 = 140,
    CYHAL_TRIGGER_TR_GROUP1_INPUT25 = 141,
    CYHAL_TRIGGER_TR_GROUP1_INPUT26 = 142,
    CYHAL_TRIGGER_TR_GROUP1_INPUT27 = 143,
    CYHAL_TRIGGER_TR_GROUP1_INPUT28 = 144,
    CYHAL_TRIGGER_TR_GROUP1_INPUT29 = 145,
    CYHAL_TRIGGER_TR_GROUP1_INPUT30 = 146,
    CYHAL_TRIGGER_TR_GROUP1_INPUT31 = 147,
    CYHAL_TRIGGER_TR_GROUP1_INPUT32 = 148,
    CYHAL_TRIGGER_TR_GROUP1_INPUT33 = 149,
    CYHAL_TRIGGER_TR_GROUP1_INPUT34 = 150,
    CYHAL_TRIGGER_TR_GROUP1_INPUT35 = 151,
    CYHAL_TRIGGER_TR_GROUP1_INPUT36 = 152,
    CYHAL_TRIGGER_TR_GROUP1_INPUT37 = 153,
    CYHAL_TRIGGER_TR_GROUP1_INPUT38 = 154,
    CYHAL_TRIGGER_TR_GROUP1_INPUT39 = 155,
    CYHAL_TRIGGER_TR_GROUP1_INPUT40 = 156,
    CYHAL_TRIGGER_TR_GROUP1_INPUT41 = 157,
    CYHAL_TRIGGER_TR_GROUP1_INPUT42 = 158,
    CYHAL_TRIGGER_TR_GROUP1_INPUT43 = 159,
    CYHAL_TRIGGER_TR_GROUP1_INPUT44 = 160,
    CYHAL_TRIGGER_TR_GROUP1_INPUT45 = 161,
    CYHAL_TRIGGER_TR_GROUP1_INPUT46 = 162,
    CYHAL_TRIGGER_TR_GROUP1_INPUT47 = 163,
    CYHAL_TRIGGER_TR_GROUP1_INPUT48 = 164,
    CYHAL_TRIGGER_TR_GROUP1_INPUT49 = 165,
    CYHAL_TRIGGER_TR_GROUP1_INPUT50 = 166,
    CYHAL_TRIGGER_TR_GROUP2_INPUT1 = 167,
    CYHAL_TRIGGER_TR_GROUP2_INPUT2 = 168,
    CYHAL_TRIGGER_TR_GROUP2_INPUT3 = 169,
    CYHAL_TRIGGER_TR_GROUP2_INPUT4 = 170,
    CYHAL_TRIGGER_TR_GROUP2_INPUT5 = 171,
    CYHAL_TRIGGER_TR_GROUP2_INPUT6 = 172,
    CYHAL_TRIGGER_TR_GROUP2_INPUT7 = 173,
    CYHAL_TRIGGER_TR_GROUP2_INPUT8 = 174,
    CYHAL_TRIGGER_TR_GROUP2_INPUT9 = 175,
    CYHAL_TRIGGER_TR_GROUP2_INPUT10 = 176,
    CYHAL_TRIGGER_TR_GROUP2_INPUT11 = 177,
    CYHAL_TRIGGER_TR_GROUP2_INPUT12 = 178,
    CYHAL_TRIGGER_TR_GROUP2_INPUT13 = 179,
    CYHAL_TRIGGER_TR_GROUP2_INPUT14 = 180,
    CYHAL_TRIGGER_TR_GROUP2_INPUT15 = 181,
    CYHAL_TRIGGER_TR_GROUP2_INPUT16 = 182,
    CYHAL_TRIGGER_TR_GROUP2_INPUT17 = 183,
    CYHAL_TRIGGER_TR_GROUP2_INPUT18 = 184,
    CYHAL_TRIGGER_TR_GROUP2_INPUT19 = 185,
    CYHAL_TRIGGER_TR_GROUP2_INPUT20 = 186,
    CYHAL_TRIGGER_TR_GROUP2_INPUT21 = 187,
    CYHAL_TRIGGER_TR_GROUP2_INPUT22 = 188,
    CYHAL_TRIGGER_TR_GROUP2_INPUT23 = 189,
    CYHAL_TRIGGER_TR_GROUP2_INPUT24 = 190,
    CYHAL_TRIGGER_TR_GROUP2_INPUT25 = 191,
    CYHAL_TRIGGER_TR_GROUP2_INPUT26 = 192,
    CYHAL_TRIGGER_TR_GROUP2_INPUT27 = 193,
    CYHAL_TRIGGER_TR_GROUP2_INPUT28 = 194,
    CYHAL_TRIGGER_TR_GROUP2_INPUT29 = 195,
    CYHAL_TRIGGER_TR_GROUP2_INPUT30 = 196,
    CYHAL_TRIGGER_TR_GROUP2_INPUT31 = 197,
    CYHAL_TRIGGER_TR_GROUP2_INPUT32 = 198,
    CYHAL_TRIGGER_TR_GROUP2_INPUT33 = 199,
    CYHAL_TRIGGER_TR_GROUP2_INPUT34 = 200,
    CYHAL_TRIGGER_TR_GROUP2_INPUT35 = 201,
    CYHAL_TRIGGER_TR_GROUP2_INPUT36 = 202,
    CYHAL_TRIGGER_TR_GROUP2_INPUT37 = 203,
    CYHAL_TRIGGER_TR_GROUP2_INPUT38 = 204,
    CYHAL_TRIGGER_TR_GROUP2_INPUT39 = 205,
    CYHAL_TRIGGER_TR_GROUP2_INPUT40 = 206,
    CYHAL_TRIGGER_TR_GROUP2_INPUT41 = 207,
    CYHAL_TRIGGER_TR_GROUP2_INPUT42 = 208,
    CYHAL_TRIGGER_TR_GROUP3_INPUT1 = 209,
    CYHAL_TRIGGER_TR_GROUP3_INPUT2 = 210,
    CYHAL_TRIGGER_TR_GROUP3_INPUT3 = 211,
    CYHAL_TRIGGER_TR_GROUP3_INPUT4 = 212,
    CYHAL_TRIGGER_TR_GROUP3_INPUT5 = 213,
    CYHAL_TRIGGER_TR_GROUP3_INPUT6 = 214,
    CYHAL_TRIGGER_TR_GROUP3_INPUT7 = 215,
    CYHAL_TRIGGER_TR_GROUP3_INPUT8 = 216,
    CYHAL_TRIGGER_TR_GROUP3_INPUT9 = 217,
    CYHAL_TRIGGER_TR_GROUP3_INPUT10 = 218,
    CYHAL_TRIGGER_TR_GROUP3_INPUT11 = 219,
    CYHAL_TRIGGER_TR_GROUP3_INPUT12 = 220,
    CYHAL_TRIGGER_TR_GROUP3_INPUT13 = 221,
    CYHAL_TRIGGER_TR_GROUP3_INPUT14 = 222,
    CYHAL_TRIGGER_TR_GROUP3_INPUT15 = 223,
    CYHAL_TRIGGER_TR_GROUP3_INPUT16 = 224,
    CYHAL_TRIGGER_TR_GROUP3_INPUT17 = 225,
    CYHAL_TRIGGER_TR_GROUP3_INPUT18 = 226,
    CYHAL_TRIGGER_TR_GROUP3_INPUT19 = 227,
    CYHAL_TRIGGER_TR_GROUP3_INPUT20 = 228,
    CYHAL_TRIGGER_TR_GROUP3_INPUT21 = 229,
    CYHAL_TRIGGER_TR_GROUP3_INPUT22 = 230,
    CYHAL_TRIGGER_TR_GROUP3_INPUT23 = 231,
    CYHAL_TRIGGER_TR_GROUP3_INPUT24 = 232,
    CYHAL_TRIGGER_TR_GROUP3_INPUT25 = 233,
    CYHAL_TRIGGER_TR_GROUP3_INPUT26 = 234,
    CYHAL_TRIGGER_TR_GROUP3_INPUT27 = 235,
    CYHAL_TRIGGER_TR_GROUP3_INPUT28 = 236,
    CYHAL_TRIGGER_TR_GROUP3_INPUT29 = 237,
    CYHAL_TRIGGER_TR_GROUP3_INPUT30 = 238,
    CYHAL_TRIGGER_TR_GROUP3_INPUT31 = 239,
    CYHAL_TRIGGER_TR_GROUP3_INPUT32 = 240,
    CYHAL_TRIGGER_TR_GROUP3_INPUT33 = 241,
    CYHAL_TRIGGER_TR_GROUP3_INPUT34 = 242,
    CYHAL_TRIGGER_TR_GROUP3_INPUT35 = 243,
    CYHAL_TRIGGER_TR_GROUP3_INPUT36 = 244,
    CYHAL_TRIGGER_TR_GROUP3_INPUT37 = 245,
    CYHAL_TRIGGER_TR_GROUP3_INPUT38 = 246,
    CYHAL_TRIGGER_TR_GROUP3_INPUT39 = 247,
    CYHAL_TRIGGER_TR_GROUP3_INPUT40 = 248,
    CYHAL_TRIGGER_TR_GROUP3_INPUT41 = 249,
    CYHAL_TRIGGER_TR_GROUP3_INPUT42 = 250,
    CYHAL_TRIGGER_TR_GROUP4_INPUT1 = 251,
    CYHAL_TRIGGER_TR_GROUP4_INPUT2 = 252,
    CYHAL_TRIGGER_TR_GROUP4_INPUT3 = 253,
    CYHAL_TRIGGER_TR_GROUP4_INPUT4 = 254,
    CYHAL_TRIGGER_TR_GROUP4_INPUT5 = 255,
    CYHAL_TRIGGER_TR_GROUP4_INPUT6 = 256,
    CYHAL_TRIGGER_TR_GROUP4_INPUT7 = 257,
    CYHAL_TRIGGER_TR_GROUP4_INPUT8 = 258,
    CYHAL_TRIGGER_TR_GROUP4_INPUT9 = 259,
    CYHAL_TRIGGER_TR_GROUP4_INPUT10 = 260,
    CYHAL_TRIGGER_TR_GROUP4_INPUT11 = 261,
    CYHAL_TRIGGER_TR_GROUP4_INPUT12 = 262,
    CYHAL_TRIGGER_TR_GROUP4_INPUT13 = 263,
    CYHAL_TRIGGER_TR_GROUP4_INPUT14 = 264,
    CYHAL_TRIGGER_TR_GROUP4_INPUT15 = 265,
    CYHAL_TRIGGER_TR_GROUP4_INPUT16 = 266,
    CYHAL_TRIGGER_TR_GROUP4_INPUT17 = 267,
    CYHAL_TRIGGER_TR_GROUP4_INPUT18 = 268,
    CYHAL_TRIGGER_TR_GROUP4_INPUT19 = 269,
    CYHAL_TRIGGER_TR_GROUP4_INPUT20 = 270,
    CYHAL_TRIGGER_TR_GROUP4_INPUT21 = 271,
    CYHAL_TRIGGER_TR_GROUP4_INPUT22 = 272,
    CYHAL_TRIGGER_TR_GROUP4_INPUT23 = 273,
    CYHAL_TRIGGER_TR_GROUP4_INPUT24 = 274,
    CYHAL_TRIGGER_TR_GROUP4_INPUT25 = 275,
    CYHAL_TRIGGER_TR_GROUP4_INPUT26 = 276,
    CYHAL_TRIGGER_TR_GROUP4_INPUT27 = 277,
    CYHAL_TRIGGER_TR_GROUP4_INPUT28 = 278,
    CYHAL_TRIGGER_TR_GROUP4_INPUT29 = 279,
    CYHAL_TRIGGER_TR_GROUP4_INPUT30 = 280,
    CYHAL_TRIGGER_TR_GROUP4_INPUT31 = 281,
    CYHAL_TRIGGER_TR_GROUP4_INPUT32 = 282,
    CYHAL_TRIGGER_TR_GROUP4_INPUT33 = 283,
    CYHAL_TRIGGER_TR_GROUP4_INPUT34 = 284,
    CYHAL_TRIGGER_TR_GROUP4_INPUT35 = 285,
    CYHAL_TRIGGER_TR_GROUP4_INPUT36 = 286,
    CYHAL_TRIGGER_TR_GROUP4_INPUT37 = 287,
    CYHAL_TRIGGER_TR_GROUP4_INPUT38 = 288,
    CYHAL_TRIGGER_TR_GROUP4_INPUT39 = 289,
    CYHAL_TRIGGER_TR_GROUP4_INPUT40 = 290,
    CYHAL_TRIGGER_TR_GROUP4_INPUT41 = 291,
    CYHAL_TRIGGER_TR_GROUP4_INPUT42 = 292,
    CYHAL_TRIGGER_TR_GROUP5_INPUT1 = 293,
    CYHAL_TRIGGER_TR_GROUP5_INPUT2 = 294,
    CYHAL_TRIGGER_TR_GROUP5_INPUT3 = 295,
    CYHAL_TRIGGER_TR_GROUP5_INPUT4 = 296,
    CYHAL_TRIGGER_TR_GROUP5_INPUT5 = 297,
    CYHAL_TRIGGER_TR_GROUP5_INPUT6 = 298,
    CYHAL_TRIGGER_TR_GROUP5_INPUT7 = 299,
    CYHAL_TRIGGER_TR_GROUP5_INPUT8 = 300,
    CYHAL_TRIGGER_TR_GROUP5_INPUT9 = 301,
    CYHAL_TRIGGER_TR_GROUP5_INPUT10 = 302,
    CYHAL_TRIGGER_TR_GROUP5_INPUT11 = 303,
    CYHAL_TRIGGER_TR_GROUP5_INPUT12 = 304,
    CYHAL_TRIGGER_TR_GROUP5_INPUT13 = 305,
    CYHAL_TRIGGER_TR_GROUP5_INPUT14 = 306,
    CYHAL_TRIGGER_TR_GROUP5_INPUT15 = 307,
    CYHAL_TRIGGER_TR_GROUP5_INPUT16 = 308,
    CYHAL_TRIGGER_TR_GROUP5_INPUT17 = 309,
    CYHAL_TRIGGER_TR_GROUP5_INPUT18 = 310,
    CYHAL_TRIGGER_TR_GROUP5_INPUT19 = 311,
    CYHAL_TRIGGER_TR_GROUP5_INPUT20 = 312,
    CYHAL_TRIGGER_TR_GROUP5_INPUT21 = 313,
    CYHAL_TRIGGER_TR_GROUP5_INPUT22 = 314,
    CYHAL_TRIGGER_TR_GROUP5_INPUT23 = 315,
    CYHAL_TRIGGER_TR_GROUP5_INPUT24 = 316,
    CYHAL_TRIGGER_TR_GROUP5_INPUT25 = 317,
    CYHAL_TRIGGER_TR_GROUP5_INPUT26 = 318,
    CYHAL_TRIGGER_TR_GROUP5_INPUT27 = 319,
    CYHAL_TRIGGER_TR_GROUP5_INPUT28 = 320,
    CYHAL_TRIGGER_TR_GROUP5_INPUT29 = 321,
    CYHAL_TRIGGER_TR_GROUP5_INPUT30 = 322,
    CYHAL_TRIGGER_TR_GROUP5_INPUT31 = 323,
    CYHAL_TRIGGER_TR_GROUP5_INPUT32 = 324,
    CYHAL_TRIGGER_TR_GROUP5_INPUT33 = 325,
    CYHAL_TRIGGER_TR_GROUP5_INPUT34 = 326,
    CYHAL_TRIGGER_TR_GROUP5_INPUT35 = 327,
    CYHAL_TRIGGER_TR_GROUP5_INPUT36 = 328,
    CYHAL_TRIGGER_TR_GROUP5_INPUT37 = 329,
    CYHAL_TRIGGER_TR_GROUP5_INPUT38 = 330,
    CYHAL_TRIGGER_TR_GROUP5_INPUT39 = 331,
    CYHAL_TRIGGER_TR_GROUP5_INPUT40 = 332,
    CYHAL_TRIGGER_TR_GROUP5_INPUT41 = 333,
    CYHAL_TRIGGER_TR_GROUP5_INPUT42 = 334,
    CYHAL_TRIGGER_TR_GROUP6_INPUT1 = 335,
    CYHAL_TRIGGER_TR_GROUP6_INPUT2 = 336,
    CYHAL_TRIGGER_TR_GROUP6_INPUT3 = 337,
    CYHAL_TRIGGER_TR_GROUP6_INPUT4 = 338,
    CYHAL_TRIGGER_TR_GROUP6_INPUT5 = 339,
    CYHAL_TRIGGER_TR_GROUP6_INPUT6 = 340,
    CYHAL_TRIGGER_TR_GROUP6_INPUT7 = 341,
    CYHAL_TRIGGER_TR_GROUP6_INPUT8 = 342,
    CYHAL_TRIGGER_TR_GROUP6_INPUT9 = 343,
    CYHAL_TRIGGER_TR_GROUP6_INPUT10 = 344,
    CYHAL_TRIGGER_TR_GROUP6_INPUT11 = 345,
    CYHAL_TRIGGER_TR_GROUP6_INPUT12 = 346,
    CYHAL_TRIGGER_TR_GROUP6_INPUT13 = 347,
    CYHAL_TRIGGER_TR_GROUP6_INPUT14 = 348,
    CYHAL_TRIGGER_TR_GROUP6_INPUT15 = 349,
    CYHAL_TRIGGER_TR_GROUP6_INPUT16 = 350,
    CYHAL_TRIGGER_TR_GROUP6_INPUT17 = 351,
    CYHAL_TRIGGER_TR_GROUP6_INPUT18 = 352,
    CYHAL_TRIGGER_TR_GROUP6_INPUT19 = 353,
    CYHAL_TRIGGER_TR_GROUP6_INPUT20 = 354,
    CYHAL_TRIGGER_TR_GROUP6_INPUT21 = 355,
    CYHAL_TRIGGER_TR_GROUP6_INPUT22 = 356,
    CYHAL_TRIGGER_TR_GROUP6_INPUT23 = 357,
    CYHAL_TRIGGER_TR_GROUP6_INPUT24 = 358,
    CYHAL_TRIGGER_TR_GROUP6_INPUT25 = 359,
    CYHAL_TRIGGER_TR_GROUP6_INPUT26 = 360,
    CYHAL_TRIGGER_TR_GROUP6_INPUT27 = 361,
    CYHAL_TRIGGER_TR_GROUP6_INPUT28 = 362,
    CYHAL_TRIGGER_TR_GROUP6_INPUT29 = 363,
    CYHAL_TRIGGER_TR_GROUP6_INPUT30 = 364,
    CYHAL_TRIGGER_TR_GROUP6_INPUT31 = 365,
    CYHAL_TRIGGER_TR_GROUP6_INPUT32 = 366,
    CYHAL_TRIGGER_TR_GROUP6_INPUT33 = 367,
    CYHAL_TRIGGER_TR_GROUP6_INPUT34 = 368,
    CYHAL_TRIGGER_TR_GROUP6_INPUT35 = 369,
    CYHAL_TRIGGER_TR_GROUP6_INPUT36 = 370,
    CYHAL_TRIGGER_TR_GROUP6_INPUT37 = 371,
    CYHAL_TRIGGER_TR_GROUP6_INPUT38 = 372,
    CYHAL_TRIGGER_TR_GROUP6_INPUT39 = 373,
    CYHAL_TRIGGER_TR_GROUP6_INPUT40 = 374,
    CYHAL_TRIGGER_TR_GROUP6_INPUT41 = 375,
    CYHAL_TRIGGER_TR_GROUP6_INPUT42 = 376,
    CYHAL_TRIGGER_TR_GROUP7_INPUT1 = 377,
    CYHAL_TRIGGER_TR_GROUP7_INPUT2 = 378,
    CYHAL_TRIGGER_TR_GROUP7_INPUT3 = 379,
    CYHAL_TRIGGER_TR_GROUP7_INPUT4 = 380,
    CYHAL_TRIGGER_TR_GROUP7_INPUT5 = 381,
    CYHAL_TRIGGER_TR_GROUP7_INPUT6 = 382,
    CYHAL_TRIGGER_TR_GROUP7_INPUT7 = 383,
    CYHAL_TRIGGER_TR_GROUP7_INPUT8 = 384,
    CYHAL_TRIGGER_TR_GROUP7_INPUT9 = 385,
    CYHAL_TRIGGER_TR_GROUP7_INPUT10 = 386,
    CYHAL_TRIGGER_TR_GROUP7_INPUT11 = 387,
    CYHAL_TRIGGER_TR_GROUP7_INPUT12 = 388,
    CYHAL_TRIGGER_TR_GROUP7_INPUT13 = 389,
    CYHAL_TRIGGER_TR_GROUP7_INPUT14 = 390,
    CYHAL_TRIGGER_TR_GROUP7_INPUT15 = 391,
    CYHAL_TRIGGER_TR_GROUP7_INPUT16 = 392,
    CYHAL_TRIGGER_TR_GROUP7_INPUT17 = 393,
    CYHAL_TRIGGER_TR_GROUP7_INPUT18 = 394,
    CYHAL_TRIGGER_TR_GROUP7_INPUT19 = 395,
    CYHAL_TRIGGER_TR_GROUP7_INPUT20 = 396,
    CYHAL_TRIGGER_TR_GROUP7_INPUT21 = 397,
    CYHAL_TRIGGER_TR_GROUP7_INPUT22 = 398,
    CYHAL_TRIGGER_TR_GROUP7_INPUT23 = 399,
    CYHAL_TRIGGER_TR_GROUP7_INPUT24 = 400,
    CYHAL_TRIGGER_TR_GROUP7_INPUT25 = 401,
    CYHAL_TRIGGER_TR_GROUP7_INPUT26 = 402,
    CYHAL_TRIGGER_TR_GROUP7_INPUT27 = 403,
    CYHAL_TRIGGER_TR_GROUP7_INPUT28 = 404,
    CYHAL_TRIGGER_TR_GROUP7_INPUT29 = 405,
    CYHAL_TRIGGER_TR_GROUP7_INPUT30 = 406,
    CYHAL_TRIGGER_TR_GROUP7_INPUT31 = 407,
    CYHAL_TRIGGER_TR_GROUP7_INPUT32 = 408,
    CYHAL_TRIGGER_TR_GROUP7_INPUT33 = 409,
    CYHAL_TRIGGER_TR_GROUP7_INPUT34 = 410,
    CYHAL_TRIGGER_TR_GROUP7_INPUT35 = 411,
    CYHAL_TRIGGER_TR_GROUP7_INPUT36 = 412,
    CYHAL_TRIGGER_TR_GROUP7_INPUT37 = 413,
    CYHAL_TRIGGER_TR_GROUP7_INPUT38 = 414,
    CYHAL_TRIGGER_TR_GROUP7_INPUT39 = 415,
    CYHAL_TRIGGER_TR_GROUP7_INPUT40 = 416,
    CYHAL_TRIGGER_TR_GROUP7_INPUT41 = 417,
    CYHAL_TRIGGER_TR_GROUP7_INPUT42 = 418,
    CYHAL_TRIGGER_TR_GROUP8_INPUT1 = 419,
    CYHAL_TRIGGER_TR_GROUP8_INPUT2 = 420,
    CYHAL_TRIGGER_TR_GROUP8_INPUT3 = 421,
    CYHAL_TRIGGER_TR_GROUP8_INPUT4 = 422,
    CYHAL_TRIGGER_TR_GROUP8_INPUT5 = 423,
    CYHAL_TRIGGER_TR_GROUP8_INPUT6 = 424,
    CYHAL_TRIGGER_TR_GROUP8_INPUT7 = 425,
    CYHAL_TRIGGER_TR_GROUP8_INPUT8 = 426,
    CYHAL_TRIGGER_TR_GROUP8_INPUT9 = 427,
    CYHAL_TRIGGER_TR_GROUP8_INPUT10 = 428,
    CYHAL_TRIGGER_TR_GROUP8_INPUT11 = 429,
    CYHAL_TRIGGER_TR_GROUP8_INPUT12 = 430,
    CYHAL_TRIGGER_TR_GROUP8_INPUT13 = 431,
    CYHAL_TRIGGER_TR_GROUP8_INPUT14 = 432,
    CYHAL_TRIGGER_TR_GROUP8_INPUT15 = 433,
    CYHAL_TRIGGER_TR_GROUP8_INPUT16 = 434,
    CYHAL_TRIGGER_TR_GROUP8_INPUT17 = 435,
    CYHAL_TRIGGER_TR_GROUP8_INPUT18 = 436,
    CYHAL_TRIGGER_TR_GROUP8_INPUT19 = 437,
    CYHAL_TRIGGER_TR_GROUP8_INPUT20 = 438,
    CYHAL_TRIGGER_TR_GROUP8_INPUT21 = 439,
    CYHAL_TRIGGER_TR_GROUP8_INPUT22 = 440,
    CYHAL_TRIGGER_TR_GROUP8_INPUT23 = 441,
    CYHAL_TRIGGER_TR_GROUP8_INPUT24 = 442,
    CYHAL_TRIGGER_TR_GROUP8_INPUT25 = 443,
    CYHAL_TRIGGER_TR_GROUP8_INPUT26 = 444,
    CYHAL_TRIGGER_TR_GROUP8_INPUT27 = 445,
    CYHAL_TRIGGER_TR_GROUP8_INPUT28 = 446,
    CYHAL_TRIGGER_TR_GROUP8_INPUT29 = 447,
    CYHAL_TRIGGER_TR_GROUP8_INPUT30 = 448,
    CYHAL_TRIGGER_TR_GROUP8_INPUT31 = 449,
    CYHAL_TRIGGER_TR_GROUP8_INPUT32 = 450,
    CYHAL_TRIGGER_TR_GROUP8_INPUT33 = 451,
    CYHAL_TRIGGER_TR_GROUP8_INPUT34 = 452,
    CYHAL_TRIGGER_TR_GROUP8_INPUT35 = 453,
    CYHAL_TRIGGER_TR_GROUP8_INPUT36 = 454,
    CYHAL_TRIGGER_TR_GROUP8_INPUT37 = 455,
    CYHAL_TRIGGER_TR_GROUP8_INPUT38 = 456,
    CYHAL_TRIGGER_TR_GROUP8_INPUT39 = 457,
    CYHAL_TRIGGER_TR_GROUP8_INPUT40 = 458,
    CYHAL_TRIGGER_TR_GROUP8_INPUT41 = 459,
    CYHAL_TRIGGER_TR_GROUP8_INPUT42 = 460,
    CYHAL_TRIGGER_UDB_TR_DW_ACK0 = 461,
    CYHAL_TRIGGER_UDB_TR_DW_ACK1 = 462,
    CYHAL_TRIGGER_UDB_TR_DW_ACK2 = 463,
    CYHAL_TRIGGER_UDB_TR_DW_ACK3 = 464,
    CYHAL_TRIGGER_UDB_TR_DW_ACK4 = 465,
    CYHAL_TRIGGER_UDB_TR_DW_ACK5 = 466,
    CYHAL_TRIGGER_UDB_TR_DW_ACK6 = 467,
    CYHAL_TRIGGER_UDB_TR_DW_ACK7 = 468,
    CYHAL_TRIGGER_UDB_TR_IN0 = 469,
    CYHAL_TRIGGER_UDB_TR_IN1 = 470,
    CYHAL_TRIGGER_USB_DMA_BURSTEND0 = 471,
    CYHAL_TRIGGER_USB_DMA_BURSTEND1 = 472,
    CYHAL_TRIGGER_USB_DMA_BURSTEND2 = 473,
    CYHAL_TRIGGER_USB_DMA_BURSTEND3 = 474,
    CYHAL_TRIGGER_USB_DMA_BURSTEND4 = 475,
    CYHAL_TRIGGER_USB_DMA_BURSTEND5 = 476,
    CYHAL_TRIGGER_USB_DMA_BURSTEND6 = 477,
    CYHAL_TRIGGER_USB_DMA_BURSTEND7 = 478,
} cyhal_trigger_dest_psoc6_01_t;
typedef cyhal_trigger_dest_psoc6_01_t cyhal_dest_t;
extern const uint16_t cyhal_sources_per_mux[15];
extern const _Bool cyhal_is_mux_1to1[15];
extern const _cyhal_trigger_source_psoc6_01_t* cyhal_mux_to_sources [15];
extern const uint8_t cyhal_dest_to_mux[479];
extern const uint8_t cyhal_mux_dest_index[479];
typedef struct {
    cy_israddress callback;
    void* callback_arg;
} cyhal_event_callback_data_t;
typedef struct {
    union
    {
        void *v;
        uint8_t *u8;
        uint16_t *u16;
        uint32_t *u32;
    } addr;
    uint32_t size;
} _cyhal_buffer_info_t;
typedef struct {
    _Bool owned_by_configurator;
    _Bool presleep_state;
    TCPWM_Type* base;
    cyhal_resource_inst_t resource;
    cyhal_clock_t clock;
    _Bool dedicated_clock;
    uint32_t clock_hz;
    cyhal_event_callback_data_t callback_data;
    uint32_t clear_intr_mask;
    cyhal_source_t inputs[5];
} cyhal_tcpwm_t;
typedef struct {
    cyhal_resource_inst_t resource;
    union
    {
        cy_stc_dma_channel_config_t dw;
    } channel_config;
    union
    {
        cy_stc_dma_descriptor_config_t dw;
    } descriptor_config;
    union
    {
        cy_stc_dma_descriptor_t dw;
    } descriptor;
    uint16_t expected_bursts;
    uint32_t direction;
    uint32_t irq_cause;
    cyhal_event_callback_data_t callback_data;
    cyhal_source_t source;
    _Bool owned_by_configurator;
} cyhal_dma_t;
typedef struct
{
    const cyhal_resource_inst_t* resource;
    struct
    {
        union
        {
            cy_stc_dma_channel_config_t const* dw_channel_config;
        };
        union
        {
            cy_stc_dma_descriptor_config_t const* dw_descriptor_config;
        };
    };
} cyhal_dma_configurator_t;
struct _cyhal_audioss_s;
typedef struct
{
    uint32_t (*convert_interrupt_cause)(uint32_t pdl_event);
    uint32_t (*convert_to_pdl)(uint32_t hal_event);
    void (*invoke_user_callback)(struct _cyhal_audioss_s* obj, uint32_t hal_event);
    uint32_t event_mask_empty;
    uint32_t event_mask_half_empty;
    uint32_t event_mask_full;
    uint32_t event_mask_half_full;
    uint32_t event_rx_complete;
    uint32_t event_tx_complete;
    cy_rslt_t err_invalid_pin;
    cy_rslt_t err_invalid_arg;
    cy_rslt_t err_clock;
    cy_rslt_t err_not_supported;
} _cyhal_audioss_interface_t;
typedef struct _cyhal_audioss_s {
    _Bool owned_by_configurator;
    I2S_Type *base;
    cyhal_resource_inst_t resource;
    cyhal_gpio_t pin_tx_sck;
    cyhal_gpio_t pin_tx_ws;
    cyhal_gpio_t pin_tx_sdo;
    cyhal_gpio_t pin_rx_sck;
    cyhal_gpio_t pin_rx_mclk;
    cyhal_gpio_t pin_rx_ws;
    cyhal_gpio_t pin_rx_sdi;
    cyhal_gpio_t pin_tx_mclk;
    uint8_t user_fifo_level_rx;
    uint32_t mclk_hz_rx;
    uint8_t channel_length_rx;
    uint8_t word_length_rx;
    uint32_t mclk_hz_tx;
    uint8_t channel_length_tx;
    uint8_t word_length_tx;
    cyhal_clock_t clock;
    _Bool is_clock_owned;
    uint16_t user_enabled_events;
    cyhal_event_callback_data_t callback_data;
    cyhal_async_mode_t async_mode;
    uint8_t async_dma_priority;
    cyhal_dma_t tx_dma;
    cyhal_dma_t rx_dma;
    volatile const void *async_tx_buff;
    volatile size_t async_tx_length;
    volatile void *async_rx_buff;
    volatile size_t async_rx_length;
    volatile _Bool pm_transition_ready;
    cyhal_syspm_callback_data_t pm_callback;
    const _cyhal_audioss_interface_t *interface;
} _cyhal_audioss_t;
typedef struct
{
    const cyhal_resource_inst_t* resource;
    const cy_stc_i2s_config_t* config;
    const cyhal_clock_t * clock;
    uint32_t mclk_hz_rx;
    uint32_t mclk_hz_tx;
} _cyhal_audioss_configurator_t;
struct _cyhal_adc_channel_s;
typedef struct {
    _Bool owned_by_configurator;
    SAR_Type* base;
    struct _cyhal_adc_channel_s* channel_config[(16u)];
    cyhal_resource_inst_t resource;
    cyhal_clock_t clock;
    _Bool dedicated_clock;
    volatile _Bool conversion_complete;
    _Bool stop_after_scan;
    uint8_t user_enabled_events;
    cyhal_event_callback_data_t callback_data;
    int32_t *async_buff_next;
    _Bool async_transfer_in_uv;
    size_t async_scans_remaining;
    _Bool continuous_scanning;
    cyhal_async_mode_t async_mode;
    cyhal_dma_t dma;
    cyhal_source_t source;
    int32_t *async_buff_orig;
} cyhal_adc_t;
typedef struct
{
    const cyhal_resource_inst_t* resource;
    cy_stc_sar_config_t const* config;
    const cyhal_clock_t * clock;
    uint8_t num_channels;
    const uint32_t* achieved_acquisition_time;
} cyhal_adc_configurator_t;
typedef struct _cyhal_adc_channel_s {
    cyhal_adc_t* adc;
    cyhal_gpio_t vplus;
    uint8_t channel_idx;
    cyhal_gpio_t vminus;
    uint32_t minimum_acquisition_ns;
} cyhal_adc_channel_t;
typedef struct {
    _Bool owned_by_configurator;
    cyhal_resource_inst_t resource;
    union
    {
        CTBM_Type *base_ctb;
        LPCOMP_Type *base_lpcomp;
    };
    cyhal_gpio_t pin_vin_p;
    cyhal_gpio_t pin_vin_m;
    cyhal_gpio_t pin_out;
    cyhal_event_callback_data_t callback_data;
    uint32_t irq_cause;
} cyhal_comp_t;
typedef struct
{
    const cyhal_resource_inst_t* resource;
    union
    {
        const cy_stc_lpcomp_config_t *lpcomp;
        const cy_stc_ctb_opamp_config_t *opamp;
    };
} cyhal_comp_configurator_t;
typedef struct {
    CRYPTO_Type* base;
    cyhal_resource_inst_t resource;
    uint32_t crc_width;
} cyhal_crc_t;
typedef struct {
    _Bool owned_by_configurator;
    CTDAC_Type* base_dac;
    CTBM_Type* base_opamp;
    cyhal_resource_inst_t resource_dac;
    cyhal_resource_inst_t resource_opamp;
    cyhal_resource_inst_t resource_aref_opamp;
    cyhal_gpio_t pin;
} cyhal_dac_t;
typedef struct
{
    const cyhal_resource_inst_t* resource;
    const cy_stc_ctdac_config_t* config;
} cyhal_dac_configurator_t;
typedef struct {
    _Bool owned_by_configurator;
    CTBM_Type* base;
    cyhal_resource_inst_t resource;
    cyhal_gpio_t pin_vin_p;
    cyhal_gpio_t pin_vin_m;
    cyhal_gpio_t pin_vout;
    _Bool is_init_success;
} cyhal_opamp_t;
typedef struct
{
    const cyhal_resource_inst_t* resource;
    const cy_stc_ctb_opamp_config_t* config;
} cyhal_opamp_configurator_t;
typedef struct {
    void *empty;
} cyhal_nvm_t;
typedef struct {
    CySCB_Type* base;
    cyhal_resource_inst_t resource;
    cyhal_gpio_t pin_sda;
    cyhal_gpio_t pin_scl;
    cyhal_clock_t clock;
    _Bool is_clock_owned;
    cy_stc_scb_i2c_context_t context;
    cy_stc_scb_i2c_master_xfer_config_t rx_config;
    cy_stc_scb_i2c_master_xfer_config_t tx_config;
    uint32_t irq_cause;
    uint8_t addr_irq_cause;
    uint16_t pending;
    _Bool op_in_callback;
    _cyhal_buffer_info_t rx_slave_buff;
    _cyhal_buffer_info_t tx_slave_buff;
    cyhal_event_callback_data_t callback_data;
    cyhal_event_callback_data_t addr_callback_data;
    _Bool dc_configured;
} cyhal_i2c_t;
typedef struct {
    const cyhal_resource_inst_t* resource;
    const cy_stc_scb_i2c_config_t* config;
    const cyhal_clock_t* clock;
} cyhal_i2c_configurator_t;
typedef struct {
    CySCB_Type* base;
    cyhal_resource_inst_t resource;
    cyhal_gpio_t pin_sda;
    cyhal_gpio_t pin_scl;
    cyhal_clock_t clock;
    _Bool is_clock_owned;
    cy_stc_scb_ezi2c_context_t context;
    uint32_t irq_cause;
    cyhal_event_callback_data_t callback_data;
    _Bool two_addresses;
    _Bool dc_configured;
} cyhal_ezi2c_t;
typedef struct {
    const cyhal_resource_inst_t* resource;
    const cy_stc_scb_ezi2c_config_t* config;
    const cyhal_clock_t* clock;
} cyhal_ezi2c_configurator_t;
typedef _cyhal_audioss_t cyhal_i2s_t;
typedef _cyhal_audioss_configurator_t cyhal_i2s_configurator_t;
typedef struct cyhal_ipc_s {
    _Bool sema_preemptable;
    uint32_t sema_number;
    _Bool sema_taken;
    struct cyhal_ipc_queue_s* queue_obj;
    uint16_t user_events;
    uint32_t processed_events;
    cyhal_event_callback_data_t callback_data;
    struct cyhal_ipc_s* prev_object;
} cyhal_ipc_t;
typedef struct {
    void *empty;
} cyhal_keyscan_t;
typedef struct {
    void *empty;
} cyhal_keyscan_configurator_t;
typedef struct {
    MCWDT_STRUCT_Type *base;
    cyhal_resource_inst_t resource;
    cyhal_event_callback_data_t callback_data;
    _Bool clear_int_mask;
    uint8_t isr_instruction;
} cyhal_lptimer_t;
typedef struct {
    _Bool owned_by_configurator;
    PDM_Type *base;
    cyhal_resource_inst_t resource;
    cyhal_gpio_t pin_data;
    cyhal_gpio_t pin_clk;
    cyhal_clock_t clock;
    _Bool is_clock_owned;
    uint8_t user_trigger_level;
    uint32_t irq_cause;
    cyhal_event_callback_data_t callback_data;
    uint8_t word_size;
    cyhal_dma_t dma;
    volatile _Bool stabilized;
    volatile _Bool pm_transition_ready;
    cyhal_syspm_callback_data_t pm_callback;
    void *async_buffer;
    size_t async_read_remaining;
} cyhal_pdm_pcm_t;
typedef struct {
    const cyhal_resource_inst_t* resource;
    const cy_stc_pdm_pcm_config_t* config;
    const cyhal_clock_t* clock;
} cyhal_pdm_pcm_configurator_t;
typedef struct {
    cyhal_tcpwm_t tcpwm;
    cyhal_gpio_t pin;
    cyhal_gpio_t pin_compl;
    _Bool dead_time_set;
} cyhal_pwm_t;
typedef struct
{
    const cyhal_resource_inst_t* resource;
    cy_stc_tcpwm_pwm_config_t const* config;
    const cyhal_clock_t * clock;
} cyhal_pwm_configurator_t;
typedef struct {
    void *empty;
} cyhal_qspi_t;
typedef struct {
    void *empty;
} cyhal_qspi_configurator_t;
typedef struct {
    cyhal_tcpwm_t tcpwm;
    cyhal_gpio_t phi_a;
    cyhal_gpio_t phi_b;
    cyhal_gpio_t index;
    uint32_t last_counter_value;
} cyhal_quaddec_t;
typedef struct
{
    const cyhal_resource_inst_t* resource;
    const cy_stc_tcpwm_quaddec_config_t* config;
    const cyhal_clock_t * clock;
} cyhal_quaddec_configurator_t;
typedef struct {
    CRYPTO_Type* base;
    cyhal_resource_inst_t resource;
} cyhal_trng_t;
typedef struct {
    cy_stc_rtc_dst_t dst;
} cyhal_rtc_t;
typedef struct
{
    const cyhal_resource_inst_t* resource;
    cy_stc_rtc_config_t const* config;
    cy_stc_rtc_dst_t const* dst_config;
} cyhal_rtc_configurator_t;
typedef struct {
    void *empty;
} cyhal_sdhc_t;
typedef struct {
    void *empty;
} cyhal_sdhc_configurator_t;
typedef struct {
    void *empty;
} cyhal_sdio_t;
typedef struct {
    void *empty;
} cyhal_sdio_configurator_t;
typedef struct {
    CySCB_Type* base;
    cyhal_resource_inst_t resource;
    cyhal_gpio_t pin_miso;
    cyhal_gpio_t pin_mosi;
    cyhal_gpio_t pin_sclk;
    cyhal_gpio_t pin_ssel[4];
    cy_en_scb_spi_polarity_t ssel_pol[4];
    uint8_t active_ssel;
    cyhal_clock_t clock;
    cy_en_scb_spi_sclk_mode_t clk_mode;
    uint8_t mode;
    uint8_t data_bits;
    _Bool is_slave;
    _Bool alloc_clock;
    uint8_t oversample_value;
    _Bool msb_first;
    cy_stc_scb_spi_context_t context;
    uint32_t irq_cause;
    uint16_t volatile pending;
    _Bool op_in_callback;
    uint8_t write_fill;
    void *rx_buffer;
    uint32_t rx_buffer_size;
    const void *tx_buffer;
    uint32_t tx_buffer_size;
    _Bool is_async;
    cyhal_event_callback_data_t callback_data;
    _Bool dc_configured;
} cyhal_spi_t;
typedef struct {
    const cyhal_resource_inst_t* resource;
    const cy_stc_scb_spi_config_t* config;
    const cyhal_clock_t* clock;
    struct
    {
        cyhal_gpio_t sclk;
        cyhal_gpio_t ssel[4];
        cyhal_gpio_t mosi;
        cyhal_gpio_t miso;
    } gpios;
} cyhal_spi_configurator_t;
typedef _cyhal_audioss_t cyhal_tdm_t;
typedef _cyhal_audioss_configurator_t cyhal_tdm_configurator_t;
typedef struct {
    cyhal_tcpwm_t tcpwm;
    uint32_t default_value;
} cyhal_timer_t;
typedef struct
{
    const cyhal_resource_inst_t* resource;
    const cy_stc_tcpwm_counter_config_t* config;
    const cyhal_clock_t * clock;
} cyhal_timer_configurator_t;
typedef struct {
    CySCB_Type* base;
    cyhal_resource_inst_t resource;
    cyhal_gpio_t pin_rx;
    cyhal_gpio_t pin_tx;
    cyhal_gpio_t pin_cts;
    cyhal_gpio_t pin_rts;
    _Bool cts_enabled;
    _Bool rts_enabled;
    _Bool is_clock_owned;
    cyhal_clock_t clock;
    cy_stc_scb_uart_context_t context;
    cy_stc_scb_uart_config_t config;
    uint32_t irq_cause;
    en_hsiom_sel_t saved_tx_hsiom;
    en_hsiom_sel_t saved_rts_hsiom;
    cyhal_event_callback_data_t callback_data;
    _Bool dc_configured;
    uint32_t baud_rate;
    cyhal_async_mode_t async_mode;
    cyhal_dma_t dma_tx;
    cyhal_dma_t dma_rx;
    volatile uint32_t async_tx_length;
    volatile uint32_t async_rx_length;
    volatile void *async_tx_buff;
    volatile void *async_rx_buff;
    uint32_t user_fifo_level;
} cyhal_uart_t;
typedef struct {
    const cyhal_resource_inst_t* resource;
    const cy_stc_scb_uart_config_t* config;
    const cyhal_clock_t* clock;
    struct
    {
        cyhal_gpio_t pin_tx;
        cyhal_gpio_t pin_rts;
        cyhal_gpio_t pin_cts;
    } gpios;
} cyhal_uart_configurator_t;
typedef struct {
    void *empty;
} cyhal_usb_dev_t;
typedef struct {
    uint8_t placeholder;
} cyhal_wdt_t;
typedef enum {
    CYHAL_SPI_IRQ_DATA_IN_FIFO = 1 << 1,
    CYHAL_SPI_IRQ_DONE = 1 << 2,
    CYHAL_SPI_IRQ_ERROR = 1 << 3,
} cyhal_spi_event_t;
typedef enum {
    CYHAL_SPI_SSEL_ACTIVE_LOW = 0,
    CYHAL_SPI_SSEL_ACTIVE_HIGH = 1,
} cyhal_spi_ssel_polarity_t;
typedef void (*cyhal_spi_event_callback_t)(void *callback_arg, cyhal_spi_event_t event);
typedef enum
{
    CYHAL_SPI_MODE_00_MSB = ((((0) > 0) ? (0x04u) : 0) | (((0) > 0) ? (0x02u) : 0) | (((0) > 0) ? (0x01u) : 0)),
    CYHAL_SPI_MODE_00_LSB = ((((0) > 0) ? (0x04u) : 0) | (((0) > 0) ? (0x02u) : 0) | (((1) > 0) ? (0x01u) : 0)),
    CYHAL_SPI_MODE_01_MSB = ((((0) > 0) ? (0x04u) : 0) | (((1) > 0) ? (0x02u) : 0) | (((0) > 0) ? (0x01u) : 0)),
    CYHAL_SPI_MODE_01_LSB = ((((0) > 0) ? (0x04u) : 0) | (((1) > 0) ? (0x02u) : 0) | (((1) > 0) ? (0x01u) : 0)),
    CYHAL_SPI_MODE_10_MSB = ((((1) > 0) ? (0x04u) : 0) | (((0) > 0) ? (0x02u) : 0) | (((0) > 0) ? (0x01u) : 0)),
    CYHAL_SPI_MODE_10_LSB = ((((1) > 0) ? (0x04u) : 0) | (((0) > 0) ? (0x02u) : 0) | (((1) > 0) ? (0x01u) : 0)),
    CYHAL_SPI_MODE_11_MSB = ((((1) > 0) ? (0x04u) : 0) | (((1) > 0) ? (0x02u) : 0) | (((0) > 0) ? (0x01u) : 0)),
    CYHAL_SPI_MODE_11_LSB = ((((1) > 0) ? (0x04u) : 0) | (((1) > 0) ? (0x02u) : 0) | (((1) > 0) ? (0x01u) : 0)),
} cyhal_spi_mode_t;
typedef enum
{
    CYHAL_SPI_FIFO_RX,
    CYHAL_SPI_FIFO_TX,
} cyhal_spi_fifo_type_t;
typedef enum
{
    CYHAL_SPI_OUTPUT_TRIGGER_RX_FIFO_LEVEL_REACHED,
    CYHAL_SPI_OUTPUT_TRIGGER_TX_FIFO_LEVEL_REACHED,
} cyhal_spi_output_t;
typedef struct
{
    cyhal_spi_mode_t mode;
    uint8_t data_bits;
    _Bool is_slave;
} cyhal_spi_cfg_t;
cy_rslt_t cyhal_spi_init(cyhal_spi_t *obj, cyhal_gpio_t mosi, cyhal_gpio_t miso, cyhal_gpio_t sclk, cyhal_gpio_t ssel,
                         const cyhal_clock_t *clk, uint8_t bits, cyhal_spi_mode_t mode, _Bool is_slave);
void cyhal_spi_free(cyhal_spi_t *obj);
cy_rslt_t cyhal_spi_set_frequency(cyhal_spi_t *obj, uint32_t hz);
cy_rslt_t cyhal_spi_slave_select_config(cyhal_spi_t *obj, cyhal_gpio_t ssel, cyhal_spi_ssel_polarity_t polarity);
cy_rslt_t cyhal_spi_select_active_ssel(cyhal_spi_t *obj, cyhal_gpio_t ssel);
cy_rslt_t cyhal_spi_recv(cyhal_spi_t *obj, uint32_t* value);
cy_rslt_t cyhal_spi_send(cyhal_spi_t *obj, uint32_t value);
cy_rslt_t cyhal_spi_slave_read(cyhal_spi_t *obj, uint8_t *dst_buff, uint16_t *size, uint32_t timeout);
cy_rslt_t cyhal_spi_slave_write(cyhal_spi_t *obj, const uint8_t *src_buff, uint16_t *size, uint32_t timeout);
uint32_t cyhal_spi_readable(cyhal_spi_t *obj);
uint32_t cyhal_spi_writable(cyhal_spi_t *obj);
cy_rslt_t cyhal_spi_transfer(cyhal_spi_t *obj, const uint8_t *tx, size_t tx_length, uint8_t *rx, size_t rx_length, uint8_t write_fill);
cy_rslt_t cyhal_spi_transfer_async(cyhal_spi_t *obj, const uint8_t *tx, size_t tx_length, uint8_t *rx, size_t rx_length);
_Bool cyhal_spi_is_busy(cyhal_spi_t *obj);
cy_rslt_t cyhal_spi_abort_async(cyhal_spi_t *obj);
void cyhal_spi_register_callback(cyhal_spi_t *obj, cyhal_spi_event_callback_t callback, void *callback_arg);
void cyhal_spi_enable_event(cyhal_spi_t *obj, cyhal_spi_event_t event, uint8_t intr_priority, _Bool enable);
cy_rslt_t cyhal_spi_set_fifo_level(cyhal_spi_t *obj, cyhal_spi_fifo_type_t type, uint16_t level);
cy_rslt_t cyhal_spi_enable_output(cyhal_spi_t *obj, cyhal_spi_output_t output, cyhal_source_t *source);
cy_rslt_t cyhal_spi_disable_output(cyhal_spi_t *obj, cyhal_spi_output_t output);
cy_rslt_t cyhal_spi_init_cfg(cyhal_spi_t *obj, const cyhal_spi_configurator_t *cfg);
cy_rslt_t cyhal_spi_clear(cyhal_spi_t *obj);
extern void __VERIFIER_assume(int assumption);
extern void __VERIFIER_error(void);
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);
extern _Bool __VERIFIER_nondet_bool(void);
extern _Bool __VERIFIER_nondet__Bool(void);
extern char __VERIFIER_nondet_char(void);
extern unsigned char __VERIFIER_nondet_uchar(void);
extern char* __VERIFIER_nondet_pchar(void);
extern short __VERIFIER_nondet_short(void);
extern unsigned short __VERIFIER_nondet_ushort(void);
extern unsigned __VERIFIER_nondet_unsigned(void);
extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern size_t __VERIFIER_nondet_size_t(void);
extern long __VERIFIER_nondet_long(void);
extern unsigned long __VERIFIER_nondet_ulong(void);
extern long long __VERIFIER_nondet_longlong(void);
extern unsigned long long __VERIFIER_nondet_ulonglong(void);
extern float __VERIFIER_nondet_float(void);
extern double __VERIFIER_nondet_double(void);
extern void* __VERIFIER_nondet_pointer(void);
_Bool __hal_spi_initialized = 0;
_Bool __hal_spi_interrupt_registered = 0;
cy_rslt_t cyhal_spi_init(cyhal_spi_t* obj, cyhal_gpio_t mosi, cyhal_gpio_t miso, cyhal_gpio_t sclk, cyhal_gpio_t ssel,
                         const cyhal_clock_t* clk, uint8_t bits, cyhal_spi_mode_t mode, _Bool is_slave)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 0) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 21, __func__, "__hal_spi_initialized == false"));
    __hal_spi_initialized = 1;
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_spi_init_cfg(cyhal_spi_t* obj, const cyhal_spi_configurator_t* cfg)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 0) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 31, __func__, "__hal_spi_initialized == false"));
    __hal_spi_initialized = 1;
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
void cyhal_spi_free(cyhal_spi_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 41, __func__, "__hal_spi_initialized == true"));
    __hal_spi_initialized = 0;
    __hal_spi_interrupt_registered = 0;
    __VERIFIER_atomic_end();
    return;
}
cy_rslt_t cyhal_spi_set_frequency(cyhal_spi_t* obj, uint32_t hz)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 52, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_spi_select_active_ssel(cyhal_spi_t* obj, cyhal_gpio_t ssel)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 61, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_spi_slave_select_config(cyhal_spi_t* obj, cyhal_gpio_t ssel, cyhal_spi_ssel_polarity_t polarity)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 70, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_spi_recv(cyhal_spi_t* obj, uint32_t* value)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 79, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_spi_send(cyhal_spi_t* obj, uint32_t value)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 88, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_spi_slave_read(cyhal_spi_t* obj, uint8_t* dst_buff, uint16_t* size, uint32_t timeout)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 97, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_spi_slave_write(cyhal_spi_t* obj, const uint8_t* src_buff, uint16_t* size, uint32_t timeout)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 106, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_spi_transfer(cyhal_spi_t* obj, const uint8_t* tx, size_t tx_length, uint8_t* rx, size_t rx_length,
                             uint8_t write_fill)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 116, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_spi_transfer_async(cyhal_spi_t* obj, const uint8_t* tx, size_t tx_length, uint8_t* rx, size_t rx_length)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 125, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
_Bool cyhal_spi_is_busy(cyhal_spi_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 134, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_bool();
}
cy_rslt_t cyhal_spi_abort_async(cyhal_spi_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 143, __func__, "__hal_spi_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
void cyhal_spi_register_callback(cyhal_spi_t* obj, cyhal_spi_event_callback_t callback, void* callback_arg)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 152, __func__, "__hal_spi_initialized == true"));
    __hal_spi_interrupt_registered = 1;
    __VERIFIER_atomic_end();
    return;
}
void cyhal_spi_enable_event(cyhal_spi_t* obj, cyhal_spi_event_t event, uint8_t intr_priority, _Bool enable)
{
    __VERIFIER_atomic_begin();
    ((__hal_spi_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 162, __func__, "__hal_spi_initialized == true"));
    ((__hal_spi_interrupt_registered == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-spi.c", 163, __func__, "__hal_spi_interrupt_registered == true"));
    __VERIFIER_atomic_end();
    return;
}
void __assert (const char *, int, const char *)
     __attribute__ ((__noreturn__));
void __assert_func (const char *, int, const char *, const char *)
     __attribute__ ((__noreturn__));

typedef enum
{
    CYHAL_UART_PARITY_NONE,
    CYHAL_UART_PARITY_EVEN,
    CYHAL_UART_PARITY_ODD,
} cyhal_uart_parity_t;
typedef enum
{
    CYHAL_UART_IRQ_NONE = 0,
    CYHAL_UART_IRQ_TX_TRANSMIT_IN_FIFO = 1 << 1,
    CYHAL_UART_IRQ_TX_DONE = 1 << 2,
    CYHAL_UART_IRQ_TX_ERROR = 1 << 3,
    CYHAL_UART_IRQ_RX_FULL = 1 << 4,
    CYHAL_UART_IRQ_RX_DONE = 1 << 5,
    CYHAL_UART_IRQ_RX_ERROR = 1 << 6,
    CYHAL_UART_IRQ_RX_NOT_EMPTY = 1 << 7,
    CYHAL_UART_IRQ_TX_EMPTY = 1 << 8,
    CYHAL_UART_IRQ_TX_FIFO = 1 << 9,
    CYHAL_UART_IRQ_RX_FIFO = 1 << 10,
} cyhal_uart_event_t;
typedef enum
{
    CYHAL_UART_FIFO_RX,
    CYHAL_UART_FIFO_TX,
} cyhal_uart_fifo_type_t;
typedef enum
{
    CYHAL_UART_OUTPUT_TRIGGER_RX_FIFO_LEVEL_REACHED,
    CYHAL_UART_OUTPUT_TRIGGER_TX_FIFO_LEVEL_REACHED,
} cyhal_uart_output_t;
typedef struct
{
    uint32_t data_bits;
    uint32_t stop_bits;
    cyhal_uart_parity_t parity;
    uint8_t *rx_buffer;
    uint32_t rx_buffer_size;
} cyhal_uart_cfg_t;
typedef void (*cyhal_uart_event_callback_t)(void *callback_arg, cyhal_uart_event_t event);
cy_rslt_t cyhal_uart_init(cyhal_uart_t *obj, cyhal_gpio_t tx, cyhal_gpio_t rx, cyhal_gpio_t cts, cyhal_gpio_t rts, const cyhal_clock_t *clk, const cyhal_uart_cfg_t *cfg);
void cyhal_uart_free(cyhal_uart_t *obj);
cy_rslt_t cyhal_uart_set_baud(cyhal_uart_t *obj, uint32_t baudrate, uint32_t *actualbaud);
cy_rslt_t cyhal_uart_configure(cyhal_uart_t *obj, const cyhal_uart_cfg_t *cfg);
cy_rslt_t cyhal_uart_getc(cyhal_uart_t *obj, uint8_t *value, uint32_t timeout);
cy_rslt_t cyhal_uart_putc(cyhal_uart_t *obj, uint32_t value);
uint32_t cyhal_uart_readable(cyhal_uart_t *obj);
uint32_t cyhal_uart_writable(cyhal_uart_t *obj);
cy_rslt_t cyhal_uart_clear(cyhal_uart_t *obj);
cy_rslt_t cyhal_uart_enable_flow_control(cyhal_uart_t *obj, _Bool enable_cts, _Bool enable_rts);
cy_rslt_t cyhal_uart_write(cyhal_uart_t *obj, void *tx, size_t *tx_length);
cy_rslt_t cyhal_uart_read(cyhal_uart_t *obj, void *rx, size_t *rx_length);
cy_rslt_t cyhal_uart_set_async_mode(cyhal_uart_t *obj, cyhal_async_mode_t mode, uint8_t dma_priority);
cy_rslt_t cyhal_uart_write_async(cyhal_uart_t *obj, void *tx, size_t length);
cy_rslt_t cyhal_uart_read_async(cyhal_uart_t *obj, void *rx, size_t length);
_Bool cyhal_uart_is_tx_active(cyhal_uart_t *obj);
_Bool cyhal_uart_is_rx_active(cyhal_uart_t *obj);
cy_rslt_t cyhal_uart_write_abort(cyhal_uart_t *obj);
cy_rslt_t cyhal_uart_read_abort(cyhal_uart_t *obj);
void cyhal_uart_register_callback(cyhal_uart_t *obj, cyhal_uart_event_callback_t callback, void *callback_arg);
void cyhal_uart_enable_event(cyhal_uart_t *obj, cyhal_uart_event_t event, uint8_t intr_priority, _Bool enable);
cy_rslt_t cyhal_uart_set_fifo_level(cyhal_uart_t *obj, cyhal_uart_fifo_type_t type, uint16_t level);
cy_rslt_t cyhal_uart_enable_output(cyhal_uart_t *obj, cyhal_uart_output_t output, cyhal_source_t *source);
cy_rslt_t cyhal_uart_disable_output(cyhal_uart_t *obj, cyhal_uart_output_t output);
cy_rslt_t cyhal_uart_init_cfg(cyhal_uart_t *obj, const cyhal_uart_configurator_t *cfg);
cy_rslt_t cyhal_uart_config_software_buffer(cyhal_uart_t *obj, uint8_t *rx_buffer, uint32_t rx_buffer_size);
_Bool __hal_uart_initialized = 0;
_Bool __hal_uart_interrupt_registered = 0;
cy_rslt_t cyhal_uart_init(cyhal_uart_t* obj, cyhal_gpio_t tx, cyhal_gpio_t rx, cyhal_gpio_t cts, cyhal_gpio_t rts,
                          const cyhal_clock_t* clk, const cyhal_uart_cfg_t* cfg)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 0) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 44, __func__, "__hal_uart_initialized == false"));
    __hal_uart_initialized = 1;
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_init_cfg(cyhal_uart_t* obj, const cyhal_uart_configurator_t* cfg)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 0) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 54, __func__, "__hal_uart_initialized == false"));
    __hal_uart_initialized = 1;
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
void cyhal_uart_free(cyhal_uart_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 64, __func__, "__hal_uart_initialized == true"));
    __hal_uart_initialized = 0;
    __VERIFIER_atomic_end();
    return;
}
cy_rslt_t cyhal_uart_set_baud(cyhal_uart_t* obj, uint32_t baudrate, uint32_t* actualbaud)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 74, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_configure(cyhal_uart_t* obj, const cyhal_uart_cfg_t* cfg)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 83, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_getc(cyhal_uart_t* obj, uint8_t* value, uint32_t timeout)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 92, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_putc(cyhal_uart_t* obj, uint32_t value)
{
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 100, __func__, "__hal_uart_initialized == true"));
    return __VERIFIER_nondet_uint();
}
uint32_t cyhal_uart_readable(cyhal_uart_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 108, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
uint32_t cyhal_uart_writable(cyhal_uart_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 117, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_clear(cyhal_uart_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 126, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_enable_flow_control(cyhal_uart_t* obj, _Bool enable_cts, _Bool enable_rts)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 135, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_write(cyhal_uart_t* obj, void* tx, size_t* tx_length)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 144, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_read(cyhal_uart_t* obj, void* rx, size_t* rx_length)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 153, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_set_async_mode(cyhal_uart_t* obj, cyhal_async_mode_t mode, uint8_t dma_priority)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 162, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_write_async(cyhal_uart_t* obj, void* tx, size_t length)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 171, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_read_async(cyhal_uart_t* obj, void* rx, size_t length)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 180, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
_Bool cyhal_uart_is_tx_active(cyhal_uart_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 189, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_bool();
}
_Bool cyhal_uart_is_rx_active(cyhal_uart_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 198, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_bool();
}
cy_rslt_t cyhal_uart_write_abort(cyhal_uart_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 207, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_read_abort(cyhal_uart_t* obj)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 216, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
void cyhal_uart_register_callback(cyhal_uart_t* obj, cyhal_uart_event_callback_t callback, void* callback_arg)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 225, __func__, "__hal_uart_initialized == true"));
    __hal_uart_interrupt_registered = 1;
    __VERIFIER_atomic_end();
    return;
}
void cyhal_uart_enable_event(cyhal_uart_t* obj, cyhal_uart_event_t event, uint8_t intr_priority, _Bool enable)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 235, __func__, "__hal_uart_initialized"));
    ((__hal_uart_interrupt_registered == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 236, __func__, "__hal_uart_interrupt_registered == true"));
    __VERIFIER_atomic_end();
    return;
}
cy_rslt_t cyhal_uart_set_fifo_level(cyhal_uart_t* obj, cyhal_uart_fifo_type_t type, uint16_t level)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 245, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_enable_output(cyhal_uart_t* obj, cyhal_uart_output_t output, cyhal_source_t* source)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 254, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_disable_output(cyhal_uart_t* obj, cyhal_uart_output_t output)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 263, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
cy_rslt_t cyhal_uart_config_software_buffer(cyhal_uart_t* obj, uint8_t* rx_buffer, uint32_t rx_buffer_size)
{
    __VERIFIER_atomic_begin();
    ((__hal_uart_initialized == 1) ? (void)0 : __assert_func ("/home/archlinux/Git/idcc/program-3dfs-sb17/firmware-3dfs-sb17/verification/sb-17-annotated-uart.c", 272, __func__, "__hal_uart_initialized == true"));
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
_Bool fs3d_packet_encode(uint8_t *const buf, size_t *const len, size_t size);
_Bool fs3d_packet_decode(uint8_t *const buf, size_t *const len, size_t size);
uint8_t fs3d_packet_cb_crc(const uint8_t *const buf, size_t len);
_Bool fs3d_packet_encode(uint8_t *const buf, size_t *const len, size_t size)
{
    if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
    fs3d_packet_cb_crc((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
    return __VERIFIER_nondet_bool();
}
_Bool fs3d_packet_decode(uint8_t *const buf, size_t *const len, size_t size)
{
    fs3d_packet_cb_crc((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
    return __VERIFIER_nondet_bool();
}
void __assert (const char *, int, const char *)
     __attribute__ ((__noreturn__));
void __assert_func (const char *, int, const char *, const char *)
     __attribute__ ((__noreturn__));

typedef uint8_t pb_byte_t;
typedef pb_byte_t pb_type_t;
    typedef uint_least16_t pb_size_t;
    typedef int_least16_t pb_ssize_t;
typedef struct pb_istream_s pb_istream_t;
typedef struct pb_ostream_s pb_ostream_t;
typedef struct pb_field_iter_s pb_field_iter_t;
typedef struct pb_msgdesc_s pb_msgdesc_t;
struct pb_msgdesc_s {
    const uint32_t *field_info;
    const pb_msgdesc_t * const * submsg_info;
    const pb_byte_t *default_value;
    _Bool (*field_callback)(pb_istream_t *istream, pb_ostream_t *ostream, const pb_field_iter_t *field);
    pb_size_t field_count;
    pb_size_t required_field_count;
    pb_size_t largest_tag;
};
struct pb_field_iter_s {
    const pb_msgdesc_t *descriptor;
    void *message;
    pb_size_t index;
    pb_size_t field_info_index;
    pb_size_t required_field_index;
    pb_size_t submessage_index;
    pb_size_t tag;
    pb_size_t data_size;
    pb_size_t array_size;
    pb_type_t type;
    void *pField;
    void *pData;
    void *pSize;
    const pb_msgdesc_t *submsg_desc;
};
typedef pb_field_iter_t pb_field_t;


struct pb_bytes_array_s {
    pb_size_t size;
    pb_byte_t bytes[1];
};
typedef struct pb_bytes_array_s pb_bytes_array_t;
typedef struct pb_callback_s pb_callback_t;
struct pb_callback_s {
    union {
        _Bool (*decode)(pb_istream_t *stream, const pb_field_t *field, void **arg);
        _Bool (*encode)(pb_ostream_t *stream, const pb_field_t *field, void * const *arg);
    } funcs;
    void *arg;
};
extern _Bool pb_default_field_callback(pb_istream_t *istream, pb_ostream_t *ostream, const pb_field_t *field);
typedef enum {
    PB_WT_VARINT = 0,
    PB_WT_64BIT = 1,
    PB_WT_STRING = 2,
    PB_WT_32BIT = 5,
    PB_WT_PACKED = 255
} pb_wire_type_t;
typedef struct pb_extension_type_s pb_extension_type_t;
typedef struct pb_extension_s pb_extension_t;
struct pb_extension_type_s {
    _Bool (*decode)(pb_istream_t *stream, pb_extension_t *extension,
                   uint32_t tag, pb_wire_type_t wire_type);
    _Bool (*encode)(pb_ostream_t *stream, const pb_extension_t *extension);
    const void *arg;
};
struct pb_extension_s {
    const pb_extension_type_t *type;
    void *dest;
    pb_extension_t *next;
    _Bool found;
};
typedef enum _hs_protobuf_fs3d_SensorConfigType {
    hs_protobuf_fs3d_SensorConfigType_SENSORCONFIG_SENSOR_ENABLED = 0,
    hs_protobuf_fs3d_SensorConfigType_SENSORCONFIG_SENSOR_OFFSET = 1
} hs_protobuf_fs3d_SensorConfigType;
typedef enum _hs_protobuf_fs3d_SensorDataType {
    hs_protobuf_fs3d_SensorDataType_SENSORDATA_RAW_VALUES = 0,
    hs_protobuf_fs3d_SensorDataType_SENSORDATA_FILTERED_VALUES = 1
} hs_protobuf_fs3d_SensorDataType;
typedef enum _hs_protobuf_fs3d_ResponseCode {
    hs_protobuf_fs3d_ResponseCode_SUCCESSFUL = 0,
    hs_protobuf_fs3d_ResponseCode_NOT_SUPPORTED = 1,
    hs_protobuf_fs3d_ResponseCode_NOT_IMPLEMENTED = 2,
    hs_protobuf_fs3d_ResponseCode_UNKNOWN_FAIlURE = 3,
    hs_protobuf_fs3d_ResponseCode_DECODE_FAILED = 4,
    hs_protobuf_fs3d_ResponseCode_UNSUPPORTED_MESSAGE_TYPE = 5,
    hs_protobuf_fs3d_ResponseCode_MSG_TRANSFER_FAILED = 6
} hs_protobuf_fs3d_ResponseCode;
typedef enum _hs_protobuf_fs3d_GetSysInfoRequest_SysInfoType {
    hs_protobuf_fs3d_GetSysInfoRequest_SysInfoType_SYSINFO_VERSION_FIRMWARE = 0,
    hs_protobuf_fs3d_GetSysInfoRequest_SysInfoType_SYSINFO_VERSION_PROTOCOL = 1,
    hs_protobuf_fs3d_GetSysInfoRequest_SysInfoType_SYSINFO_DETAILS_SENSOR = 2
} hs_protobuf_fs3d_GetSysInfoRequest_SysInfoType;
typedef enum _hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType {
    hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType_SYSCONFIG_SENSORS_SENSITIVITY = 0,
    hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType_SYSCONFIG_SENSORS_SAMPLING_RATE = 1,
    hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType_SYSCONFIG_DATA_TRANSFER_RATE = 2,
    hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType_SYSCONFIG_SAR_CLOCK_DIVIDER = 3
} hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType;
typedef enum _hs_protobuf_fs3d_GetSensorDataBulkRequest_SensorDataBulkState {
    hs_protobuf_fs3d_GetSensorDataBulkRequest_SensorDataBulkState_SENSORDATA_BULK_START = 0,
    hs_protobuf_fs3d_GetSensorDataBulkRequest_SensorDataBulkState_SENSORDATA_BULK_STOP = 1
} hs_protobuf_fs3d_GetSensorDataBulkRequest_SensorDataBulkState;
typedef struct _hs_protobuf_fs3d_Empty {
    char dummy_field;
} hs_protobuf_fs3d_Empty;
typedef struct _hs_protobuf_fs3d_SysInfoVersion {
    uint32_t major;
    uint32_t minor;
    uint32_t patch;
} hs_protobuf_fs3d_SysInfoVersion;
typedef struct _hs_protobuf_fs3d_SysInfoDetailsSensor {
    pb_callback_t name;
    _Bool has_version;
    hs_protobuf_fs3d_SysInfoVersion version;
    uint32_t maxNumSensors;
} hs_protobuf_fs3d_SysInfoDetailsSensor;
typedef struct _hs_protobuf_fs3d_GetSysInfoRequest {
    hs_protobuf_fs3d_GetSysInfoRequest_SysInfoType type;
} hs_protobuf_fs3d_GetSysInfoRequest;
typedef struct _hs_protobuf_fs3d_GetSysInfoResponse {
    pb_size_t which_data;
    union {
        hs_protobuf_fs3d_SysInfoVersion versionFirmware;
        hs_protobuf_fs3d_SysInfoVersion versionProtocol;
        hs_protobuf_fs3d_SysInfoDetailsSensor detailsSensor;
    } data;
} hs_protobuf_fs3d_GetSysInfoResponse;
typedef struct _hs_protobuf_fs3d_GetSysConfigRequest {
    hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType type;
} hs_protobuf_fs3d_GetSysConfigRequest;
typedef struct _hs_protobuf_fs3d_SysConfigData {
    pb_size_t which_data;
    union {
        uint32_t sensorsSensitivity;
        uint32_t sensorsSamplingRate;
        uint32_t dataTransferRate;
        uint32_t sarClockDivider;
    } data;
} hs_protobuf_fs3d_SysConfigData;
typedef struct _hs_protobuf_fs3d_GetSysConfigResponse {
    _Bool has_data;
    hs_protobuf_fs3d_SysConfigData data;
} hs_protobuf_fs3d_GetSysConfigResponse;
typedef struct _hs_protobuf_fs3d_SetSysConfigRequest {
    _Bool has_data;
    hs_protobuf_fs3d_SysConfigData data;
} hs_protobuf_fs3d_SetSysConfigRequest;
typedef struct _hs_protobuf_fs3d_GetSensorConfigData {
    uint32_t sensorNum;
    hs_protobuf_fs3d_SensorConfigType type;
} hs_protobuf_fs3d_GetSensorConfigData;
typedef struct _hs_protobuf_fs3d_GetSensorConfigRequest {
    pb_callback_t data;
} hs_protobuf_fs3d_GetSensorConfigRequest;
typedef struct _hs_protobuf_fs3d_SensorConfigData {
    uint32_t sensorNum;
    pb_size_t which_data;
    union {
        _Bool sensorEnabled;
        int32_t sensorOffset;
    } data;
} hs_protobuf_fs3d_SensorConfigData;
typedef struct _hs_protobuf_fs3d_GetSensorConfigResponse {
    pb_callback_t data;
} hs_protobuf_fs3d_GetSensorConfigResponse;
typedef struct _hs_protobuf_fs3d_SetSensorConfigRequest {
    pb_callback_t data;
} hs_protobuf_fs3d_SetSensorConfigRequest;
typedef struct _hs_protobuf_fs3d_GetSensorDataSingleRequest {
    hs_protobuf_fs3d_SensorDataType type;
} hs_protobuf_fs3d_GetSensorDataSingleRequest;
typedef struct _hs_protobuf_fs3d_GetSensorDataBulkRequest {
    hs_protobuf_fs3d_SensorDataType type;
    hs_protobuf_fs3d_GetSensorDataBulkRequest_SensorDataBulkState state;
} hs_protobuf_fs3d_GetSensorDataBulkRequest;
typedef struct _hs_protobuf_fs3d_SensorMeasurement {
    uint32_t timestamp;
    int32_t value;
} hs_protobuf_fs3d_SensorMeasurement;
typedef struct _hs_protobuf_fs3d_SensorData {
    uint32_t sensorNum;
    _Bool has_measurement;
    hs_protobuf_fs3d_SensorMeasurement measurement;
} hs_protobuf_fs3d_SensorData;
typedef struct _hs_protobuf_fs3d_GetSensorDataResponse {
    pb_callback_t data;
} hs_protobuf_fs3d_GetSensorDataResponse;
typedef struct _hs_protobuf_fs3d_Requests {
    pb_callback_t cb_request;
    pb_size_t which_request;
    union {
        hs_protobuf_fs3d_GetSysInfoRequest getSysInfo;
        hs_protobuf_fs3d_GetSysConfigRequest getSysConfig;
        hs_protobuf_fs3d_SetSysConfigRequest setSysConfig;
        hs_protobuf_fs3d_GetSensorConfigRequest getSensorConfig;
        hs_protobuf_fs3d_SetSensorConfigRequest setSensorConfig;
        hs_protobuf_fs3d_GetSensorDataSingleRequest getSensorDataSingle;
        hs_protobuf_fs3d_GetSensorDataBulkRequest getSensorDataBulk;
    } request;
} hs_protobuf_fs3d_Requests;
typedef struct _hs_protobuf_fs3d_Responses {
    hs_protobuf_fs3d_ResponseCode responseCode;
    pb_callback_t cb_response;
    pb_size_t which_response;
    union {
        hs_protobuf_fs3d_GetSysInfoResponse getSysInfo;
        hs_protobuf_fs3d_GetSysConfigResponse getSysConfig;
        hs_protobuf_fs3d_GetSensorConfigResponse getSensorConfig;
        hs_protobuf_fs3d_GetSensorDataResponse getSensorData;
    } response;
} hs_protobuf_fs3d_Responses;
extern const pb_msgdesc_t hs_protobuf_fs3d_Empty_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_SysInfoVersion_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_SysInfoDetailsSensor_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_GetSysInfoRequest_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_GetSysInfoResponse_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_GetSysConfigRequest_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_SysConfigData_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_GetSysConfigResponse_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_SetSysConfigRequest_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_GetSensorConfigData_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_GetSensorConfigRequest_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_SensorConfigData_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_GetSensorConfigResponse_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_SetSensorConfigRequest_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_GetSensorDataSingleRequest_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_GetSensorDataBulkRequest_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_SensorMeasurement_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_SensorData_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_GetSensorDataResponse_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_Requests_msg;
extern const pb_msgdesc_t hs_protobuf_fs3d_Responses_msg;
typedef hs_protobuf_fs3d_SysInfoVersion FS3D_SysInfoVersion_Init_t;
typedef struct FS3D_SysInfoDetailsSensor_Init {
    const char *name;
    FS3D_SysInfoVersion_Init_t version;
    uint32_t maxNumSensors;
} FS3D_SysInfoDetailsSensor_Init_t;
typedef struct {
    uint8_t count;
    hs_protobuf_fs3d_SensorConfigData data[32];
} FS3D_SensorConfigData_t;
typedef struct {
    uint8_t count;
    hs_protobuf_fs3d_GetSensorConfigData data[32];
} FS3D_GetSensorConfigData_t;
union FS3D_Sensor_Config_Request_Union {
    FS3D_SensorConfigData_t setSensorConfig;
    FS3D_GetSensorConfigData_t getSensorConfig;
};
typedef struct {
    uint8_t count;
    hs_protobuf_fs3d_SensorData data[32];
} FS3D_SensorData_t;
typedef struct {
    _Bool enabled;
    int32_t offset;
} FS3D_Sensor_Configuration;
void fs3d_init(const FS3D_SysInfoVersion_Init_t *const version_firmware,
               const FS3D_SysInfoDetailsSensor_Init_t *const details_sensor, const _Bool initially_activated,
               const _Bool sensor_offset_configurable);
void fs3d_deinit(void);
_Bool fs3d_msg_process(uint8_t *const dst, size_t dst_size, const uint8_t *const src, size_t src_len);
hs_protobuf_fs3d_ResponseCode fs3d_cb_req_getSysConfig(const hs_protobuf_fs3d_GetSysConfigRequest *const req,
                                                       hs_protobuf_fs3d_GetSysConfigResponse *const rsp);
_Bool fs3d_cb_req_setSysConfig(const hs_protobuf_fs3d_SetSysConfigRequest *const req);
_Bool fs3d_cb_req_setSensorConfig(const FS3D_SensorConfigData_t *const req);
_Bool fs3d_cb_req_getSensorDataBulk(const hs_protobuf_fs3d_GetSensorDataBulkRequest *const req);
_Bool fs3d_msg_cb_send(uint8_t *const buf, size_t len);
void fs3d_update_sensor_measurement(const uint32_t sensor_num, const uint32_t timestamp, const int32_t value);
_Bool fs3d_transfer_sensor_data(_Bool raw, uint8_t *const buf, size_t size);
void fs3d_rsp_code_send_transfer_failed(uint8_t *const buf, size_t size);
struct pb_istream_s
{
    _Bool (*callback)(pb_istream_t *stream, pb_byte_t *buf, size_t count);
    void *state;
    size_t bytes_left;
    const char *errmsg;
};
_Bool pb_decode(pb_istream_t *stream, const pb_msgdesc_t *fields, void *dest_struct);
_Bool pb_decode_ex(pb_istream_t *stream, const pb_msgdesc_t *fields, void *dest_struct, unsigned int flags);
void pb_release(const pb_msgdesc_t *fields, void *dest_struct);
pb_istream_t pb_istream_from_buffer(const pb_byte_t *buf, size_t msglen);
_Bool pb_read(pb_istream_t *stream, pb_byte_t *buf, size_t count);
_Bool pb_decode_tag(pb_istream_t *stream, pb_wire_type_t *wire_type, uint32_t *tag, _Bool *eof);
_Bool pb_skip_field(pb_istream_t *stream, pb_wire_type_t wire_type);
_Bool pb_decode_varint(pb_istream_t *stream, uint64_t *dest);
_Bool pb_decode_varint32(pb_istream_t *stream, uint32_t *dest);
_Bool pb_decode_bool(pb_istream_t *stream, _Bool *dest);
_Bool pb_decode_svarint(pb_istream_t *stream, int64_t *dest);
_Bool pb_decode_fixed32(pb_istream_t *stream, void *dest);
_Bool pb_decode_fixed64(pb_istream_t *stream, void *dest);
_Bool pb_make_string_substream(pb_istream_t *stream, pb_istream_t *substream);
_Bool pb_close_string_substream(pb_istream_t *stream, pb_istream_t *substream);
struct pb_ostream_s
{
    _Bool (*callback)(pb_ostream_t *stream, const pb_byte_t *buf, size_t count);
    void *state;
    size_t max_size;
    size_t bytes_written;
    const char *errmsg;
};
_Bool pb_encode(pb_ostream_t *stream, const pb_msgdesc_t *fields, const void *src_struct);
_Bool pb_encode_ex(pb_ostream_t *stream, const pb_msgdesc_t *fields, const void *src_struct, unsigned int flags);
_Bool pb_get_encoded_size(size_t *size, const pb_msgdesc_t *fields, const void *src_struct);
pb_ostream_t pb_ostream_from_buffer(pb_byte_t *buf, size_t bufsize);
_Bool pb_write(pb_ostream_t *stream, const pb_byte_t *buf, size_t count);
_Bool pb_encode_tag_for_field(pb_ostream_t *stream, const pb_field_iter_t *field);
_Bool pb_encode_tag(pb_ostream_t *stream, pb_wire_type_t wiretype, uint32_t field_number);
_Bool pb_encode_varint(pb_ostream_t *stream, uint64_t value);
_Bool pb_encode_svarint(pb_ostream_t *stream, int64_t value);
_Bool pb_encode_string(pb_ostream_t *stream, const pb_byte_t *buffer, size_t size);
_Bool pb_encode_fixed32(pb_ostream_t *stream, const void *value);
_Bool pb_encode_fixed64(pb_ostream_t *stream, const void *value);
_Bool pb_encode_submessage(pb_ostream_t *stream, const pb_msgdesc_t *fields, const void *src_struct);
static _Bool _fs3d_pb_encode_str(pb_ostream_t *ostream, const pb_field_t *field, void *const *arg);
static _Bool _fs3d_cb_req_getSysInfo(const hs_protobuf_fs3d_GetSysInfoRequest *const req, uint8_t *const buf,
                                    size_t size);
static _Bool _fs3d_cb_req_getSysConfig(const hs_protobuf_fs3d_GetSysConfigRequest *const req, uint8_t *const buf,
                                      size_t size);
static _Bool _fs3d_cb_req_getSensorConfig(const FS3D_GetSensorConfigData_t *const req, uint8_t *const buf, size_t size);
static _Bool _fs3d_cb_req_getSensorDataSingle(const hs_protobuf_fs3d_GetSensorDataSingleRequest *const req,
                                             uint8_t *const buf, size_t size);
static void _fs3d_save_sensor_configuration(hs_protobuf_fs3d_SensorConfigData *data)
{
    if (__VERIFIER_nondet_bool()) {
        if (__VERIFIER_nondet_bool()) {
            __asm volatile ("nop");
        } else if (__VERIFIER_nondet_bool()) {
            __asm volatile ("nop");
        }
    }
    return;
}
static _Bool _fs3d_set_sensor_config_data_callback(pb_istream_t *stream, const pb_field_t *field, void **arg)
{
    pb_decode((pb_istream_t *)__VERIFIER_nondet_pointer(), (const pb_msgdesc_t *)__VERIFIER_nondet_pointer(),
              (void *)__VERIFIER_nondet_pointer());
    _fs3d_save_sensor_configuration((hs_protobuf_fs3d_SensorConfigData *)__VERIFIER_nondet_pointer());
    return __VERIFIER_nondet_bool();
}
static _Bool _fs3d_get_sensor_config_data_callback(pb_istream_t *stream, const pb_field_t *field, void **arg)
{
    return pb_decode((pb_istream_t *)__VERIFIER_nondet_pointer(), (const pb_msgdesc_t *)__VERIFIER_nondet_pointer(),
                     (void *)__VERIFIER_nondet_pointer());
}
static _Bool _fs3d_decode_callback(pb_istream_t *stream, const pb_field_t *field, void **arg)
{
    if (__VERIFIER_nondet_bool()) {
        _fs3d_set_sensor_config_data_callback((pb_istream_t *)__VERIFIER_nondet_pointer(),
                                              (const pb_field_t *)__VERIFIER_nondet_pointer(),
                                              (void **)__VERIFIER_nondet_pointer());
    } else if (__VERIFIER_nondet_bool()) {
        _fs3d_get_sensor_config_data_callback((pb_istream_t *)__VERIFIER_nondet_pointer(),
                                              (const pb_field_t *)__VERIFIER_nondet_pointer(),
                                              (void **)__VERIFIER_nondet_pointer());
    }
    return __VERIFIER_nondet_bool();
}
static _Bool _fs3d_msg_encode(uint8_t *const buf, size_t *const len, size_t size, const pb_msgdesc_t *fields,
                             const void *src_struct)
{
    pb_ostream_from_buffer((pb_byte_t *)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
    pb_encode((pb_ostream_t *)__VERIFIER_nondet_pointer(), (const pb_msgdesc_t *)__VERIFIER_nondet_pointer(),
              (void *)__VERIFIER_nondet_pointer());
    return __VERIFIER_nondet_bool();
}
static _Bool _fs3d_msg_encode_send(uint8_t *const buf, size_t size, const pb_msgdesc_t *fields, const void *src_struct)
{
    if (!_fs3d_msg_encode((uint8_t *)__VERIFIER_nondet_pointer(), (size_t *)__VERIFIER_nondet_pointer(),
                          __VERIFIER_nondet_size_t(), (const pb_msgdesc_t *)__VERIFIER_nondet_pointer(),
                          (const void *)__VERIFIER_nondet_pointer())) {
        return __VERIFIER_nondet_bool();
    }
    return fs3d_msg_cb_send((uint8_t *)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
}
static _Bool _fs3d_msg_decode(const uint8_t *const buf, size_t len, const pb_msgdesc_t *fields, void *dest_struct)
{
    pb_istream_from_buffer((const pb_byte_t *)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
    return pb_decode((pb_istream_t *)__VERIFIER_nondet_pointer(), (pb_msgdesc_t *)__VERIFIER_nondet_pointer(),
                     (void *)__VERIFIER_nondet_pointer());
}
static void _fs3d_rsp_code_send(uint8_t *const buf, size_t size, hs_protobuf_fs3d_ResponseCode code)
{
    _fs3d_msg_encode_send((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                          (const pb_msgdesc_t *)__VERIFIER_nondet_pointer(), (const void *)__VERIFIER_nondet_pointer());
}
void fs3d_init(const FS3D_SysInfoVersion_Init_t *const version_firmware,
               const FS3D_SysInfoDetailsSensor_Init_t *const details_sensor, const _Bool initially_activated,
               const _Bool sensor_offset_configurable)
{
    for (int i = 0; i < 32; i++) {
        __asm volatile ("nop");
    }
    return;
}
void fs3d_deinit(void)
{
    return;
}
_Bool fs3d_msg_process(uint8_t *const dst, size_t dst_size, const uint8_t *const src, size_t src_len)
{
    _fs3d_decode_callback((pb_istream_t *)__VERIFIER_nondet_pointer(), (const pb_field_t *)__VERIFIER_nondet_pointer(),
                          (void **)__VERIFIER_nondet_pointer());
    if (!_fs3d_msg_decode((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                          (const pb_msgdesc_t *)__VERIFIER_nondet_pointer(), (void **)__VERIFIER_nondet_pointer())) {
        _fs3d_rsp_code_send((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                            (hs_protobuf_fs3d_ResponseCode)__VERIFIER_nondet_int());
        return __VERIFIER_nondet_bool();
    }
    switch (__VERIFIER_nondet_size_t()) {
        case 1:
            _fs3d_cb_req_getSysInfo((const hs_protobuf_fs3d_GetSysInfoRequest *)__VERIFIER_nondet_pointer(),
                                    (uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
            break;
        case 2:
            _fs3d_cb_req_getSysConfig((const hs_protobuf_fs3d_GetSysConfigRequest *const)__VERIFIER_nondet_pointer(),
                                      (uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
            break;
        case 3:
            fs3d_cb_req_setSysConfig((const hs_protobuf_fs3d_SetSysConfigRequest *const)__VERIFIER_nondet_pointer());
            break;
        case 4:
            _fs3d_cb_req_getSensorConfig((const FS3D_GetSensorConfigData_t *const)__VERIFIER_nondet_pointer(),
                                         (uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
            break;
        case 5:
            fs3d_cb_req_setSensorConfig((const FS3D_SensorConfigData_t *const)__VERIFIER_nondet_pointer());
            break;
        case 6:
            _fs3d_cb_req_getSensorDataSingle(
                (const hs_protobuf_fs3d_GetSensorDataSingleRequest *const)__VERIFIER_nondet_pointer(),
                (uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
            break;
        case 7:
            fs3d_cb_req_getSensorDataBulk(
                (const hs_protobuf_fs3d_GetSensorDataBulkRequest *const)__VERIFIER_nondet_pointer());
            break;
        default:
            _fs3d_rsp_code_send((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                                __VERIFIER_nondet_int());
    }
    return __VERIFIER_nondet_bool();
}
static _Bool _fs3d_pb_encode_str(pb_ostream_t *ostream, const pb_field_t *field, void *const *arg)
{
    if (!pb_encode_tag_for_field((pb_ostream_t *)__VERIFIER_nondet_pointer(),
                                 (const pb_field_iter_t *)__VERIFIER_nondet_bool())) {
        return __VERIFIER_nondet_bool();
    };
    return pb_encode_string((pb_ostream_t *)__VERIFIER_nondet_pointer(), (const pb_byte_t *)__VERIFIER_nondet_pointer(),
                            __VERIFIER_nondet_size_t());
}
static _Bool _fs3d_cb_req_getSysInfo(const hs_protobuf_fs3d_GetSysInfoRequest *const req, uint8_t *const buf,
                                    size_t size)
{
    switch (__VERIFIER_nondet_uchar()) {
        case hs_protobuf_fs3d_GetSysInfoRequest_SysInfoType_SYSINFO_VERSION_FIRMWARE:
            break;
        case hs_protobuf_fs3d_GetSysInfoRequest_SysInfoType_SYSINFO_VERSION_PROTOCOL:
            break;
        case hs_protobuf_fs3d_GetSysInfoRequest_SysInfoType_SYSINFO_DETAILS_SENSOR:
            _fs3d_pb_encode_str((pb_ostream_t *)__VERIFIER_nondet_pointer(),
                                (const pb_field_t *)__VERIFIER_nondet_pointer(),
                                (void *const *)__VERIFIER_nondet_pointer());
            break;
    }
    return _fs3d_msg_encode_send((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                                 (const pb_msgdesc_t *)__VERIFIER_nondet_pointer(),
                                 (const void *)__VERIFIER_nondet_pointer());
}
static _Bool _fs3d_cb_req_getSysConfig(const hs_protobuf_fs3d_GetSysConfigRequest *const req, uint8_t *const buf,
                                      size_t size)
{
    fs3d_cb_req_getSysConfig((const hs_protobuf_fs3d_GetSysConfigRequest *const)__VERIFIER_nondet_pointer(),
                             (hs_protobuf_fs3d_GetSysConfigResponse *const)__VERIFIER_nondet_pointer());
    return _fs3d_msg_encode_send((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                                 (const pb_msgdesc_t *)__VERIFIER_nondet_pointer(),
                                 (const void *)__VERIFIER_nondet_pointer());
}
_Bool _fs3d_encode_get_SensorConfig(pb_ostream_t *stream, const pb_field_iter_t *field, void *const *arg)
{
    {
        if (!pb_encode_tag_for_field((pb_ostream_t *)__VERIFIER_nondet_pointer(),
                                     (const pb_field_iter_t *)__VERIFIER_nondet_pointer())) {
            return __VERIFIER_nondet_bool();
        }
        if (!pb_encode_submessage((pb_ostream_t *)__VERIFIER_nondet_pointer(),
                                  (pb_msgdesc_t *)__VERIFIER_nondet_pointer(), (void *)__VERIFIER_nondet_pointer())) {
            return __VERIFIER_nondet_bool();
        }
    }
    return __VERIFIER_nondet_bool();
}
static _Bool _fs3d_cb_req_getSensorConfig(const FS3D_GetSensorConfigData_t *const req, uint8_t *const buf, size_t size)
{
    {
        if (__VERIFIER_nondet_bool()) {
            __asm volatile ("nop");
        } else if (__VERIFIER_nondet_bool()) {
            __asm volatile ("nop");
        }
    }
    _fs3d_encode_get_SensorConfig((pb_ostream_t *)__VERIFIER_nondet_pointer(),
                                  (const pb_field_iter_t *)__VERIFIER_nondet_pointer(),
                                  (void *const *)__VERIFIER_nondet_pointer());
    return _fs3d_msg_encode_send((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                                 (const pb_msgdesc_t *)__VERIFIER_nondet_pointer(),
                                 (const void *)__VERIFIER_nondet_pointer());
}
static _Bool _fs3d_cb_req_getSensorDataSingle(const hs_protobuf_fs3d_GetSensorDataSingleRequest *const req,
                                             uint8_t *const buf, size_t size)
{
    return fs3d_transfer_sensor_data(__VERIFIER_nondet_bool(), (uint8_t *const)__VERIFIER_nondet_pointer(),
                                     __VERIFIER_nondet_size_t());
}
static _Bool _fs3d_encode_getSensorData(pb_ostream_t *stream, const pb_field_iter_t *field, void *const *arg)
{
    {
        if (!pb_encode_tag_for_field((pb_ostream_t *)__VERIFIER_nondet_pointer(),
                                     (const pb_field_iter_t *)__VERIFIER_nondet_pointer())) {
            return __VERIFIER_nondet_bool();
        }
        if (!pb_encode_submessage((pb_ostream_t *)__VERIFIER_nondet_pointer(),
                                  (pb_msgdesc_t *)__VERIFIER_nondet_pointer(), (void *)__VERIFIER_nondet_pointer())) {
            return __VERIFIER_nondet_bool();
        }
    }
    return __VERIFIER_nondet_bool();
}
_Bool fs3d_transfer_sensor_data(_Bool raw, uint8_t *const buf, size_t size)
{
    if (__VERIFIER_nondet_bool()) {
        {
            if (__VERIFIER_nondet_bool()) {
                __asm volatile ("nop");
            }
        }
    } else {
        __asm volatile ("nop");
    }
    _fs3d_encode_getSensorData((pb_ostream_t *)__VERIFIER_nondet_pointer(),
                               (const pb_field_iter_t *)__VERIFIER_nondet_pointer(),
                               (void *const *)__VERIFIER_nondet_pointer());
    return _fs3d_msg_encode_send((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                                 (const pb_msgdesc_t *)__VERIFIER_nondet_pointer(),
                                 (const void *)__VERIFIER_nondet_pointer());
}
void fs3d_update_sensor_measurement(const uint32_t sensor_num, const uint32_t timestamp, const int32_t value)
{
    return;
}
void fs3d_rsp_code_send_transfer_failed(uint8_t *const buf, size_t size)
{
    _fs3d_rsp_code_send((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                        __VERIFIER_nondet_int());
}
typedef struct fs3d_slip_state {
    size_t dst_len;
    _Bool escaping;
} fs3d_slip_state_t;
_Bool fs3d_slip_encode(uint8_t *const dst, size_t *dst_len, size_t dst_size, const uint8_t *const src, size_t src_len);
_Bool fs3d_slip_decode(uint8_t *const dst, size_t dst_size, const uint8_t *const src, size_t src_len);
void fs3d_slip_decode_init(fs3d_slip_state_t *const state);
_Bool fs3d_slip_decode_chr(fs3d_slip_state_t *const state, uint8_t *const dst, size_t dst_size, uint8_t chr);
void fs3d_slip_cb_decode_complete(uint8_t *const buf, size_t len);
_Bool fs3d_slip_encode(uint8_t *const dst, size_t *dst_len, size_t dst_size, const uint8_t *const src, size_t src_len)
{
    if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
    {
        if (__VERIFIER_nondet_bool()) {
            if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
        } else if (__VERIFIER_nondet_bool()) {
            if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
        } else {
            if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
        }
    }
    if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
    return __VERIFIER_nondet_bool();
}
_Bool fs3d_slip_decode(uint8_t *const dst, size_t dst_size, const uint8_t *const src, size_t src_len)
{
    if (!(__VERIFIER_nondet_bool())) { return 0; };
    if (!(__VERIFIER_nondet_bool())) { return 0; };
    if (!(__VERIFIER_nondet_bool())) { return 0; };
    {
        if (__VERIFIER_nondet_bool()) {
            if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
            if (__VERIFIER_nondet_bool()) {
                if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
            } else if (__VERIFIER_nondet_bool()) {
                if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
            } else {
                return __VERIFIER_nondet_bool();
            }
        } else {
            if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
        }
    }
    return __VERIFIER_nondet_bool();
}
void fs3d_slip_decode_init(fs3d_slip_state_t *const state)
{
    return;
}
_Bool fs3d_slip_decode_chr(fs3d_slip_state_t *const state, uint8_t *const dst, size_t dst_size, uint8_t chr)
{
    if (__VERIFIER_nondet_bool()) {
        if (__VERIFIER_nondet_bool()) {
            fs3d_slip_cb_decode_complete((uint8_t *const)__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
        }
        fs3d_slip_decode_init((fs3d_slip_state_t *const)__VERIFIER_nondet_pointer());
    } else if (__VERIFIER_nondet_bool()) {
        __asm volatile ("nop");
    } else {
        if (__VERIFIER_nondet_bool()) {
            if (__VERIFIER_nondet_bool()) {
                if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
            } else if (__VERIFIER_nondet_bool()) {
                if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
            }
        } else {
            if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
        }
    }
    if (__VERIFIER_nondet_size_t() >= __VERIFIER_nondet_size_t() - __VERIFIER_nondet_size_t()) { return 0; };
    return __VERIFIER_nondet_bool();
}
typedef struct {
    uint8_t Channel;
    uint8_t Direction;
    uint16_t Value;
    uint8_t Gain;
} SB17_SENSOR_DATA_t;
typedef struct {
    uint32_t Timestamp;
    SB17_SENSOR_DATA_t Reading;
} SB17_SENSOR_READING_t;
typedef SB17_SENSOR_READING_t SENSOR_READINGS_t[32 * 4];
typedef struct {
    uint8_t SpiVersion;
    uint8_t SpiRevision;
    uint16_t ChipId;
    uint8_t ChipRevision;
    uint8_t ROM[16];
} SB17_CHIP_DATA_t;
typedef struct {
    uint32_t SensorSamplingRate;
    uint32_t DataTransferRate;
    uint32_t EnabledSenorsMask;
} SB17_CHIP_CONFIG_t;
cy_rslt_t sb17_initialize_spi(void (*publish_data)(SB17_SENSOR_READING_t readings[4]));
cy_rslt_t sb17_spi_read_chip_data(SB17_CHIP_DATA_t* chip_data);
void sb17_spi_read_all_data();
void sb17_spi_read_single_data(uint8_t sensor_id);
void sb17_spi_read_continous_range(uint8_t start_id, uint8_t end_id, _Bool range_readout);

typedef enum
{
    CYHAL_GPIO_IRQ_NONE = 0,
    CYHAL_GPIO_IRQ_RISE = 1 << 0,
    CYHAL_GPIO_IRQ_FALL = 1 << 1,
    CYHAL_GPIO_IRQ_BOTH = (CYHAL_GPIO_IRQ_RISE | CYHAL_GPIO_IRQ_FALL),
} cyhal_gpio_event_t;
typedef enum
{
    CYHAL_GPIO_DIR_INPUT,
    CYHAL_GPIO_DIR_OUTPUT,
    CYHAL_GPIO_DIR_BIDIRECTIONAL,
} cyhal_gpio_direction_t;
typedef enum
{
    CYHAL_GPIO_DRIVE_NONE,
    CYHAL_GPIO_DRIVE_ANALOG,
    CYHAL_GPIO_DRIVE_PULLUP,
    CYHAL_GPIO_DRIVE_PULLDOWN,
    CYHAL_GPIO_DRIVE_OPENDRAINDRIVESLOW,
    CYHAL_GPIO_DRIVE_OPENDRAINDRIVESHIGH,
    CYHAL_GPIO_DRIVE_STRONG,
    CYHAL_GPIO_DRIVE_PULLUPDOWN,
    CYHAL_GPIO_DRIVE_PULL_NONE,
} cyhal_gpio_drive_mode_t;
typedef void (*cyhal_gpio_event_callback_t)(void *callback_arg, cyhal_gpio_event_t event);
typedef struct cyhal_gpio_callback_data_s
{
    cyhal_gpio_event_callback_t callback;
    void* callback_arg;
    struct cyhal_gpio_callback_data_s* next;
    cyhal_gpio_t pin;
} cyhal_gpio_callback_data_t;
cy_rslt_t cyhal_gpio_init(cyhal_gpio_t pin, cyhal_gpio_direction_t direction, cyhal_gpio_drive_mode_t drive_mode, _Bool init_val);
void cyhal_gpio_free(cyhal_gpio_t pin);
cy_rslt_t cyhal_gpio_configure(cyhal_gpio_t pin, cyhal_gpio_direction_t direction, cyhal_gpio_drive_mode_t drive_mode);
void cyhal_gpio_write(cyhal_gpio_t pin, _Bool value);
_Bool cyhal_gpio_read(cyhal_gpio_t pin);
void cyhal_gpio_toggle(cyhal_gpio_t pin);
void cyhal_gpio_register_callback(cyhal_gpio_t pin, cyhal_gpio_callback_data_t* callback_data);
void cyhal_gpio_enable_event(cyhal_gpio_t pin, cyhal_gpio_event_t event, uint8_t intr_priority, _Bool enable);
cy_rslt_t cyhal_gpio_connect_digital(cyhal_gpio_t pin, cyhal_source_t source);
cy_rslt_t cyhal_gpio_enable_output(cyhal_gpio_t pin, cyhal_signal_type_t type, cyhal_source_t *source);
cy_rslt_t cyhal_gpio_disconnect_digital(cyhal_gpio_t pin, cyhal_source_t source);
cy_rslt_t cyhal_gpio_disable_output(cyhal_gpio_t pin);

static inline cyhal_resource_inst_t _cyhal_utils_get_gpio_resource(cyhal_gpio_t pin)
{
    cyhal_resource_inst_t rsc = { CYHAL_RSC_GPIO, ((uint8_t)(((uint8_t)pin) >> 3U)), ((uint8_t)(((uint8_t)pin) & 0x07U)) };
    return rsc;
}
cy_rslt_t _cyhal_utils_reserve_and_connect(const cyhal_resource_pin_mapping_t *mapping, uint8_t drive_mode);
void _cyhal_utils_disconnect_and_free(cyhal_gpio_t pin);
uint32_t _cyhal_utils_get_clock_count(cyhal_clock_block_t block);
static inline uint32_t _cyhal_utils_get_peripheral_clock_frequency(const cyhal_resource_inst_t *clocked_item)
{
    ( (void)(clocked_item) );
    return Cy_SysClk_ClkPeriGetFrequency();
}
static inline uint32_t _cyhal_utils_divider_value(const cyhal_resource_inst_t *clocked_item, uint32_t frequency, uint32_t frac_bits)
{
    return ((_cyhal_utils_get_peripheral_clock_frequency(clocked_item) * (1 << frac_bits)) + (frequency / 2)) / frequency;
}
cy_en_syspm_callback_mode_t _cyhal_utils_convert_haltopdl_pm_mode(cyhal_syspm_callback_mode_t mode);
cyhal_syspm_callback_mode_t _cyhal_utils_convert_pdltohal_pm_mode(cy_en_syspm_callback_mode_t mode);
int32_t _cyhal_utils_calculate_tolerance(cyhal_clock_tolerance_unit_t type, uint32_t desired_hz, uint32_t actual_hz);
cy_rslt_t _cyhal_utils_allocate_clock(cyhal_clock_t *clock, const cyhal_resource_inst_t *clocked_item,
                        cyhal_clock_block_t div, _Bool accept_larger);
cy_rslt_t _cyhal_utils_set_clock_frequency(cyhal_clock_t* clock, uint32_t hz, const cyhal_clock_tolerance_t *tolerance);
cy_rslt_t _cyhal_utils_find_hf_clk_div(uint32_t hz_src, uint32_t desired_hz, const cyhal_clock_tolerance_t *tolerance,
                        _Bool only_below_desired, uint32_t *div);
typedef cy_rslt_t (*_cyhal_utils_clk_div_func_t)(uint32_t hz_src, uint32_t desired_hz,
                        const cyhal_clock_tolerance_t *tolerance, _Bool only_below_desired, uint32_t *div);
cy_rslt_t _cyhal_utils_find_hf_source_n_divider(cyhal_clock_t *clock, uint32_t hz,
                        const cyhal_clock_tolerance_t *tolerance, _cyhal_utils_clk_div_func_t div_find_func,
                        cyhal_clock_t *hf_source, uint32_t *div);
cy_rslt_t _cyhal_utils_set_clock_frequency2(cyhal_clock_t *clock, uint32_t hz, const cyhal_clock_tolerance_t *tolerance);
static inline cy_rslt_t _cyhal_utils_peri_pclk_set_divider(en_clk_dst_t clk_dest, const cyhal_clock_t *clock, uint32_t div)
{
    ( (void)(clk_dest) );
    return Cy_SysClk_PeriphSetDivider(((cy_en_divider_types_t)((clock->block) & 0x03)), clock->channel, div);
}
static inline uint32_t _cyhal_utils_peri_pclk_get_divider(en_clk_dst_t clk_dest, const cyhal_clock_t *clock)
{
    ( (void)(clk_dest) );
    return Cy_SysClk_PeriphGetDivider(((cy_en_divider_types_t)((clock->block) & 0x03)), clock->channel);
}
static inline cy_rslt_t _cyhal_utils_peri_pclk_set_frac_divider(en_clk_dst_t clk_dest, const cyhal_clock_t *clock, uint32_t div_int, uint32_t div_frac)
{
    ( (void)(clk_dest) );
    return Cy_SysClk_PeriphSetFracDivider(((cy_en_divider_types_t)((clock->block) & 0x03)), clock->channel, div_int, div_frac);
}
static inline void _cyhal_utils_peri_pclk_get_frac_divider(en_clk_dst_t clk_dest, const cyhal_clock_t *clock, uint32_t *div_int, uint32_t *div_frac)
{
    ( (void)(clk_dest) );
    Cy_SysClk_PeriphGetFracDivider(((cy_en_divider_types_t)((clock->block) & 0x03)), clock->channel, div_int, div_frac);
}
static inline uint32_t _cyhal_utils_peri_pclk_get_frequency(en_clk_dst_t clk_dest, const cyhal_clock_t *clock)
{
    ( (void)(clk_dest) );
    return Cy_SysClk_PeriphGetFrequency(((cy_en_divider_types_t)((clock->block) & 0x03)), clock->channel);
}
static inline cy_rslt_t _cyhal_utils_peri_pclk_assign_divider(en_clk_dst_t clk_dest, const cyhal_clock_t *clock)
{
        return Cy_SysClk_PeriphAssignDivider(clk_dest, ((cy_en_divider_types_t)((clock->block) & 0x03)), clock->channel);
}
static inline uint32_t _cyhal_utils_peri_pclk_get_assigned_divider(en_clk_dst_t clk_dest)
{
        return Cy_SysClk_PeriphGetAssignedDivider(clk_dest);
}
static inline cy_rslt_t _cyhal_utils_peri_pclk_enable_divider(en_clk_dst_t clk_dest, const cyhal_clock_t *clock)
{
    ( (void)(clk_dest) );
    return Cy_SysClk_PeriphEnableDivider(((cy_en_divider_types_t)((clock->block) & 0x03)), clock->channel);
}
static inline cy_rslt_t _cyhal_utils_peri_pclk_disable_divider(en_clk_dst_t clk_dest, const cyhal_clock_t *clock)
{
    ( (void)(clk_dest) );
    return Cy_SysClk_PeriphDisableDivider(((cy_en_divider_types_t)((clock->block) & 0x03)), clock->channel);
}
static inline cy_rslt_t _cyhal_utils_peri_pclk_enable_phase_align_divider(en_clk_dst_t clk_dest, const cyhal_clock_t *clock, const cyhal_clock_t *clock2)
{
    ( (void)(clk_dest) );
    return Cy_SysClk_PeriphEnablePhaseAlignDivider(((cy_en_divider_types_t)((clock->block) & 0x03)), clock->channel,
                                                   ((cy_en_divider_types_t)((clock2->block) & 0x03)), clock2->channel);
}
static inline _Bool _cyhal_utils_peri_pclk_is_divider_enabled(en_clk_dst_t clk_dest, const cyhal_clock_t *clock)
{
    ( (void)(clk_dest) );
    return Cy_SysClk_PeriphGetDividerEnabled(((cy_en_divider_types_t)((clock->block) & 0x03)), clock->channel);
}
const cyhal_resource_pin_mapping_t *_cyhal_utils_get_resource(cyhal_gpio_t pin, const cyhal_resource_pin_mapping_t* mappings, size_t count, const cyhal_resource_inst_t* block_res, _Bool ignore_channel);
const cyhal_resource_pin_mapping_t* _cyhal_utils_try_alloc(cyhal_gpio_t pin, cyhal_resource_t rsc, const cyhal_resource_pin_mapping_t *pin_map, size_t count);
void _cyhal_utils_release_if_used(cyhal_gpio_t *pin);
static inline _Bool _cyhal_utils_resources_equal(const cyhal_resource_inst_t *resource1, const cyhal_resource_inst_t *resource2)
{
    return (resource1->type == resource2->type) && (resource1->block_num == resource2->block_num) && (resource1->channel_num == resource2->channel_num);
}
static inline _Bool _cyhal_utils_map_resource_equal(const cyhal_resource_inst_t *resource, const cyhal_resource_pin_mapping_t *map,
    _Bool ignore_channel)
{
    return (resource->block_num == map->block_num) && (ignore_channel || resource->channel_num == map->channel_num);
}
static inline _Bool _cyhal_utils_map_resources_equal(const cyhal_resource_pin_mapping_t *map1, const cyhal_resource_pin_mapping_t *map2)
{
    return (map1->block_num == map2->block_num) && (map1->channel_num == map2->channel_num);
}
_Bool _cyhal_utils_map_resources_equal_all(uint32_t count, ...);
uint32_t _cyhal_utils_convert_flags(const uint32_t map[], uint32_t count, uint32_t source_flags);
static inline void cyhal_gpio_write_internal(cyhal_gpio_t pin, _Bool value)
{
    Cy_GPIO_Write((Cy_GPIO_PortToAddr(((uint8_t)(((uint8_t)pin) >> 3U)))), ((uint8_t)(((uint8_t)pin) & 0x07U)), value);
}
static inline _Bool cyhal_gpio_read_internal(cyhal_gpio_t pin)
{
    return 0 != Cy_GPIO_Read((Cy_GPIO_PortToAddr(((uint8_t)(((uint8_t)pin) >> 3U)))), ((uint8_t)(((uint8_t)pin) & 0x07U)));
}
static inline void cyhal_gpio_toggle_internal(cyhal_gpio_t pin)
{
    Cy_GPIO_Inv((Cy_GPIO_PortToAddr(((uint8_t)(((uint8_t)pin) >> 3U)))), ((uint8_t)(((uint8_t)pin) & 0x07U)));
}

typedef enum
{
    CYHAL_TIMER_DIR_UP,
    CYHAL_TIMER_DIR_DOWN,
    CYHAL_TIMER_DIR_UP_DOWN,
} cyhal_timer_direction_t;
typedef enum {
    CYHAL_TIMER_IRQ_NONE = 0,
    CYHAL_TIMER_IRQ_TERMINAL_COUNT = 1 << 0,
    CYHAL_TIMER_IRQ_CAPTURE_COMPARE = 1 << 1,
    CYHAL_TIMER_IRQ_ALL = (1 << 2) - 1,
} cyhal_timer_event_t;
typedef enum
{
    CYHAL_TIMER_INPUT_START,
    CYHAL_TIMER_INPUT_STOP,
    CYHAL_TIMER_INPUT_RELOAD,
    CYHAL_TIMER_INPUT_COUNT,
    CYHAL_TIMER_INPUT_CAPTURE,
} cyhal_timer_input_t;
typedef enum
{
    CYHAL_TIMER_OUTPUT_OVERFLOW,
    CYHAL_TIMER_OUTPUT_UNDERFLOW,
    CYHAL_TIMER_OUTPUT_COMPARE_MATCH,
    CYHAL_TIMER_OUTPUT_TERMINAL_COUNT,
} cyhal_timer_output_t;
typedef struct
{
    _Bool is_continuous;
    cyhal_timer_direction_t direction;
    _Bool is_compare;
    uint32_t period;
    uint32_t compare_value;
    uint32_t value;
} cyhal_timer_cfg_t;
typedef void(*cyhal_timer_event_callback_t)(void *callback_arg, cyhal_timer_event_t event);
cy_rslt_t cyhal_timer_init(cyhal_timer_t *obj, cyhal_gpio_t pin, const cyhal_clock_t *clk);
 cy_rslt_t cyhal_timer_init_cfg(cyhal_timer_t *obj, const cyhal_timer_configurator_t *cfg);
void cyhal_timer_free(cyhal_timer_t *obj);
cy_rslt_t cyhal_timer_configure(cyhal_timer_t *obj, const cyhal_timer_cfg_t *cfg);
cy_rslt_t cyhal_timer_set_frequency(cyhal_timer_t *obj, uint32_t hz);
cy_rslt_t cyhal_timer_start(cyhal_timer_t *obj);
cy_rslt_t cyhal_timer_stop(cyhal_timer_t *obj);
cy_rslt_t cyhal_timer_reset(cyhal_timer_t *obj);
uint32_t cyhal_timer_read(const cyhal_timer_t *obj);
void cyhal_timer_register_callback(cyhal_timer_t *obj, cyhal_timer_event_callback_t callback, void *callback_arg);
void cyhal_timer_enable_event(cyhal_timer_t *obj, cyhal_timer_event_t event, uint8_t intr_priority, _Bool enable);
cy_rslt_t cyhal_timer_connect_digital(cyhal_timer_t *obj, cyhal_source_t source, cyhal_timer_input_t signal);
cy_rslt_t cyhal_timer_connect_digital2(cyhal_timer_t *obj, cyhal_source_t source, cyhal_timer_input_t signal, cyhal_edge_type_t edge_type);
cy_rslt_t cyhal_timer_enable_output(cyhal_timer_t *obj, cyhal_timer_output_t signal, cyhal_source_t *source);
cy_rslt_t cyhal_timer_disconnect_digital(cyhal_timer_t *obj, cyhal_source_t source, cyhal_timer_input_t signal);
cy_rslt_t cyhal_timer_disable_output(cyhal_timer_t *obj, cyhal_timer_output_t signal);

cy_rslt_t cyhal_connect_pin(const cyhal_resource_pin_mapping_t *pin_connection, uint8_t drive_mode);
cy_rslt_t cyhal_disconnect_pin(cyhal_gpio_t pin);

cy_rslt_t _cyhal_connect_signal(cyhal_source_t source, cyhal_dest_t dest);
cy_rslt_t _cyhal_disconnect_signal(cyhal_source_t source, cyhal_dest_t dest);
_Bool _cyhal_can_connect_signal(cyhal_source_t source, cyhal_dest_t dest);
    extern const uint16_t _CYHAL_TCPWM_TRIGGER_INPUTS_IDX_OFFSET[1];
    extern const uint16_t _CYHAL_TCPWM_TRIGGER_INPUTS_PER_BLOCK[1];
typedef enum
{
    CYHAL_TCPWM_INPUT_START,
    CYHAL_TCPWM_INPUT_STOP,
    CYHAL_TCPWM_INPUT_RELOAD,
    CYHAL_TCPWM_INPUT_COUNT,
    CYHAL_TCPWM_INPUT_CAPTURE,
} cyhal_tcpwm_input_t;
typedef enum
{
    CYHAL_TCPWM_OUTPUT_OVERFLOW,
    CYHAL_TCPWM_OUTPUT_UNDERFLOW,
    CYHAL_TCPWM_OUTPUT_COMPARE_MATCH,
    CYHAL_TCPWM_OUTPUT_TERMINAL_COUNT,
    CYHAL_TCPWM_OUTPUT_LINE_OUT,
} cyhal_tcpwm_output_t;
typedef void(*_cyhal_tcpwm_event_callback_t)(void *callback_arg, int event);
typedef struct {
    TCPWM_Type* base;
    en_clk_dst_t clock_dst;
    uint32_t max_count;
    uint8_t num_channels;
    uint8_t channel_offset;
    uint8_t isr_offset;
} _cyhal_tcpwm_data_t;
extern const _cyhal_tcpwm_data_t _CYHAL_TCPWM_DATA[2u];
void _cyhal_tcpwm_free(cyhal_tcpwm_t *obj);
void _cyhal_tcpwm_init_data(cyhal_tcpwm_t *tcpwm);
void _cyhal_tcpwm_register_callback(cyhal_resource_inst_t *resource, cy_israddress callback, void *callback_arg);
void _cyhal_tcpwm_enable_event(cyhal_tcpwm_t *tcpwm, cyhal_resource_inst_t *resource, uint32_t event, uint8_t intr_priority, _Bool enable);
_Bool _cyhal_tcpwm_pm_transition_pending(void);
cy_rslt_t _cyhal_tcpwm_connect_digital(cyhal_tcpwm_t *obj, cyhal_source_t source, cyhal_tcpwm_input_t signal, cyhal_edge_type_t type);
cy_rslt_t _cyhal_tcpwm_enable_output(cyhal_tcpwm_t *obj, cyhal_tcpwm_output_t signal, cyhal_source_t *source);
cy_rslt_t _cyhal_tcpwm_disconnect_digital(cyhal_tcpwm_t *obj, cyhal_source_t source, cyhal_tcpwm_input_t signal);
cy_rslt_t _cyhal_tcpwm_disable_output(cyhal_tcpwm_t *obj, cyhal_tcpwm_output_t signal);
cyhal_dest_t _cyhal_tpwm_calculate_dest(uint8_t block, uint8_t trig_index);
static inline uint32_t _cyhal_timer_convert_event(cyhal_timer_event_t event)
{
    uint32_t pdl_event = 0U;
    if (event & CYHAL_TIMER_IRQ_TERMINAL_COUNT)
    {
        pdl_event |= (1U);
    }
    if (event & CYHAL_TIMER_IRQ_CAPTURE_COMPARE)
    {
        pdl_event |= (2U);
    }
    return pdl_event;
}
static inline void _cyhal_timer_free(cyhal_timer_t *obj)
{
    _cyhal_tcpwm_free(&obj->tcpwm);
}
static inline void cyhal_timer_register_callback_internal(cyhal_timer_t *obj, cyhal_timer_event_callback_t callback, void *callback_arg)
{
    _cyhal_tcpwm_register_callback(&obj->tcpwm.resource, (cy_israddress) callback, callback_arg);
}
static inline void cyhal_timer_enable_event_internal(cyhal_timer_t *obj, cyhal_timer_event_t event, uint8_t intr_priority, _Bool enable)
{
    uint32_t converted = _cyhal_timer_convert_event(event);
    _cyhal_tcpwm_enable_event(&obj->tcpwm, &obj->tcpwm.resource, converted, intr_priority, enable);
}
cy_rslt_t sb17_intialize_isr_timer(cyhal_timer_t* data_transfer_timer_obj,
                                   void (*isr)(void* callback_arg, cyhal_timer_event_t event), uint32_t freq);
cy_rslt_t sb17_initialize_timestamp_timer(cyhal_timer_t* timer);
cy_rslt_t sb17_start_timer(cyhal_timer_t* timer);
cy_rslt_t sb17_stop_timer(cyhal_timer_t* timer);
static SB17_SENSOR_DATA_t _sb17_read_single_sensor_value();
static uint8_t _sb17_retrieve_sensor_id(uint16_t buf);
static uint8_t _sb17_retrieve_direction(uint16_t buf);
static uint8_t _sb17_retrieve_gain(uint16_t buf);
static uint16_t _sb17_retrieve_value(uint16_t buf);
static uint8_t _sb17_retrieve_spi_version(uint8_t buf);
static uint8_t _sb17_retrieve_spi_revision(uint8_t buf);
static uint16_t _sb17_retrieve_chip_id(uint8_t upper, uint8_t lower);
static uint8_t _sb17_retrieve_chip_revision(uint8_t buf);
static void _sb17_set_settle_time();
void (*_sb_17_publish_sensor_data)(SB17_SENSOR_READING_t readings[4]);
cy_rslt_t sb17_initialize_spi(void (*publish_data)(SB17_SENSOR_READING_t readings[4]))
{
    cyhal_spi_init(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int(),
                   __VERIFIER_nondet_int(), __VERIFIER_nondet_int(), __VERIFIER_nondet_pointer(),
                   __VERIFIER_nondet_uint(), __VERIFIER_nondet_int(), __VERIFIER_nondet_bool());
    cyhal_spi_set_frequency(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint());
    cyhal_gpio_init(__VERIFIER_nondet_int(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int(),
                    __VERIFIER_nondet_bool());
    sb17_initialize_timestamp_timer(__VERIFIER_nondet_pointer());
    sb17_start_timer(__VERIFIER_nondet_pointer());
    _sb17_set_settle_time();
    _sb_17_publish_sensor_data = publish_data;
    return __VERIFIER_nondet_uint();
}
cy_rslt_t sb17_spi_read_chip_data(SB17_CHIP_DATA_t* chip_data)
{
    cyhal_gpio_write_internal(__VERIFIER_nondet_int(), __VERIFIER_nondet_bool());
    cyhal_spi_transfer(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(),
                       __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(), __VERIFIER_nondet_char());
    cyhal_gpio_write_internal(__VERIFIER_nondet_int(), __VERIFIER_nondet_bool());
    for (int i = 1; i < __VERIFIER_nondet_uint(); ++i) {
        __asm volatile ("nop");
    }
    _sb17_retrieve_spi_version(__VERIFIER_nondet_char());
    _sb17_retrieve_spi_revision(__VERIFIER_nondet_char());
    _sb17_retrieve_chip_id(__VERIFIER_nondet_char(), __VERIFIER_nondet_char());
    _sb17_retrieve_chip_revision(__VERIFIER_nondet_char());
    return __VERIFIER_nondet_uint();
}
void sb17_spi_read_all_data()
{
    sb17_spi_read_continous_range(__VERIFIER_nondet_char(), __VERIFIER_nondet_char(), __VERIFIER_nondet_bool());
}
void sb17_spi_read_single_data(uint8_t sensor_id)
{
    sb17_spi_read_continous_range(__VERIFIER_nondet_char(), __VERIFIER_nondet_char(), __VERIFIER_nondet_bool());
}
void sb17_spi_read_continous_range(uint8_t start_id, uint8_t end_id, _Bool range_readout)
{
    if (__VERIFIER_nondet_bool()) {
        __asm volatile ("nop");
    }
    cyhal_gpio_write_internal(__VERIFIER_nondet_int(), __VERIFIER_nondet_bool());
    cyhal_spi_transfer(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(),
                       __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(), __VERIFIER_nondet_char());
    for (int i = 0; i < __VERIFIER_nondet_uint(); i++) {
        for (int c = 0; c < 4; c++) {
            _sb17_read_single_sensor_value();
            cyhal_timer_read(__VERIFIER_nondet_pointer());
            Cy_SysLib_EnterCriticalSection();
            Cy_SysLib_ExitCriticalSection(__VERIFIER_nondet_uint());
        }
        _sb_17_publish_sensor_data(__VERIFIER_nondet_pointer());
    }
    cyhal_gpio_write_internal(__VERIFIER_nondet_int(), __VERIFIER_nondet_bool());
}
SB17_SENSOR_DATA_t _sb17_read_single_sensor_value()
{
    while (__VERIFIER_nondet_bool()) {
        cyhal_spi_transfer(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(),
                           __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(), __VERIFIER_nondet_char());
    }
    _sb17_retrieve_sensor_id(__VERIFIER_nondet_short());
    _sb17_retrieve_direction(__VERIFIER_nondet_short());
    while (__VERIFIER_nondet_bool()) {
        cyhal_spi_transfer(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(),
                           __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(), __VERIFIER_nondet_char());
    }
    _sb17_retrieve_value(__VERIFIER_nondet_short());
    _sb17_retrieve_gain(__VERIFIER_nondet_short());
    SB17_SENSOR_DATA_t data;
    return data;
}
static uint8_t _sb17_retrieve_spi_version(uint8_t buf)
{
    return __VERIFIER_nondet_uchar();
}
static uint8_t _sb17_retrieve_spi_revision(uint8_t buf)
{
    return __VERIFIER_nondet_uchar();
}
static uint16_t _sb17_retrieve_chip_id(uint8_t upper, uint8_t lower)
{
    return __VERIFIER_nondet_ushort();
}
static uint8_t _sb17_retrieve_chip_revision(uint8_t buf)
{
    return __VERIFIER_nondet_uchar();
}
static uint8_t _sb17_retrieve_sensor_id(uint16_t buf)
{
    return __VERIFIER_nondet_uchar();
}
static uint8_t _sb17_retrieve_direction(uint16_t buf)
{
    return __VERIFIER_nondet_uchar();
}
static uint8_t _sb17_retrieve_gain(uint16_t buf)
{
    return __VERIFIER_nondet_uchar();
}
static uint16_t _sb17_retrieve_value(uint16_t buf)
{
    return __VERIFIER_nondet_uchar();
}
static void _sb17_set_settle_time()
{
    cyhal_gpio_write_internal(__VERIFIER_nondet_int(), __VERIFIER_nondet_bool());
    cyhal_spi_transfer(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(),
                       __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(), __VERIFIER_nondet_char());
    cyhal_gpio_write_internal(__VERIFIER_nondet_int(), __VERIFIER_nondet_bool());
}
cy_rslt_t sb17_initialize_uart();
cy_rslt_t sb17_uart_read_data(uint8_t *buffer, size_t length);
cy_rslt_t sb17_uart_send_data(uint8_t *buffer, size_t length);
uint32_t sb17_uart_readable();
cy_rslt_t sb17_uart_getc(uint8_t *value);
void sb17_uart_handler_tx_done();
void sb17_uart_handler_rx_not_empty();

typedef struct
{
  int quot;
  int rem;
} div_t;
typedef struct
{
  long quot;
  long rem;
} ldiv_t;
typedef struct
{
  long long int quot;
  long long int rem;
} lldiv_t;
typedef int (*__compar_fn_t) (const void *, const void *);
int __locale_mb_cur_max (void);
void abort (void) __attribute__ ((__noreturn__));
int abs (int);
__uint32_t arc4random (void);
__uint32_t arc4random_uniform (__uint32_t);
void arc4random_buf (void *, size_t);
int atexit (void (*__func)(void));
double atof (const char *__nptr);
float atoff (const char *__nptr);
int atoi (const char *__nptr);
int _atoi_r (struct _reent *, const char *__nptr);
long atol (const char *__nptr);
long _atol_r (struct _reent *, const char *__nptr);
void * bsearch (const void *__key,
         const void *__base,
         size_t __nmemb,
         size_t __size,
         __compar_fn_t _compar);
void *calloc(size_t, size_t) __attribute__((__malloc__)) __attribute__((__warn_unused_result__))
      __attribute__((__alloc_size__(1, 2))) ;
div_t div (int __numer, int __denom);
void exit (int __status) __attribute__ ((__noreturn__));
void free (void *) ;
char * getenv (const char *__string);
char * _getenv_r (struct _reent *, const char *__string);
char * _findenv (const char *, int *);
char * _findenv_r (struct _reent *, const char *, int *);
extern char *suboptarg;
int getsubopt (char **, char * const *, char **);
long labs (long);
ldiv_t ldiv (long __numer, long __denom);
void *malloc(size_t) __attribute__((__malloc__)) __attribute__((__warn_unused_result__)) __attribute__((__alloc_size__(1))) ;
int mblen (const char *, size_t);
int _mblen_r (struct _reent *, const char *, size_t, _mbstate_t *);
int mbtowc (wchar_t *restrict, const char *restrict, size_t);
int _mbtowc_r (struct _reent *, wchar_t *restrict, const char *restrict, size_t, _mbstate_t *);
int wctomb (char *, wchar_t);
int _wctomb_r (struct _reent *, char *, wchar_t, _mbstate_t *);
size_t mbstowcs (wchar_t *restrict, const char *restrict, size_t);
size_t _mbstowcs_r (struct _reent *, wchar_t *restrict, const char *restrict, size_t, _mbstate_t *);
size_t wcstombs (char *restrict, const wchar_t *restrict, size_t);
size_t _wcstombs_r (struct _reent *, char *restrict, const wchar_t *restrict, size_t, _mbstate_t *);
char * mkdtemp (char *);
int mkstemp (char *);
int mkstemps (char *, int);
char * mktemp (char *) __attribute__ ((__deprecated__("the use of `mktemp' is dangerous; use `mkstemp' instead")));
char * _mkdtemp_r (struct _reent *, char *);
int _mkostemp_r (struct _reent *, char *, int);
int _mkostemps_r (struct _reent *, char *, int, int);
int _mkstemp_r (struct _reent *, char *);
int _mkstemps_r (struct _reent *, char *, int);
char * _mktemp_r (struct _reent *, char *) __attribute__ ((__deprecated__("the use of `mktemp' is dangerous; use `mkstemp' instead")));
void qsort (void *__base, size_t __nmemb, size_t __size, __compar_fn_t _compar);
int rand (void);
void *realloc(void *, size_t) __attribute__((__warn_unused_result__)) __attribute__((__alloc_size__(2))) ;
void *reallocarray(void *, size_t, size_t) __attribute__((__warn_unused_result__)) __attribute__((__alloc_size__(2, 3)));
void *reallocf(void *, size_t) __attribute__((__warn_unused_result__)) __attribute__((__alloc_size__(2)));
char * realpath (const char *restrict path, char *restrict resolved_path);
int rpmatch (const char *response);
void srand (unsigned __seed);
double strtod (const char *restrict __n, char **restrict __end_PTR);
double _strtod_r (struct _reent *,const char *restrict __n, char **restrict __end_PTR);
float strtof (const char *restrict __n, char **restrict __end_PTR);
long strtol (const char *restrict __n, char **restrict __end_PTR, int __base);
long _strtol_r (struct _reent *,const char *restrict __n, char **restrict __end_PTR, int __base);
unsigned long strtoul (const char *restrict __n, char **restrict __end_PTR, int __base);
unsigned long _strtoul_r (struct _reent *,const char *restrict __n, char **restrict __end_PTR, int __base);
int system (const char *__string);
long a64l (const char *__input);
char * l64a (long __input);
char * _l64a_r (struct _reent *,long __input);
int on_exit (void (*__func)(int, void *),void *__arg);
void _Exit (int __status) __attribute__ ((__noreturn__));
int putenv (char *__string);
int _putenv_r (struct _reent *, char *__string);
void * _reallocf_r (struct _reent *, void *, size_t);
int setenv (const char *__string, const char *__value, int __overwrite);
int _setenv_r (struct _reent *, const char *__string, const char *__value, int __overwrite);
char * __itoa (int, char *, int);
char * __utoa (unsigned, char *, int);
char * itoa (int, char *, int);
char * utoa (unsigned, char *, int);
int rand_r (unsigned *__seed);
double drand48 (void);
double _drand48_r (struct _reent *);
double erand48 (unsigned short [3]);
double _erand48_r (struct _reent *, unsigned short [3]);
long jrand48 (unsigned short [3]);
long _jrand48_r (struct _reent *, unsigned short [3]);
void lcong48 (unsigned short [7]);
void _lcong48_r (struct _reent *, unsigned short [7]);
long lrand48 (void);
long _lrand48_r (struct _reent *);
long mrand48 (void);
long _mrand48_r (struct _reent *);
long nrand48 (unsigned short [3]);
long _nrand48_r (struct _reent *, unsigned short [3]);
unsigned short *
       seed48 (unsigned short [3]);
unsigned short *
       _seed48_r (struct _reent *, unsigned short [3]);
void srand48 (long);
void _srand48_r (struct _reent *, long);
char * initstate (unsigned, char *, size_t);
long random (void);
char * setstate (char *);
void srandom (unsigned);
long long atoll (const char *__nptr);
long long _atoll_r (struct _reent *, const char *__nptr);
long long llabs (long long);
lldiv_t lldiv (long long __numer, long long __denom);
long long strtoll (const char *restrict __n, char **restrict __end_PTR, int __base);
long long _strtoll_r (struct _reent *, const char *restrict __n, char **restrict __end_PTR, int __base);
unsigned long long strtoull (const char *restrict __n, char **restrict __end_PTR, int __base);
unsigned long long _strtoull_r (struct _reent *, const char *restrict __n, char **restrict __end_PTR, int __base);
void cfree (void *);
int unsetenv (const char *__string);
int _unsetenv_r (struct _reent *, const char *__string);
int posix_memalign (void **, size_t, size_t) __attribute__((__nonnull__ (1)))
     __attribute__((__warn_unused_result__));
char * _dtoa_r (struct _reent *, double, int, int, int *, int*, char**);
void * _malloc_r (struct _reent *, size_t) ;
void * _calloc_r (struct _reent *, size_t, size_t) ;
void _free_r (struct _reent *, void *) ;
void * _realloc_r (struct _reent *, void *, size_t) ;
void _mstats_r (struct _reent *, char *);
int _system_r (struct _reent *, const char *);
void __eprintf (const char *, const char *, unsigned int, const char *);
void qsort_r (void *__base, size_t __nmemb, size_t __size, void *__thunk, int (*_compar)(void *, const void *, const void *))
             __asm__ ("" "__bsd_qsort_r");
extern long double _strtold_r (struct _reent *, const char *restrict, char **restrict);
extern long double strtold (const char *restrict, char **restrict);
void * aligned_alloc(size_t, size_t) __attribute__((__malloc__)) __attribute__((__alloc_align__(1)))
     __attribute__((__alloc_size__(2))) __attribute__((__warn_unused_result__));
int at_quick_exit(void (*)(void));
_Noreturn void
 quick_exit(int);

static void _sb17_uart_event_handler(void *handler_arg, cyhal_uart_event_t event);
cy_rslt_t sb17_initialize_uart()
{
    cyhal_uart_init(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int(),
                    __VERIFIER_nondet_int(), __VERIFIER_nondet_int(), __VERIFIER_nondet_pointer(),
                    __VERIFIER_nondet_pointer());
    cyhal_uart_set_baud(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(), __VERIFIER_nondet_pointer());
    cyhal_uart_set_async_mode(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_int(), __VERIFIER_nondet_int());
    cyhal_uart_clear(__VERIFIER_nondet_pointer());
    cyhal_uart_register_callback(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer());
    cyhal_uart_enable_event(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint(), __VERIFIER_nondet_uint(),
                            __VERIFIER_nondet_bool());
    return __VERIFIER_nondet_uint();
}
cy_rslt_t sb17_uart_read_data(uint8_t *buffer, size_t length)
{
    {
        cyhal_uart_read_async(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer, __VERIFIER_nondet_size_t());
    }
    return __VERIFIER_nondet_uint();
}
cy_rslt_t sb17_uart_send_data(uint8_t *buffer, size_t length)
{
    {
        cyhal_uart_write_async(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
    }
    return __VERIFIER_nondet_uint();
}
uint32_t sb17_uart_readable()
{
    return cyhal_uart_readable(__VERIFIER_nondet_pointer());
}
cy_rslt_t sb17_uart_getc(uint8_t *value)
{
    return cyhal_uart_getc(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint());
}
static void _sb17_uart_event_handler(void *handler_arg, cyhal_uart_event_t event)
{
    (void)handler_arg;
    if (__VERIFIER_nondet_bool()) {
        sb17_uart_handler_tx_done();
    } else if (__VERIFIER_nondet_bool()) {
        sb17_uart_handler_rx_not_empty();
    }
}
cy_rslt_t sb17_intialize_isr_timer(cyhal_timer_t* timer, void (*isr)(void* callback_arg, cyhal_timer_event_t event),
                                   uint32_t freq)
{
    cyhal_timer_init(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_int(), __VERIFIER_nondet_pointer());
    cyhal_timer_configure(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer());
    cyhal_timer_set_frequency(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint());
    cyhal_timer_register_callback_internal(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer());
    cyhal_timer_enable_event_internal(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_int(), __VERIFIER_nondet_uint(), __VERIFIER_nondet_bool());
    return __VERIFIER_nondet_uint();
}
cy_rslt_t sb17_initialize_timestamp_timer(cyhal_timer_t* timer)
{
    cyhal_timer_init(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_int(), __VERIFIER_nondet_pointer());
    cyhal_timer_configure(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer());
    cyhal_timer_set_frequency(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint());
    return __VERIFIER_nondet_uint();
}
cy_rslt_t sb17_start_timer(cyhal_timer_t* timer)
{
    return cyhal_timer_start(__VERIFIER_nondet_pointer());
}
cy_rslt_t sb17_stop_timer(cyhal_timer_t* timer)
{
    cyhal_timer_stop(__VERIFIER_nondet_pointer());
    _cyhal_timer_free(__VERIFIER_nondet_pointer());
    return __VERIFIER_nondet_uint();
}
cy_rslt_t sb17_initialize_messenger(void);
cy_rslt_t sb17_messenger_send_data(uint8_t *const tx_buffer, size_t length);
_Bool sb17_messenger_transfer_sensor_data(void);
cy_rslt_t sb17_initialize_messenger(void)
{
    fs3d_slip_decode_init(__VERIFIER_nondet_pointer());
    return sb17_initialize_uart();
}
cy_rslt_t sb17_messenger_send_data(uint8_t *const tx_buffer, size_t length)
{
    fs3d_slip_encode(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                     __VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
    return sb17_uart_send_data(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
}
static _Bool _sb17_messenger_process_data(uint8_t *const buf, size_t len)
{
    if (fs3d_packet_decode(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t())) {
        fs3d_msg_process(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(), __VERIFIER_nondet_pointer(),
                         __VERIFIER_nondet_size_t());
    } else {
        fs3d_rsp_code_send_transfer_failed(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
    }
    return __VERIFIER_nondet_bool();
}
_Bool sb17_messenger_transfer_sensor_data(void)
{
    Cy_SysLib_EnterCriticalSection();
    fs3d_transfer_sensor_data(__VERIFIER_nondet_bool(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
    Cy_SysLib_ExitCriticalSection(__VERIFIER_nondet_uint());
    return __VERIFIER_nondet_bool();
}
void sb17_uart_handler_tx_done()
{
}
void sb17_uart_handler_rx_not_empty()
{
    sb17_uart_readable(); if (__VERIFIER_nondet_bool()) {
        if (sb17_uart_getc(__VERIFIER_nondet_pointer()) == ((cy_rslt_t)0x00000000U)) {
            fs3d_slip_decode_chr(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t(),
                                 __VERIFIER_nondet_uchar());
        } else {
        }
    }
}
void fs3d_slip_cb_decode_complete(uint8_t *const buf, size_t len)
{
    _sb17_messenger_process_data(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
}
typedef enum
  {
    memory_order_relaxed = 0,
    memory_order_consume = 1,
    memory_order_acquire = 2,
    memory_order_release = 3,
    memory_order_acq_rel = 4,
    memory_order_seq_cst = 5
  } memory_order;
typedef _Atomic _Bool atomic_bool;
typedef _Atomic char atomic_char;
typedef _Atomic signed char atomic_schar;
typedef _Atomic unsigned char atomic_uchar;
typedef _Atomic short atomic_short;
typedef _Atomic unsigned short atomic_ushort;
typedef _Atomic int atomic_int;
typedef _Atomic unsigned int atomic_uint;
typedef _Atomic long atomic_long;
typedef _Atomic unsigned long atomic_ulong;
typedef _Atomic long long atomic_llong;
typedef _Atomic unsigned long long atomic_ullong;
typedef _Atomic short unsigned int atomic_char16_t;
typedef _Atomic long unsigned int atomic_char32_t;
typedef _Atomic unsigned int atomic_wchar_t;
typedef _Atomic signed char atomic_int_least8_t;
typedef _Atomic unsigned char atomic_uint_least8_t;
typedef _Atomic short int atomic_int_least16_t;
typedef _Atomic short unsigned int atomic_uint_least16_t;
typedef _Atomic long int atomic_int_least32_t;
typedef _Atomic long unsigned int atomic_uint_least32_t;
typedef _Atomic long long int atomic_int_least64_t;
typedef _Atomic long long unsigned int atomic_uint_least64_t;
typedef _Atomic int atomic_int_fast8_t;
typedef _Atomic unsigned int atomic_uint_fast8_t;
typedef _Atomic int atomic_int_fast16_t;
typedef _Atomic unsigned int atomic_uint_fast16_t;
typedef _Atomic int atomic_int_fast32_t;
typedef _Atomic unsigned int atomic_uint_fast32_t;
typedef _Atomic long long int atomic_int_fast64_t;
typedef _Atomic long long unsigned int atomic_uint_fast64_t;
typedef _Atomic int atomic_intptr_t;
typedef _Atomic unsigned int atomic_uintptr_t;
typedef _Atomic unsigned int atomic_size_t;
typedef _Atomic int atomic_ptrdiff_t;
typedef _Atomic long long int atomic_intmax_t;
typedef _Atomic long long unsigned int atomic_uintmax_t;
extern void atomic_thread_fence (memory_order);
extern void atomic_signal_fence (memory_order);
typedef _Atomic struct
{
  _Bool __val;
} atomic_flag;
extern _Bool atomic_flag_test_and_set (volatile atomic_flag *);
extern _Bool atomic_flag_test_and_set_explicit (volatile atomic_flag *,
      memory_order);
extern void atomic_flag_clear (volatile atomic_flag *);
extern void atomic_flag_clear_explicit (volatile atomic_flag *, memory_order);
cy_rslt_t sb17_initialize_sensor_readout(SB17_CHIP_DATA_t* chip_data, SB17_CHIP_CONFIG_t* config,
                                         void (*publish_data)(SB17_SENSOR_READING_t readings[4]));
cy_rslt_t sb17_reconfigure_sensor_readout(SB17_CHIP_CONFIG_t* config);
void sb17_calculate_sensors_to_read(SB17_CHIP_CONFIG_t* config);
cy_rslt_t sb17_read_sensor_data();
uint32_t sb17_measure_time(SENSOR_READINGS_t readings, _Bool single_data);
static void _sb17_readout_timer_isr(void* callback_arg, cyhal_timer_event_t event);
static cy_rslt_t _sb17_sanity_check(SB17_CHIP_DATA_t* chip_data);
cy_rslt_t sb17_initialize_sensor_readout(SB17_CHIP_DATA_t* chip_data, SB17_CHIP_CONFIG_t* config,
                                         void (*publish_data)(SB17_SENSOR_READING_t readings[4]))
{
    sb17_initialize_spi(publish_data);
    sb17_spi_read_chip_data(__VERIFIER_nondet_pointer());
    _sb17_sanity_check(__VERIFIER_nondet_pointer());
    sb17_intialize_isr_timer(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint());
    sb17_calculate_sensors_to_read(__VERIFIER_nondet_pointer());
    sb17_start_timer(__VERIFIER_nondet_pointer());
    return __VERIFIER_nondet_uint();
}
cy_rslt_t sb17_reconfigure_sensor_readout(SB17_CHIP_CONFIG_t* config)
{
    sb17_stop_timer(__VERIFIER_nondet_pointer());
    sb17_intialize_isr_timer(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint());
    return sb17_start_timer(__VERIFIER_nondet_pointer());
}
void sb17_calculate_sensors_to_read(SB17_CHIP_CONFIG_t* config)
{
    for (int i = 0; i < 32; i++) {
        if (__VERIFIER_nondet_bool()) {
            if (__VERIFIER_nondet_bool()) {
                __asm volatile ("nop");
            } else {
                __asm volatile ("nop");
            }
        } else {
            if (__VERIFIER_nondet_bool()) {
                __asm volatile ("nop");
            }
        }
    }
    if (__VERIFIER_nondet_bool()) {
        __asm volatile ("nop");
    }
}
cy_rslt_t sb17_read_sensor_data()
{
    for (int i = 0; i < 32 / 2; i++) {
        if (__VERIFIER_nondet_bool()) {
            if (__VERIFIER_nondet_bool()) {
                sb17_spi_read_single_data(__VERIFIER_nondet_uint());
            } else {
                sb17_spi_read_continous_range(__VERIFIER_nondet_uint(), __VERIFIER_nondet_uint(),
                                              __VERIFIER_nondet_bool());
            }
        } else {
            break;
        }
    }
    return __VERIFIER_nondet_uint();
}
static void _sb17_readout_timer_isr(void* callback_arg, cyhal_timer_event_t event)
{
    return;
}
static cy_rslt_t _sb17_sanity_check(SB17_CHIP_DATA_t* chip_data)
{
    for (int i = 0; i < __VERIFIER_nondet_uint(); i++) {
        __asm volatile ("nop");
    }
    return __VERIFIER_nondet_uint();
}
typedef __uint8_t u_int8_t;
typedef __uint16_t u_int16_t;
typedef __uint32_t u_int32_t;
typedef __uint64_t u_int64_t;
typedef __intptr_t register_t;
typedef unsigned long __sigset_t;
typedef __suseconds_t suseconds_t;
typedef __int_least64_t time_t;
struct timeval {
 time_t tv_sec;
 suseconds_t tv_usec;
};
struct timespec {
 time_t tv_sec;
 long tv_nsec;
};
struct itimerspec {
 struct timespec it_interval;
 struct timespec it_value;
};
typedef __sigset_t sigset_t;
typedef unsigned long __fd_mask;
typedef __fd_mask fd_mask;
typedef struct fd_set {
 __fd_mask __fds_bits[(((64) + ((((int)sizeof(__fd_mask) * 8)) - 1)) / (((int)sizeof(__fd_mask) * 8)))];
} fd_set;

int select (int __n, fd_set *__readfds, fd_set *__writefds, fd_set *__exceptfds, struct timeval *__timeout);
int pselect (int __n, fd_set *__readfds, fd_set *__writefds, fd_set *__exceptfds, const struct timespec *__timeout, const sigset_t *__set);

typedef __uint32_t in_addr_t;
typedef __uint16_t in_port_t;
typedef __uintptr_t u_register_t;
typedef unsigned char u_char;
typedef unsigned short u_short;
typedef unsigned int u_int;
typedef unsigned long u_long;
typedef unsigned short ushort;
typedef unsigned int uint;
typedef unsigned long ulong;
typedef __blkcnt_t blkcnt_t;
typedef __blksize_t blksize_t;
typedef unsigned long clock_t;
typedef __daddr_t daddr_t;
typedef char * caddr_t;
typedef __fsblkcnt_t fsblkcnt_t;
typedef __fsfilcnt_t fsfilcnt_t;
typedef __id_t id_t;
typedef __ino_t ino_t;
typedef __off_t off_t;
typedef __dev_t dev_t;
typedef __uid_t uid_t;
typedef __gid_t gid_t;
typedef __pid_t pid_t;
typedef __key_t key_t;
typedef _ssize_t ssize_t;
typedef __mode_t mode_t;
typedef __nlink_t nlink_t;
typedef __clockid_t clockid_t;
typedef __timer_t timer_t;
typedef __useconds_t useconds_t;
typedef __int64_t sbintime_t;
struct sched_param {
  int sched_priority;
};
typedef __uint32_t pthread_t;
typedef struct {
  int is_initialized;
  void *stackaddr;
  int stacksize;
  int contentionscope;
  int inheritsched;
  int schedpolicy;
  struct sched_param schedparam;
  int detachstate;
} pthread_attr_t;
typedef __uint32_t pthread_mutex_t;
typedef struct {
  int is_initialized;
  int recursive;
} pthread_mutexattr_t;
typedef __uint32_t pthread_cond_t;
typedef struct {
  int is_initialized;
  clock_t clock;
} pthread_condattr_t;
typedef __uint32_t pthread_key_t;
typedef struct {
  int is_initialized;
  int init_executed;
} pthread_once_t;
extern char **environ;
void _exit (int __status) __attribute__ ((__noreturn__));
int access (const char *__path, int __amode);
unsigned alarm (unsigned __secs);
int chdir (const char *__path);
int chmod (const char *__path, mode_t __mode);
int chown (const char *__path, uid_t __owner, gid_t __group);
int chroot (const char *__path);
int close (int __fildes);
size_t confstr (int __name, char *__buf, size_t __len);
int daemon (int nochdir, int noclose);
int dup (int __fildes);
int dup2 (int __fildes, int __fildes2);
void endusershell (void);
int execl (const char *__path, const char *, ...);
int execle (const char *__path, const char *, ...);
int execlp (const char *__file, const char *, ...);
int execlpe (const char *__file, const char *, ...);
int execv (const char *__path, char * const __argv[]);
int execve (const char *__path, char * const __argv[], char * const __envp[]);
int execvp (const char *__file, char * const __argv[]);
int faccessat (int __dirfd, const char *__path, int __mode, int __flags);
int fchdir (int __fildes);
int fchmod (int __fildes, mode_t __mode);
int fchown (int __fildes, uid_t __owner, gid_t __group);
int fchownat (int __dirfd, const char *__path, uid_t __owner, gid_t __group, int __flags);
int fexecve (int __fd, char * const __argv[], char * const __envp[]);
pid_t fork (void);
long fpathconf (int __fd, int __name);
int fsync (int __fd);
int fdatasync (int __fd);
char * getcwd (char *__buf, size_t __size);
int getdomainname (char *__name, size_t __len);
int getentropy (void *, size_t);
gid_t getegid (void);
uid_t geteuid (void);
gid_t getgid (void);
int getgroups (int __gidsetsize, gid_t __grouplist[]);
long gethostid (void);
char * getlogin (void);
char * getpass (const char *__prompt);
int getpagesize (void);
int getpeereid (int, uid_t *, gid_t *);
pid_t getpgid (pid_t);
pid_t getpgrp (void);
pid_t getpid (void);
pid_t getppid (void);
pid_t getsid (pid_t);
uid_t getuid (void);
char * getusershell (void);
char * getwd (char *__buf);
int iruserok (unsigned long raddr, int superuser, const char *ruser, const char *luser);
int isatty (int __fildes);
int issetugid (void);
int lchown (const char *__path, uid_t __owner, gid_t __group);
int link (const char *__path1, const char *__path2);
int linkat (int __dirfd1, const char *__path1, int __dirfd2, const char *__path2, int __flags);
int nice (int __nice_value);
off_t lseek (int __fildes, off_t __offset, int __whence);
int lockf (int __fd, int __cmd, off_t __len);
long pathconf (const char *__path, int __name);
int pause (void);
int pthread_atfork (void (*)(void), void (*)(void), void (*)(void));
int pipe (int __fildes[2]);
ssize_t pread (int __fd, void *__buf, size_t __nbytes, off_t __offset);
ssize_t pwrite (int __fd, const void *__buf, size_t __nbytes, off_t __offset);
int read (int __fd, void *__buf, size_t __nbyte);
int rresvport (int *__alport);
int revoke (char *__path);
int rmdir (const char *__path);
int ruserok (const char *rhost, int superuser, const char *ruser, const char *luser);
void * sbrk (ptrdiff_t __incr);
int setegid (gid_t __gid);
int seteuid (uid_t __uid);
int setgid (gid_t __gid);
int setgroups (int ngroups, const gid_t *grouplist);
int sethostname (const char *, size_t);
int setpgid (pid_t __pid, pid_t __pgid);
int setpgrp (void);
int setregid (gid_t __rgid, gid_t __egid);
int setreuid (uid_t __ruid, uid_t __euid);
pid_t setsid (void);
int setuid (uid_t __uid);
void setusershell (void);
unsigned sleep (unsigned int __seconds);
long sysconf (int __name);
pid_t tcgetpgrp (int __fildes);
int tcsetpgrp (int __fildes, pid_t __pgrp_id);
char * ttyname (int __fildes);
int ttyname_r (int, char *, size_t);
int unlink (const char *__path);
int usleep (useconds_t __useconds);
int vhangup (void);
int write (int __fd, const void *__buf, size_t __nbyte);
extern char *optarg;
extern int optind, opterr, optopt;
int getopt(int, char * const [], const char *);
extern int optreset;
pid_t vfork (void);
int ftruncate (int __fd, off_t __length);
int truncate (const char *, off_t __length);
int getdtablesize (void);
useconds_t ualarm (useconds_t __useconds, useconds_t __interval);
 int gethostname (char *__name, size_t __len);
int setdtablesize (int);
void sync (void);
ssize_t readlink (const char *restrict __path,
                          char *restrict __buf, size_t __buflen);
int symlink (const char *__name1, const char *__name2);
ssize_t readlinkat (int __dirfd1, const char *restrict __path,
                            char *restrict __buf, size_t __buflen);
int symlinkat (const char *, int, const char *);
int unlinkat (int, const char *, int);

cy_rslt_t cyhal_hwmgr_init(void);
cy_rslt_t cyhal_hwmgr_reserve(const cyhal_resource_inst_t* obj);
void cyhal_hwmgr_free(const cyhal_resource_inst_t* obj);
cy_rslt_t cyhal_hwmgr_allocate(cyhal_resource_t type, cyhal_resource_inst_t* obj);
extern const cyhal_resource_inst_t srss_0_clock_0_pathmux_0_obj;
extern const cyhal_resource_inst_t srss_0_clock_0_pathmux_1_obj;
extern const cyhal_resource_inst_t srss_0_clock_0_pathmux_2_obj;
extern const cyhal_resource_inst_t srss_0_clock_0_pathmux_3_obj;
extern const cyhal_resource_inst_t srss_0_clock_0_pathmux_4_obj;
void init_cycfg_system(void);
static inline void init_cycfg_routing(void) {}
extern const cy_stc_gpio_pin_config_t WCO_IN_config;
extern const cyhal_resource_inst_t WCO_IN_obj;
extern const cy_stc_gpio_pin_config_t WCO_OUT_config;
extern const cyhal_resource_inst_t WCO_OUT_obj;
extern const cy_stc_gpio_pin_config_t SWDIO_config;
extern const cyhal_resource_inst_t SWDIO_obj;
extern const cy_stc_gpio_pin_config_t SWCLK_config;
extern const cyhal_resource_inst_t SWCLK_obj;
void init_cycfg_pins(void);
void reserve_cycfg_pins(void);
void init_cycfg_all(void);
void cycfg_config_init(void);
void cycfg_config_reservations(void);

cy_rslt_t cybsp_init(void);

typedef struct
{
    uint32_t width;
    uint32_t polynomial;
    uint32_t lfsrInitState;
    uint32_t dataXor;
    uint32_t remXor;
    _Bool dataReverse;
    _Bool remReverse;
} crc_algorithm_t;
cy_rslt_t cyhal_crc_init(cyhal_crc_t *obj);
void cyhal_crc_free(cyhal_crc_t *obj);
cy_rslt_t cyhal_crc_start(cyhal_crc_t *obj, const crc_algorithm_t *algorithm);
cy_rslt_t cyhal_crc_compute(const cyhal_crc_t *obj, const uint8_t *data, size_t length);
cy_rslt_t cyhal_crc_finish(const cyhal_crc_t *obj, uint32_t *crc);

static inline cy_rslt_t _cyhal_crc_start(cyhal_crc_t *obj, const crc_algorithm_t *algorithm)
{
    do { if(!(((void *)0) != obj)) { CY_HALT(); } } while (0);
    if(((void *)0) == algorithm)
        return ((((((uint16_t) CY_RSLT_MODULE_ABSTRACTION_HAL) & ((1UL << ((14U))) - 1U)) << (18U)) | ((((((((uint16_t)CYHAL_RSLT_MODULE_CRC) & ((1UL << ((8U))) - 1U)) << (8U)) | ((uint16_t) 0)) & ((1UL << ((16U))) - 1U)) << (0U))) | ((((uint16_t) CY_RSLT_TYPE_ERROR) & ((1UL << ((2U))) - 1U)) << (16U))));
    obj->crc_width = algorithm->width;
    return Cy_Crypto_Core_Crc_CalcInit((obj->base), (algorithm->width), (algorithm->polynomial), (algorithm->dataReverse) ? 1u : 0u, (algorithm->dataXor), (algorithm->remReverse) ? 1u : 0u, (algorithm->remXor), (algorithm->lfsrInitState));
}
static inline cy_rslt_t _cyhal_crc_compute(const cyhal_crc_t *obj, const uint8_t *data, size_t length)
{
    do { if(!(((void *)0) != obj)) { CY_HALT(); } } while (0);
    if(((void *)0) == data || 0 == length)
        return ((((((uint16_t) CY_RSLT_MODULE_ABSTRACTION_HAL) & ((1UL << ((14U))) - 1U)) << (18U)) | ((((((((uint16_t)CYHAL_RSLT_MODULE_CRC) & ((1UL << ((8U))) - 1U)) << (8U)) | ((uint16_t) 0)) & ((1UL << ((16U))) - 1U)) << (0U))) | ((((uint16_t) CY_RSLT_TYPE_ERROR) & ((1UL << ((2U))) - 1U)) << (16U))));
    return Cy_Crypto_Core_Crc_CalcPartial((obj->base), (data), (length));
}
static inline cy_rslt_t _cyhal_crc_finish(const cyhal_crc_t *obj, uint32_t *crc)
{
    do { if(!(((void *)0) != obj)) { CY_HALT(); } } while (0);
    if(((void *)0) == crc)
        return ((((((uint16_t) CY_RSLT_MODULE_ABSTRACTION_HAL) & ((1UL << ((14U))) - 1U)) << (18U)) | ((((((((uint16_t)CYHAL_RSLT_MODULE_CRC) & ((1UL << ((8U))) - 1U)) << (8U)) | ((uint16_t) 0)) & ((1UL << ((16U))) - 1U)) << (0U))) | ((((uint16_t) CY_RSLT_TYPE_ERROR) & ((1UL << ((2U))) - 1U)) << (16U))));
    return Cy_Crypto_Core_Crc_CalcFinish((obj->base), (obj->crc_width), (crc));
}
static void _sb17_data_transfer_isr(void* callback_arg, cyhal_timer_event_t event);
static void _sb17_publish_sensor_data_callback(SB17_SENSOR_READING_t readings[4]);
static void _sb17_configure_sensor(uint32_t sensor_num, _Bool enabled);
static void _sb17_start_bulk_transfer();
static void _sb17_stop_bulk_transfer();
extern int pthread_create(pthread_t *thread, const pthread_attr_t *attr, void *(*routine)(void *), void *arg);
pthread_t thread_isr_all;
static void *thread_all_isrs(void *args);
_Bool thread_isr_uart_enabled = 0;
_Bool thread_isr_data_transfer_enabled = 0;
_Bool thread_isr_readout_timer_enabled = 0;
void enable_irq();
int main(void)
{
    pthread_create(&thread_isr_all, ((void *)0), thread_all_isrs, ((void *)0));
    cybsp_init();
    cyhal_gpio_init(__VERIFIER_nondet_int(), __VERIFIER_nondet_char(), __VERIFIER_nondet_char(),
                    __VERIFIER_nondet_bool());
    cyhal_gpio_init(__VERIFIER_nondet_int(), __VERIFIER_nondet_char(), __VERIFIER_nondet_char(),
                    __VERIFIER_nondet_bool());
    cyhal_crc_init(__VERIFIER_nondet_pointer());
    fs3d_init(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_bool(),
              __VERIFIER_nondet_bool());
    sb17_initialize_messenger();
    enable_irq();
    sb17_initialize_sensor_readout(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(),
                                   &_sb17_publish_sensor_data_callback);
    cyhal_gpio_write_internal(__VERIFIER_nondet_int(), __VERIFIER_nondet_bool());
    while (1) {
        if (__VERIFIER_nondet_bool()) {
            sb17_read_sensor_data();
        }
        if (__VERIFIER_nondet_bool()) {
            sb17_messenger_transfer_sensor_data();
        }
    }
}
static void _sb17_data_transfer_isr(void* callback_arg, cyhal_timer_event_t event)
{
    return;
}
static void _sb17_publish_sensor_data_callback(SB17_SENSOR_READING_t readings[4])
{
    fs3d_update_sensor_measurement(__VERIFIER_nondet_uint(), __VERIFIER_nondet_uint(), __VERIFIER_nondet_int());
}
hs_protobuf_fs3d_ResponseCode fs3d_cb_req_getSysConfig(const hs_protobuf_fs3d_GetSysConfigRequest* const req,
                                                       hs_protobuf_fs3d_GetSysConfigResponse* const rsp)
{
    switch (__VERIFIER_nondet_char()) {
        case hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType_SYSCONFIG_SENSORS_SENSITIVITY:
            return __VERIFIER_nondet_int();
        case hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType_SYSCONFIG_SENSORS_SAMPLING_RATE:
            return __VERIFIER_nondet_int();
        case hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType_SYSCONFIG_DATA_TRANSFER_RATE:
            return __VERIFIER_nondet_int();
        case hs_protobuf_fs3d_GetSysConfigRequest_SysConfigType_SYSCONFIG_SAR_CLOCK_DIVIDER:
            return __VERIFIER_nondet_int();
    }
    return __VERIFIER_nondet_int();
}
_Bool fs3d_cb_req_setSysConfig(const hs_protobuf_fs3d_SetSysConfigRequest* const req)
{
    if (__VERIFIER_nondet_bool()) {
        return __VERIFIER_nondet_bool();
    }
    if (__VERIFIER_nondet_uint() == 2) {
        sb17_reconfigure_sensor_readout(__VERIFIER_nondet_pointer());
        return __VERIFIER_nondet_bool();
    } else if (__VERIFIER_nondet_uint() == 3) {
        if (__VERIFIER_nondet_bool()) {
            sb17_stop_timer(__VERIFIER_nondet_pointer());
            sb17_intialize_isr_timer(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(),
                                     __VERIFIER_nondet_uint());
            sb17_start_timer(__VERIFIER_nondet_pointer());
            __VERIFIER_nondet_bool();
        }
    }
    return __VERIFIER_nondet_bool();
}
static void _sb17_configure_sensor(uint32_t sensor_num, _Bool enabled)
{
    if (__VERIFIER_nondet_bool()) {
        return;
    }
}
_Bool fs3d_cb_req_setSensorConfig(const FS3D_SensorConfigData_t* const req)
{
    {
        if (__VERIFIER_nondet_bool()) {
            _sb17_configure_sensor(__VERIFIER_nondet_uint(), __VERIFIER_nondet_bool());
        }
    }
    return __VERIFIER_nondet_bool();
}
static void _sb17_start_bulk_transfer()
{
    if (__VERIFIER_nondet_bool()) {
        _sb17_stop_bulk_transfer();
    }
    sb17_intialize_isr_timer(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint());
    sb17_start_timer(__VERIFIER_nondet_pointer());
}
static void _sb17_stop_bulk_transfer()
{
    if (__VERIFIER_nondet_bool()) {
        sb17_stop_timer((cyhal_timer_t*)__VERIFIER_nondet_pointer);
    }
}
_Bool fs3d_cb_req_getSensorDataBulk(const hs_protobuf_fs3d_GetSensorDataBulkRequest* const req)
{
    switch (__VERIFIER_nondet_char()) {
        case hs_protobuf_fs3d_GetSensorDataBulkRequest_SensorDataBulkState_SENSORDATA_BULK_START:
            _sb17_start_bulk_transfer();
            break;
        case hs_protobuf_fs3d_GetSensorDataBulkRequest_SensorDataBulkState_SENSORDATA_BULK_STOP:
            _sb17_stop_bulk_transfer();
            break;
    }
    return __VERIFIER_nondet_bool();
}
_Bool fs3d_msg_cb_send(pb_byte_t* msg_out_buf, size_t msg_out_len)
{
    if (__VERIFIER_nondet_bool()) {
        fs3d_packet_encode(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
        sb17_messenger_send_data(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_size_t());
    }
    return __VERIFIER_nondet_bool();
}
uint8_t fs3d_packet_cb_crc(const uint8_t* const buf, const size_t len)
{
    return __VERIFIER_nondet_uchar();
}
static void *thread_all_isrs(void *args)
{
    while (1) {
        __VERIFIER_atomic_begin();
        if (thread_isr_uart_enabled == 1 && __VERIFIER_nondet_bool()) {
            _sb17_uart_event_handler(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint());
        }
        __VERIFIER_atomic_end();
        __VERIFIER_atomic_begin();
        if (thread_isr_data_transfer_enabled == 1 && __VERIFIER_nondet_bool()) {
            _sb17_data_transfer_isr(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint());
        }
        __VERIFIER_atomic_end();
        __VERIFIER_atomic_begin();
        if (thread_isr_readout_timer_enabled == 1 && __VERIFIER_nondet_bool()) {
            _sb17_readout_timer_isr(__VERIFIER_nondet_pointer(), __VERIFIER_nondet_uint());
        }
        __VERIFIER_atomic_end();
    }
    return __VERIFIER_nondet_pointer();
}
void enable_irq()
{
    __VERIFIER_atomic_begin();
    thread_isr_uart_enabled = 1;
    thread_isr_data_transfer_enabled = 1;
    thread_isr_readout_timer_enabled = 1;
    __VERIFIER_atomic_end();
}
uint32_t Cy_SysLib_EnterCriticalSection(void)
{
    __VERIFIER_atomic_begin();
    thread_isr_uart_enabled = 0;
    thread_isr_data_transfer_enabled = 0;
    thread_isr_readout_timer_enabled = 0;
    __VERIFIER_atomic_end();
    return __VERIFIER_nondet_uint();
}
void Cy_SysLib_ExitCriticalSection(uint32_t savedIntrStatus)
{
    enable_irq();
}
