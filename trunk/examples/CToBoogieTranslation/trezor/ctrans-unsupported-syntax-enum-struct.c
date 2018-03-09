//#Safe

enum rcc_clock_3v3 {
 RCC_CLOCK_3V3_120MHZ,
 RCC_CLOCK_3V3_END
};

typedef unsigned char uint8_t;
typedef short unsigned int uint16_t;
typedef long unsigned int uint32_t;

struct rcc_clock_scale {
 uint8_t pllm;
 uint32_t apb2_frequency;
};

const struct rcc_clock_scale rcc_hse_8mhz_3v3[RCC_CLOCK_3V3_END];

void rcc_clock_setup_hse_3v3(const struct rcc_clock_scale *clock)
{
}

int main()
{
  struct rcc_clock_scale clock = rcc_hse_8mhz_3v3[RCC_CLOCK_3V3_120MHZ];
  rcc_clock_setup_hse_3v3(&clock);
}
