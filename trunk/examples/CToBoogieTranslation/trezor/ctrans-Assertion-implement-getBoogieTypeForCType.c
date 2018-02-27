enum rcc_periph_clken {
 RCC_OTGFS = (((0x34) << 5) + (7)),
};

void rcc_periph_clock_enable(enum rcc_periph_clken clken);

int main(void)
{
  rcc_periph_clock_enable(RCC_OTGFS);
}
