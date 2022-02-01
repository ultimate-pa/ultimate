//#Safe
typedef long unsigned int uint32_t;


static inline uint32_t timer_ms(void) {
  extern volatile uint32_t system_millis;
  return system_millis;
}

// this triggers a "identifier is not declared" exception when declared
// after (!) it's reference in timer_ms above
volatile uint32_t system_millis;

int main()
{
  system_millis = 0;
}
