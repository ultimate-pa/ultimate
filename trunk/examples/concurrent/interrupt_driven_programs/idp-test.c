//#Safe
#include <stdio.h>
#include <stdbool.h>

// Global state

bool button_state = false;

bool step_in_isr = false;
int n = 0;

// Function Prototypes
void HAL_GPIO_Init(void);
void HAL_GPIO_Enable_Int(void);
void isr_gpio(void);
bool HAL_GPIO_Read(void);
void HAL_GPIO_Write(int pin, int state);

// External or Mock Constants
#define BTN_PRESSED true
#define ON          1
#define OFF         0

int main(void) 
{
    
    HAL_GPIO_Init();
    HAL_GPIO_Enable_Int();

    n = 0;
    while (1) {
        assert(!step_in_isr);
        n++;
        assert(!step_in_isr);
    }

    return 0;
}

void HAL_GPIO_Enable_Int(void) 
{
    // ... logic ...
}

void isr_gpio(void) 
{   
    int old_n = n;
    step_in_isr = true;
    bool st = HAL_GPIO_Read();
    if (st == BTN_PRESSED) {
        HAL_GPIO_Write(10, ON);
        button_state = st;
    } else {
        HAL_GPIO_Write(10, OFF);
        button_state = st;
    }
    int i = 0;
    while (i<3){
      i++;
    }
    step_in_isr  = false;  
   assert(n==old_n);
}
