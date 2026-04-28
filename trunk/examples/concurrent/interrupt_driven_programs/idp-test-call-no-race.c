//#Safe

#include <stdio.h>
#include <stdbool.h>

extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();

// Global state

bool button_state = false;

bool step_in_isr = false;

// Function Prototypes
void HAL_GPIO_Init(void);
void HAL_GPIO_Enable_Int1(void);
void HAL_GPIO_Enable_Int2(void);
void isr1_gpio(void);
void isr2_gpio(void);
bool HAL_GPIO_Read(int n);
void HAL_GPIO_Write(int pin, int state);
int get_value(bool st);

// External or Mock Constants
#define BTN_PRESSED true
#define ON          1
#define OFF         0

int main(void) 
{
    
    HAL_GPIO_Init();
    HAL_GPIO_Enable_Int1();
    HAL_GPIO_Enable_Int2();

    int i = 0;
    __VERIFIER_atomic_begin();
    button_state = false;
    if (button_state){
      i = 5;
    }
    __VERIFIER_atomic_end();
    assert(i == 0);
    return 0;
}

void HAL_GPIO_Enable_Int1(void) 
{
    // ... logic ...
}

void HAL_GPIO_Enable_Int2(void) 
{
    // ... logic ...
}

void isr1_gpio(void) 
{   
    step_in_isr = true;
    bool st = HAL_GPIO_Read(1);
    if (st == BTN_PRESSED) {
        HAL_GPIO_Write(10, ON);
        button_state = st;
    } else {
        HAL_GPIO_Write(10, OFF);
        button_state = st;
    }
    step_in_isr  = false;  
   
}

void isr2_gpio(void) 
{   
    step_in_isr = true;
    bool st = HAL_GPIO_Read(2);
    int val = get_value(st);
    HAL_GPIO_Write(val, ON);
    button_state = st;
    step_in_isr  = false;
}
