//#Safe

#include <stdio.h>
#include <stdbool.h>
#include <pthread.h>

// Global state

bool button_state = false;

bool step_in_isr = false;

// Function Prototypes
void HAL_GPIO_Init(void);
void HAL_GPIO_Enable_Int(void);
void isr_gpio(void);
bool HAL_GPIO_Read(void);
void HAL_GPIO_Write(int pin, int state);
void thread1(void);

// External or Mock Constants
#define BTN_PRESSED true
#define ON          1
#define OFF         0

int main(void) 
{
    
    HAL_GPIO_Init();
    HAL_GPIO_Enable_Int();

    pthread_t thr;
    pthread_create(&thr, NULL, thread1, NULL);

    return 0;
}

void HAL_GPIO_Enable_Int(void) 
{
    // ... logic ...
}

void isr_gpio(void) 
{   
    step_in_isr = true;
    bool st = HAL_GPIO_Read();
    if (st == BTN_PRESSED) {
        HAL_GPIO_Write(10, ON);
        button_state = st;
    } else {
        HAL_GPIO_Write(10, OFF);
        button_state = st;
    }
    step_in_isr  = false;  
   
}

void thread1(void)
{
    int n = 0;
    while (n < 100)
    {
        assert(!step_in_isr);
        n++;
        assert(!step_in_isr);
    }
}