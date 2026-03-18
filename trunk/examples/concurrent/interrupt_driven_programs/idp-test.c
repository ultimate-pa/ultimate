#include <stdio.h>
#include <stdbool.h>
#include <pthread.h>

extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();

// Global state
bool gpio_int_enabled = false;

bool button_state = false;

bool step_in_isr = false;

// Function Prototypes
void HAL_GPIO_Init(void);
void HAL_GPIO_Enable_Int(void);
void isr_gpio(void);
void *thr_gpio(void *arg);
bool HAL_GPIO_Read(void);
void HAL_GPIO_Write(int pin, int state);

// External or Mock Constants
#define BTN_PRESSED true
#define ON          1
#define OFF         0

int main(void) 
{
    pthread_t thr;

    // Initialize hardware before starting threads/interrupts
    pthread_create(&thr, NULL, thr_gpio, NULL);
    
    HAL_GPIO_Init();
    HAL_GPIO_Enable_Int();

    int n = 0;
    while (1) {
        assert(!step_in_isr);
        n++;
        assert(!step_in_isr);
    }

    return 0;
}

void HAL_GPIO_Enable_Int(void) 
{
    __VERIFIER_atomic_begin();
    // ... logic ...
    gpio_int_enabled = true;
    __VERIFIER_atomic_end();
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

void *thr_gpio(void *arg) 
{
    while (1) {
        __VERIFIER_atomic_begin();
        if (gpio_int_enabled) {
            isr_gpio();
        }
        __VERIFIER_atomic_end();
    }
    return NULL;
}