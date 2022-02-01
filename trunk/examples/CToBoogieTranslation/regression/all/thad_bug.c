//#Unsafe
/*-----------------------------------------------------------------------------
 * thad_bug.c - program to demonstrate bug in ACSL-to-Boogie translator
 *-----------------------------------------------------------------------------
 * author: Manuel Bentele
 * date  : Jan 30, 2020
 * copyright (c) Manuel Bentele
 *-----------------------------------------------------------------------------
 * THADs:
 *     open < ioctl(SPI_IOC_WR_MODE, SPI_MODE_3);
 *     ioctl(SPI_IOC_WR_MODE, SPI_MODE_3) < read
 *-----------------------------------------------------------------------------
 * verification result:
 *     [ IST]: Ultimate proves program to be correct (SAFE)
 *     [SOLL]: Program is incorrect due to a THAD violation
 *---------------------------------------------------------------------------*/

// DD: Same bug as thad_bug.c, see description there. 

#include <stdlib.h>
#include <stdio.h>

/*---------------------------------------------------------------------------*/
/* ghost variables for THAD monitor
/*---------------------------------------------------------------------------*/
int state_open_mode = 0;
int state_mode_read = 0;

/*---------------------------------------------------------------------------*/
/* modeled #defines and data structures for verification purposes
/*---------------------------------------------------------------------------*/
int SUCCESS = 0;
int FAILURE = 1;

int SPI_IOC_MESSAGE = 1075866368;
int SPI_IOC_WR_MODE = 1073834753;

unsigned char SPI_MODE_3 = 0x03;

/*---------------------------------------------------------------------------*/
/* modeled functions for verification purposes
/*---------------------------------------------------------------------------*/
int open(const char *path, int oflag) {
    /*@ assert (state_open_mode == 0 || state_open_mode == 1); */
    
    /*-----------------------------------------------------------------------*/
    /* implementation of open -> generate valid file descriptor (fildes)
    /*-----------------------------------------------------------------------*/
    int fildes = __VERIFIER_nondet_int();
    __VERIFIER_assume(fildes >= 0);
    /*-----------------------------------------------------------------------*/
    
    state_open_mode = 1;
    
    return fildes;
}

int ioctl(int fildes, int request, int *arg) {
    if (request == SPI_IOC_WR_MODE && *arg == SPI_MODE_3) {
        /*@ assert (state_open_mode == 1); */
        /*@ assert (state_mode_read == 0 || state_mode_read == 1); */
    }
    
    /*-----------------------------------------------------------------------*/
    /* implementation of ioctl -> set successful return code
    /*-----------------------------------------------------------------------*/
    int ret = 0;
    /*-----------------------------------------------------------------------*/
    
    if (request == SPI_IOC_WR_MODE && *arg == SPI_MODE_3) {
        state_open_mode = 1;
        state_mode_read = 1;
    }
    
    return ret;
}

int read(int fildes, void *buf, int nbyte) {
    /*@ assert (state_mode_read == 1); */
    
    /*-----------------------------------------------------------------------*/
    /* implementation of read -> set number of received bytes to buffer size
    /*-----------------------------------------------------------------------*/
    int ret = nbyte;
    /*-----------------------------------------------------------------------*/
    
    state_mode_read = 1;
    
    return ret;
}

unsigned int sleep(unsigned int seconds) {}

int NUM_VALUES = 3;

int main(void) {
    
    /* allocate memory for measurement values */
    int *values = malloc(NUM_VALUES * sizeof(int));

    /* open and initialize SPI peripheral */
    int spi_fd = open("/dev/spidev0.0", 0);
    if (spi_fd < 0) {
        return FAILURE;
    }

    int res;
    // ERROR: HAL-API routine ioctl(SPI_IOC_WR_MODE, SPI_MODE_3) must be called
    //        to satisfy THAD ioctl(SPI_IOC_WR_MODE, SPI_MODE_3) < read
    //res = ioctl(spi_fd, SPI_IOC_WR_MODE, SPI_MODE_3);
    //if (res < 0) {
    //    return FAILURE;
    //}
    
    /* buffer to receive data from SPI peripheral */
    int rx_buf = 0;
    
    /* receive measurement values from sensor via SPI transfer */
    for(int i = 0; i < NUM_VALUES; i++) {
        res = read(spi_fd, &rx_buf, sizeof(rx_buf));
        if (res < 0) {
            return FAILURE;
        }
        
        values[i] = rx_buf;
        
        sleep(1);
    }
    
    /* compute average of the received measurement values */
    int sum = 0;
    for(int j = 0; j < NUM_VALUES; j++) {
        sum += values[j]; 
    }
    int average = sum / NUM_VALUES;
    
    /* print average on the console */
    printf("Average of last %d measurement values: %d", NUM_VALUES, average);
    
    free(values);
    
    return SUCCESS;
}
