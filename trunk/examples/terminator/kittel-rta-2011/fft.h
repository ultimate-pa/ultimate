#ifndef _FFT_H_
#define _FFT_H_

typedef double fft_t;

const double pi  = 3.14159265358979;
const double pi2 = 2 * 3.14159265358979;

const int fft_forward  =  1;
const int fft_backward = -1;

void complex_fft_1d(fft_t * real_inp, fft_t * imag_inp,
                    fft_t * real_out, fft_t * imag_out,
                    const int n, const int direction);

#endif
