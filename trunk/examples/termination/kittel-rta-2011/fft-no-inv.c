/*
 *    Radix-2 Fast Fourier Transformation
 *
 *    Arne Elster 2008
 * */

#include <math.h>
#include "fft.h"

void fft_reorder(fft_t*, fft_t*, fft_t*, fft_t*, const int, const int);

/*
 *     Radix-2 FFT
 *
 *     * real_inp und imag_inp stellen einen komplexen Input Vektor dar,
 *     * real_out und imag_out einen komplexen Output Vektor.
 *     * n ist die Menge der Elemente des Input/Output Vektors,
 *       muss aber eine Potenz von 2 sein.
 *     * direction = fft_forward:  FFT Transformation
 *       direction = fft_backward: inverse Transformation
 * */
void complex_fft_1d(fft_t * real_inp, fft_t * imag_inp,
                    fft_t * real_out, fft_t * imag_out,
                    const int n, const int direction)
{
    int i, j, l;
    int bits = (int) (log((double) n) / log(2.0));

    fft_reorder(real_inp, imag_inp, real_out, imag_out, n, bits);

    int size = 2;
    for (i = 0; i < bits; i++)
    {
        for (j = 0; j < n; j += size)
        {
            int k1 = j + (size >> 1);
            int k2 = j;

            for (l = 0; l < (size >> 1); l++)
            {
                const fft_t rad = (pi2 * l) / (size * direction);
                const fft_t WRe = cos(rad);
                const fft_t WIm = -sin(rad);

                fft_t real = real_out[k1] * WRe - imag_out[k1] * WIm;
                fft_t imag = real_out[k1] * WIm + imag_out[k1] * WRe;

                real_out[k1] = real_out[k2] - real;
                imag_out[k1] = imag_out[k2] - imag;
                real_out[k2] = real_out[k2] + real;
                imag_out[k2] = imag_out[k2] + imag;

                ++k1;
                ++k2;
            }
        }

        size <<= 1;
    }

    if (direction == fft_backward)
    {
        for (i = 0; i < n; i++)
        {
            real_out[i] /= n;
            imag_out[i] /= n;
        }
    }
}

/*
 *     Durch die vielen Aufspaltungen sind die Elemente
 *     des Ergebnisvektors an anderen Positionen, als sie
 *     sein sollten. Daher vertauscht man die Elemente vor
 *     der FFT schon so, dass sie danach an ihren entsprechenden
 *     Indices sitzen.
 * */
void fft_reorder(fft_t * real_inp, fft_t * imag_inp,
                 fft_t * real_out, fft_t * imag_out,
                 const int n, const int bits)
{
    int i, l;
    for (i = 0; i < n; i++)
    {
        int k = i;
        int j = 0;

        for (l = 0; l < bits; l++)
        {
            j = (j << 1) | (k & 1);
            k >>= 1;
        }

        real_out[j] = real_inp[i];
        imag_out[j] = imag_inp[i];
    }
}
