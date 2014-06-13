/**
 * @file bmpfile.c
 * @brief The BMP library implementation
 *
 * libbmp - BMP library
 * Copyright (C) 2009 lidaibin
 * mail: lidaibin@gmail.com
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 *
 * $Id: bmpfile.c,v 1.1 2010-11-18 13:03:44 spf Exp $
 */


/*
 * BMP File Header  Stores general information about the BMP file.
 * DIB header       Stores detailed information about the bitmap image.
 * Color Palette    Stores the definition of the colors being used for
 *                    indexed color bitmaps.
 * Bitmap Data      Stores the actual image, pixel by pixel.
 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bmpfile.h"

#define DEFAULT_DPI_X 3780
#define DEFAULT_DPI_Y 3780
#define DPI_FACTOR 39.37007874015748

struct _bmpfile {
  bmp_header_t header;
  bmp_dib_v3_header_t dib;

  rgb_pixel_t **pixels;
  rgb_pixel_t *colors;
};

uint32_t
uint32_pow(uint32_t base, uint32_t depth)
{
  uint32_t i, result = 1;

  for (i = 0; i < depth; ++i)
    result *= base;

  return result;
}

/**
 * Create the standard color table for BMP object
 */
void
bmp_create_standard_color_table(bmpfile_t *bmp)
{
  int i, j, k, ell;

  switch (bmp->dib.depth) {
  case 1:
    for (i = 0; i < 2; ++i) {
      bmp->colors[i].red = i * 255;
      bmp->colors[i].green = i * 255;
      bmp->colors[i].blue = i * 255;
      bmp->colors[i].alpha = 0;
    }
    break;

  case 4:
    i = 0;
    for (ell = 0; ell < 2; ++ell) {
      for (k = 0; k < 2; ++k) {
        for (j = 0; j < 2; ++j) {
          bmp->colors[i].red = j * 128;
          bmp->colors[i].green = k * 128;
          bmp->colors[i].blue = ell * 128;
          bmp->colors[i].alpha = 0;
          ++i;
        }
      }
    }

    for (ell = 0; ell < 2; ++ell) {
      for (k = 0; k < 2; ++k) {
        for (j = 0; j < 2; ++j) {
          bmp->colors[i].red = j * 255;
          bmp->colors[i].green = k * 255;
          bmp->colors[i].blue = ell * 255;
          bmp->colors[i].alpha = 0;
          ++i;
        }
      }
    }

    i = 8;
    bmp->colors[i].red = 192;
    bmp->colors[i].green = 192;
    bmp->colors[i].blue = 192;
    bmp->colors[i].alpha = 0;

    break;

  case 8:
    i = 0;
    for (ell = 0; ell < 4; ++ell) {
      for (k = 0; k < 8; ++k) {
        for (j = 0; j < 8; ++j) {
          bmp->colors[i].red = j * 32;
          bmp->colors[i].green = k * 32;
          bmp->colors[i].blue = ell * 64;
          bmp->colors[i].alpha = 0;
          ++i;
        }
      }
    }

    i = 0;
    for (ell = 0; ell < 2; ++ell) {
      for (k = 0; k < 2; ++k) {
        for (j = 0; j < 2; ++j) {
          bmp->colors[i].red = j * 128;
          bmp->colors[i].green = k * 128;
          bmp->colors[i].blue = ell * 128;
          ++i;
        }
      }
    }

    // overwrite colors 7, 8, 9
    i = 7;
    bmp->colors[i].red = 192;
    bmp->colors[i].green = 192;
    bmp->colors[i].blue = 192;
    i++; // 8
    bmp->colors[i].red = 192;
    bmp->colors[i].green = 220;
    bmp->colors[i].blue = 192;
    i++; // 9
    bmp->colors[i].red = 166;
    bmp->colors[i].green = 202;
    bmp->colors[i].blue = 240;

    // overwrite colors 246 to 255
    i = 246;
    bmp->colors[i].red = 255;
    bmp->colors[i].green = 251;
    bmp->colors[i].blue = 240;
    i++; // 247
    bmp->colors[i].red = 160;
    bmp->colors[i].green = 160;
    bmp->colors[i].blue = 164;
    i++; // 248
    bmp->colors[i].red = 128;
    bmp->colors[i].green = 128;
    bmp->colors[i].blue = 128;
    i++; // 249
    bmp->colors[i].red = 255;
    bmp->colors[i].green = 0;
    bmp->colors[i].blue = 0;
    i++; // 250
    bmp->colors[i].red = 0;
    bmp->colors[i].green = 255;
    bmp->colors[i].blue = 0;
    i++; // 251
    bmp->colors[i].red = 255;
    bmp->colors[i].green = 255;
    bmp->colors[i].blue = 0;
    i++; // 252
    bmp->colors[i].red = 0;
    bmp->colors[i].green = 0;
    bmp->colors[i].blue = 255;
    i++; // 253
    bmp->colors[i].red = 255;
    bmp->colors[i].green = 0;
    bmp->colors[i].blue = 255;
    i++; // 254
    bmp->colors[i].red = 0;
    bmp->colors[i].green = 255;
    bmp->colors[i].blue = 255;
    i++; // 255
    bmp->colors[i].red = 255;
    bmp->colors[i].green = 255;
    bmp->colors[i].blue = 255;
    break;
  }
}

/**
 * Create grayscale color table for BMP object
 */
void
bmp_create_grayscale_color_table(bmpfile_t *bmp)
{
  uint32_t i;
  uint8_t step_size;

  if (!bmp->colors) return;

  if (bmp->dib.depth != 1)
    step_size = 255 / (bmp->dib.ncolors - 1);
  else
    step_size = 255;

  for (i = 0; i < bmp->dib.ncolors; ++i) {
    uint8_t value = i * step_size;
    rgb_pixel_t color = {value, value, value, 0};
    bmp->colors[i] = color;
  }
}

/**
 * Malloc the memory for color palette
 */
void
bmp_malloc_colors(bmpfile_t *bmp)
{
  bmp->dib.ncolors = uint32_pow(2, bmp->dib.depth);
  if (bmp->dib.depth == 1 || bmp->dib.depth == 4 || bmp->dib.depth == 8) {
    bmp->colors = malloc(sizeof(rgb_pixel_t) * bmp->dib.ncolors);
    bmp_create_standard_color_table(bmp);
  }
}

/**
 * Free the memory of color palette
 */
void
bmp_free_colors(bmpfile_t *bmp)
{
  if (bmp->colors)
    free(bmp->colors);
}

/**
 * Malloc the memory for pixels
 */
void
bmp_malloc_pixels(bmpfile_t *bmp)
{
  int i, j;
  int imax, jmax;

  bmp->pixels = malloc(sizeof(rgb_pixel_t *) * bmp->dib.width);
  imax = bmp->dib.width;
  jmax = bmp->dib.height;
  for (i = 0; i < imax; ++i) {
    bmp->pixels[i] = malloc(sizeof(rgb_pixel_t) * bmp->dib.height);
    for (j = 0; j < jmax; ++j) {
      bmp->pixels[i][j].red = 255;
      bmp->pixels[i][j].green = 255;
      bmp->pixels[i][j].blue = 255;
      bmp->pixels[i][j].alpha = 0;
    }
  }
}

/**
 * Free the memory of pixels
 */
void
bmp_free_pixels(bmpfile_t *bmp)
{
  int i;
  int imax = bmp->dib.width;

  for (i = 0; i < imax; ++i)
    free(bmp->pixels[i]);

  free(bmp->pixels), bmp->pixels = NULL;
}

/**
 * Create the BMP object with specified width and height and depth.
 */
bmpfile_t *
bmp_create(uint32_t width, uint32_t height, uint32_t depth)
{
  bmpfile_t *result;
  double bytes_per_pixel;
  uint32_t bytes_per_line;
  uint32_t palette_size;

  if (depth != 1 && depth != 4 && depth != 8 && depth != 16 && depth != 24 &&
      depth != 32)
    return NULL;

  result = malloc(sizeof(bmpfile_t));

  memset(result, 0, sizeof(bmpfile_t));

  result->header.magic[0] = 'B';
  result->header.magic[1] = 'M';

  result->dib.header_sz = 40;
  result->dib.width = width;
  result->dib.height = height;
  result->dib.nplanes = 1;
  result->dib.depth = depth;
  result->dib.hres = DEFAULT_DPI_X;
  result->dib.vres = DEFAULT_DPI_Y;

  if (depth == 16)
    result->dib.compress_type = BI_BITFIELDS;
  else
    result->dib.compress_type = BI_RGB;

  bmp_malloc_pixels(result);
  bmp_malloc_colors(result);

  /* Calculate the field value of header and DIB */
  bytes_per_pixel = (result->dib.depth * 1.0) / 8.0;
  bytes_per_line = (int)ceil(bytes_per_pixel * result->dib.width);
  if (bytes_per_line % 4 != 0)
    bytes_per_line += 4 - bytes_per_line % 4;

  result->dib.bmp_bytesz = bytes_per_line * result->dib.height;

  palette_size = 0;
  if (depth == 1 || depth == 4 || depth == 8)
    palette_size = uint32_pow(2, result->dib.depth) * 4;
  else if (result->dib.depth == 16)
    palette_size = 3 * 4;

  result->header.offset = 14 + result->dib.header_sz + palette_size;
  result->header.filesz = result->header.offset + result->dib.bmp_bytesz;

  return result;
}

void
bmp_destroy(bmpfile_t *bmp)
{
  bmp_free_pixels(bmp);
  bmp_free_colors(bmp);
  free(bmp);
}

uint32_t
bmp_get_width(bmpfile_t *bmp)
{
  return bmp->dib.width;
}

uint32_t
bmp_get_height(bmpfile_t *bmp)
{
  return bmp->dib.height;
}

uint32_t
bmp_get_depth(bmpfile_t *bmp)
{
  return bmp->dib.depth;
}

bmp_header_t
bmp_get_header(bmpfile_t *bmp)
{
  return bmp->header;
}

bmp_dib_v3_header_t
bmp_get_dib(bmpfile_t *bmp)
{
  return bmp->dib;
}

uint32_t
bmp_get_dpi_x(bmpfile_t *bmp)
{
  return (uint32_t)(bmp->dib.hres / DPI_FACTOR);
}

uint32_t
bmp_get_dpi_y(bmpfile_t *bmp)
{
  return (uint32_t)(bmp->dib.vres / DPI_FACTOR);
}

void
bmp_set_dpi(bmpfile_t *bmp, uint32_t x, uint32_t y)
{
  bmp->dib.hres = (uint32_t)(x * DPI_FACTOR);
  bmp->dib.vres = (uint32_t)(y * DPI_FACTOR);
}

rgb_pixel_t *
bmp_get_pixel(bmpfile_t *bmp, uint32_t x, uint32_t y)
{
  if ((x >= bmp->dib.width) || (y >= bmp->dib.height))
    return NULL;

  return &(bmp->pixels[x][y]);
}

bool
bmp_set_pixel(bmpfile_t *bmp, uint32_t x, uint32_t y, rgb_pixel_t pixel)
{
  if ((x >= bmp->dib.width) || (y >= bmp->dib.height))
    return FALSE;

  bmp->pixels[x][y] = pixel;
  return TRUE;
}

bool
_is_big_endian(void)
{
  uint16_t value = 0x0001;

  return (*(uint8_t *)&value) != 0x01;
}

#define UINT16_SWAP_LE_BE_CONSTANT(val) \
  ((uint16_t) \
   ( \
    (uint16_t) ((uint16_t) (val) >> 8) | \
    (uint16_t) ((uint16_t) (val) << 8)))

#define UINT32_SWAP_LE_BE_CONSTANT(val)  \
  ((uint32_t) \
   ( \
    (((uint32_t) (val) & (uint32_t) 0x000000ffU) << 24) | \
    (((uint32_t) (val) & (uint32_t) 0x0000ff00U) <<  8) | \
    (((uint32_t) (val) & (uint32_t) 0x00ff0000U) >>  8) | \
    (((uint32_t) (val) & (uint32_t) 0xff000000U) >> 24)))

void
bmp_header_swap_endianess(bmp_header_t *header)
{
  header->filesz = UINT32_SWAP_LE_BE_CONSTANT(header->filesz);
  header->creator1 = UINT16_SWAP_LE_BE_CONSTANT(header->creator1);
  header->creator2 = UINT16_SWAP_LE_BE_CONSTANT(header->creator2);
  header->offset = UINT32_SWAP_LE_BE_CONSTANT(header->offset);
}

void
bmp_dib_v3_header_swap_endianess(bmp_dib_v3_header_t *dib)
{
  dib->header_sz = UINT32_SWAP_LE_BE_CONSTANT(dib->header_sz);
  dib->width = UINT32_SWAP_LE_BE_CONSTANT(dib->width);
  dib->height = UINT32_SWAP_LE_BE_CONSTANT(dib->height);
  dib->nplanes = UINT16_SWAP_LE_BE_CONSTANT(dib->nplanes);
  dib->depth = UINT16_SWAP_LE_BE_CONSTANT(dib->depth);
  dib->compress_type = UINT32_SWAP_LE_BE_CONSTANT(dib->compress_type);
  dib->bmp_bytesz = UINT32_SWAP_LE_BE_CONSTANT(dib->bmp_bytesz);
  dib->hres = UINT32_SWAP_LE_BE_CONSTANT(dib->hres);
  dib->vres = UINT32_SWAP_LE_BE_CONSTANT(dib->vres);
  dib->ncolors = UINT32_SWAP_LE_BE_CONSTANT(dib->ncolors);
  dib->nimpcolors = UINT32_SWAP_LE_BE_CONSTANT(dib->nimpcolors);
}

void
bmp_write_header(bmpfile_t *bmp, FILE *fp)
{
  bmp_header_t header = bmp->header;

  if (_is_big_endian()) bmp_header_swap_endianess(&header);

  fwrite(header.magic, sizeof(header.magic), 1, fp);
  fwrite(&(header.filesz), sizeof(uint32_t), 1, fp);
  fwrite(&(header.creator1), sizeof(uint16_t), 1, fp);
  fwrite(&(header.creator2), sizeof(uint16_t), 1, fp);
  fwrite(&(header.offset), sizeof(uint32_t), 1, fp);
}

void
bmp_write_dib(bmpfile_t *bmp, FILE *fp)
{
  bmp_dib_v3_header_t dib = bmp->dib;

  if (_is_big_endian()) bmp_dib_v3_header_swap_endianess(&dib);

  fwrite(&(dib.header_sz), sizeof(uint32_t), 1, fp);
  fwrite(&(dib.width), sizeof(uint32_t), 1, fp);
  fwrite(&(dib.height), sizeof(uint32_t), 1, fp);
  fwrite(&(dib.nplanes), sizeof(uint16_t), 1, fp);
  fwrite(&(dib.depth), sizeof(uint16_t), 1, fp);
  fwrite(&(dib.compress_type), sizeof(uint32_t), 1, fp);
  fwrite(&(dib.bmp_bytesz), sizeof(uint32_t), 1, fp);
  fwrite(&(dib.hres), sizeof(uint32_t), 1, fp);
  fwrite(&(dib.vres), sizeof(uint32_t), 1, fp);
  fwrite(&(dib.ncolors), sizeof(uint32_t), 1, fp);
  fwrite(&(dib.nimpcolors), sizeof(uint32_t), 1, fp);
}

void
bmp_write_palette(bmpfile_t *bmp, FILE *fp)
{
  if (bmp->dib.depth == 1 || bmp->dib.depth == 4 || bmp->dib.depth == 8) {
    int i;
    int imax = bmp->dib.ncolors;
    for (i = 0; i < imax; ++i)
      fwrite(&(bmp->colors[i]), sizeof(rgb_pixel_t), 1, fp);
  }
  else if (bmp->dib.depth == 16) { /* the bit masks, not palette */
    uint16_t red_mask = 63488;  /* bits 1-5 */
    uint16_t green_mask = 2016; /* bits 6-11 */
    uint16_t blue_mask = 31;    /* bits 12-16 */
    uint16_t zero_word = 0;

    if (_is_big_endian()) {
      red_mask = UINT16_SWAP_LE_BE_CONSTANT(red_mask);
      green_mask = UINT16_SWAP_LE_BE_CONSTANT(green_mask);
      blue_mask = UINT16_SWAP_LE_BE_CONSTANT(blue_mask);
    }

    fwrite(&red_mask, sizeof(uint16_t), 1, fp);
    fwrite(&zero_word, sizeof(uint16_t), 1, fp);

    fwrite(&green_mask, sizeof(uint16_t), 1, fp);
    fwrite(&zero_word, sizeof(uint16_t), 1, fp);

    fwrite(&blue_mask, sizeof(uint16_t), 1, fp);
    fwrite(&zero_word, sizeof(uint16_t), 1, fp);
  }
}

#define INT_SQUARE(v) ((int)((v) * (v)))

int
find_closest_color(bmpfile_t *bmp, rgb_pixel_t pixel)
{
  int i, imax, best = 0;
  int best_match = 999999;

  imax = bmp->dib.ncolors;
  for (i = 0; i < imax; ++i) {
    rgb_pixel_t color = bmp->colors[i];
    int temp_match = INT_SQUARE(color.red - pixel.red) +
      INT_SQUARE(color.green - pixel.green) +
      INT_SQUARE(color.blue - pixel.blue);

    if (temp_match < best_match) {
      best = i;
      best_match = temp_match;
    }

    if (best_match < 1)
      break;
  }

  return best;
}

void
bmp_get_row_data_for_1(bmpfile_t *bmp, unsigned char *buf, size_t buf_len, uint32_t row)
{
  uint8_t pos_weights[8] = {128, 64, 32, 16, 8, 4, 2, 1};
  uint32_t i = 0, j, k = 0;
  uint32_t imax = bmp->dib.width;
  uint32_t index;

  if (bmp->dib.width > 8 * buf_len) return;

  while (i < imax) {
    for (j = 0, index = 0; j < 8 && i < imax; ++i, ++j)
      index += pos_weights[j] * find_closest_color(bmp, bmp->pixels[i][row]);

    buf[k++] = index & 0xff;
  }
}

void
bmp_get_row_data_for_4(bmpfile_t *bmp, unsigned char *buf, size_t buf_len, uint32_t row)
{
  uint8_t pos_weights[2] = {16, 1};
  uint32_t i = 0, j, k = 0;
  uint32_t imax = bmp->dib.width;
  uint32_t index;

  if (bmp->dib.width > 2 * buf_len) return;

  while (i < imax) {
    for (j = 0, index = 0; j < 2 && i < imax; ++i, ++j)
      index += pos_weights[j] * find_closest_color(bmp, bmp->pixels[i][row]);

    buf[k++] = index & 0xff;
  }
}

void
bmp_get_row_data_for_8(bmpfile_t *bmp, unsigned char *buf, size_t buf_len, uint32_t row)
{
  uint32_t i;
  uint32_t imax = bmp->dib.width;

  if (bmp->dib.width > buf_len) return;

  for (i = 0; i < imax; ++i)
    buf[i] = find_closest_color(bmp, bmp->pixels[i][row]);
}

void
bmp_get_row_data_for_24(bmpfile_t *bmp, unsigned char *buf, size_t buf_len, uint32_t row)
{
  uint32_t i;
  uint32_t imax = bmp->dib.width;

  if (bmp->dib.width * 3 > buf_len) return;

  for (i = 0; i < imax; ++i)
    memcpy(buf + 3 * i, (uint8_t *)&(bmp->pixels[i][row]), 3);
}

void
bmp_get_row_data_for_32(bmpfile_t *bmp, unsigned char *buf, size_t buf_len, uint32_t row)
{
  uint32_t i;
  uint32_t imax = bmp->dib.width;

  if (bmp->dib.width * 4 > buf_len) return;

  for (i = 0; i < imax; ++i)
    memcpy(buf + 4 * i, (uint8_t *)&(bmp->pixels[i][row]), 4);
}

bool
bmp_save(bmpfile_t *bmp, const char *filename)
{
  FILE *fp;
  int row;
  unsigned char *buf;

  /* Create the file */
  if ((fp = fopen(filename, "wb")) == NULL)
    return FALSE;

  /* Write the file */
  bmp_write_header(bmp, fp);
  bmp_write_dib(bmp, fp);
  bmp_write_palette(bmp, fp);

  if (bmp->dib.depth == 16) {
    uint32_t data_bytes = bmp->dib.width * 2;
    uint32_t padding_bytes = 4 - data_bytes % 4;

    for (row = bmp->dib.height - 1; row >= 0; --row) {
      int i;
      unsigned char zero_byte = 0;
      uint32_t write_number = 0;

      for (i = 0; write_number < data_bytes; ++i, write_number += 2) {
        uint16_t red = (uint16_t)(bmp->pixels[i][row].red / 8);
        uint16_t green = (uint16_t)(bmp->pixels[i][row].green / 4);
        uint16_t blue = (uint16_t)(bmp->pixels[i][row].blue / 8);
        uint16_t value = (red << 11) + (green << 5) + blue;

        if (_is_big_endian()) value = UINT16_SWAP_LE_BE_CONSTANT(value);
        fwrite(&value, sizeof(uint16_t), 1, fp);
      }

      for (write_number = 0; write_number < padding_bytes; ++write_number)
        fwrite(&zero_byte, 1, 1, fp);
    }
  }
  else {
    double bytes_per_pixel;
    int bytes_per_line;

    bytes_per_pixel = (bmp->dib.depth * 1.0) / 8.0;
    bytes_per_line = (int)ceil(bytes_per_pixel * bmp->dib.width);
    if (bytes_per_line % 4 != 0)
      bytes_per_line += 4 - bytes_per_line % 4;

    buf = malloc(bytes_per_line);

    for (row = bmp->dib.height - 1; row >= 0; --row) {
      memset(buf, 0, bytes_per_line);

      switch (bmp->dib.depth) {
      case 1:
        bmp_get_row_data_for_1(bmp, buf, bytes_per_line, row);
        break;

      case 4:
        bmp_get_row_data_for_4(bmp, buf, bytes_per_line, row);
        break;

      case 8:
        bmp_get_row_data_for_8(bmp, buf, bytes_per_line, row);
        break;

      case 24:
        bmp_get_row_data_for_24(bmp, buf, bytes_per_line, row);
        break;

      case 32:
        bmp_get_row_data_for_32(bmp, buf, bytes_per_line, row);
        break;
      }

      fwrite(buf, bytes_per_line, 1, fp);
    }
    free(buf);
  }

  fclose(fp);

  return TRUE;
}

int
main(int argc, char **argv)
{
  bmpfile_t *bmp;
  int i, j;
  rgb_pixel_t pixel = {128, 64, 0, 0};
  int jmax = atoi(argv[3]);

  if (argc < 5) {
    printf("Usage: %s filename width height depth.\n", argv[0]);
    return 1;
  }

  if ((bmp = bmp_create(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]))) == NULL) {
    printf("Invalid depth value: %s.\n", argv[4]);
    return 1;
  }

  for (i = 10, j = 10; j < jmax; ++i, ++j) {
    bmp_set_pixel(bmp, i, j, pixel);
    pixel.red++;
    pixel.green++;
    pixel.blue++;
    bmp_set_pixel(bmp, i + 1, j, pixel);
    bmp_set_pixel(bmp, i, j + 1, pixel);
  }

  bmp_save(bmp, argv[1]);
  bmp_destroy(bmp);

  return 0;
}
