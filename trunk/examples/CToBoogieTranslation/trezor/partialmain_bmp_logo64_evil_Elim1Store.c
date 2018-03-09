//#Unsafe
typedef unsigned int uint8_t;

static uint8_t _oledbuffer[1024];

typedef struct {
 uint8_t width, height;
 const uint8_t *data;
} BITMAP;

extern const BITMAP bmp_logo_mini_evil;
const uint8_t bmp_logo_mini_data[] = { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,};
const BITMAP bmp_logo_mini_evil = {16, 16, bmp_logo_mini_data};

void oledDrawPixel(int x, int y)
{
 if ((x < 0) || (y < 0) || (x >= 128) || (y >= 64)) {
  return;
 }
 _oledbuffer[((128 * 64 / 8) - 1 - (x) - ((y)/8)*128)] |= (1 << (7 - (y) % 8));
}

void oledClearPixel(int x, int y)
{
 if ((x < 0) || (y < 0) || (x >= 128) || (y >= 64)) {
  return;
 }
 _oledbuffer[((128 * 64 / 8) - 1 - (x) - ((y)/8)*128)] &= ~(1 << (7 - (y) % 8));
}

void oledDrawBitmap(int x, int y, const BITMAP *bmp)
{
 for (int i = 0; i < bmp->width; i++) {
  for (int j = 0; j < bmp->height; j++) {
   // this line is dangerous if bmp->width, bmp->height compute to an index
   // out of bounds of the actual data
   if (bmp->data[(i / 8) + j * bmp->width / 8] & (1 << (7 - i % 8))) {
    oledDrawPixel(x + i, y + j);
   } else {
    oledClearPixel(x + i, y + j);
   }
  }
 }
}

int main(){
  oledDrawBitmap(0, 0, &bmp_logo_mini_evil);
  return 0;
}
