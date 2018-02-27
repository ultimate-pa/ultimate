typedef unsigned int uint8_t;

typedef struct {
 uint8_t width, height;
 const uint8_t *data;
} BITMAP;
extern const BITMAP bmp_logo_mini_evil;
const uint8_t bmp_logo_mini_data[] = { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,};
const BITMAP bmp_logo_mini_evil = {9, 9, bmp_logo_mini_data};

int main() {
  bmp_logo_mini_evil;
}
