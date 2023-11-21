//#Safe

struct __mbstate_t;

typedef struct __mbstate_t __mbstate_t;

typedef __mbstate_t mbstate_t;

struct __mbstate_t {
    int __count;
    int __value;
};

int main() {
  return 0;
}
