//#Safe

struct __mbstate_t;

typedef struct __mbstate_t __mbstate_t;

typedef __mbstate_t mbstate_t;

struct __mbstate_t { /* sizeof: 8, alignof: 4 */
    int __count;
    union anonymous_8411 __value;
};

int main() {
  return 0;
}
