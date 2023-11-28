//#Safe

// 20231121 Dominik
// This chain of typedefs (resolving to an incomplete struct) causes the C translation to crash.

struct mystruct;

typedef struct mystruct mytype;

typedef mytype yourtype;

struct mystruct {
    int __count;
    int __value;
};

int main() {
  return 0;
}
