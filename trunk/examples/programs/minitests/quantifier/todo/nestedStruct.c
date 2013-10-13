/*
 * Syntax Error in TypeHandler:
 * (type instanceof CStruct)
 * -> not implemented
 */
struct Inner {
   int b;
};
struct Outer {
   int a;
   struct Inner x;
};

int main() {
    struct Outer outer;
    
    if (outer.x.b == 4) {
        return (1);
    }
    
    return (0);
}
