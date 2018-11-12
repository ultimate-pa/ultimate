//#Safe

union mytype {
    int z;
    struct {
        int x, y;
    } s;
};


int main() {
    union mytype u;
    u.s.y = 11;
    u.z = 3;
    u.s.x = 20;

    //@assert u.z == 20;
}
