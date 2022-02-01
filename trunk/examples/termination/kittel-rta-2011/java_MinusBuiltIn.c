int nondef(void);

int main() {
    int x = nondef();
    int y = nondef();
    int res = 0;

    while (x > y) {

        y++;
        res++;

    }
    
    return res;
}
