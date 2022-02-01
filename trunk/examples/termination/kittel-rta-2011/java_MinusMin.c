int min (int x, int y) {

    if (x < y) return x;
    else return y;

}

int nondef(void);

int main() {
    int x = nondef();
    int y = nondef();
    int res = 0;

    while (min(x-1,y) == y) {

        y++;
        res++;

    }

    return res;

}
