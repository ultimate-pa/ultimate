void solve(int h, int from, int to, int support) {
    if (h < 1) return;
    else if (h == 1) {
        //System.out.println("from " + from + " to " + to + "\n");
    }
    else {
        solve(h - 1, from, support, to);
        //System.out.println("from " + from + " to " + to + "\n");
        solve(h - 1, support, to, from);
    }
}
