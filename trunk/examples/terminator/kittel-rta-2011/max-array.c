int max(int a[], int low, int high)
{
    if (low >= high) {
        return a[low];
    } else {
        int mid = (low + high) / 2;
        int leftmax = max(a, low, mid);
        int rightmax = max(a, mid + 1, high);
        if (leftmax > rightmax) {
            return leftmax;
        } else {
            return rightmax;
        }
    }
}
