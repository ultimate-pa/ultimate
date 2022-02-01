int binary_search(int sorted_list[], int low, int high, int element)
{
    while (low <= high) {
        int middle = low + (high - low) / 2;
        if (element > sorted_list[middle])
            low = middle + 1;
        else if (element < sorted_list[middle])
            high = middle - 1;
        else
            return middle;
    }
    return -1;
}
