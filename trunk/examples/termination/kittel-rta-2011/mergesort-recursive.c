typedef enum bool { false, true } bool; 
 
void MergeSort(int list[], int size)
{      
    if(size > 1) {
        int half1[size/2];
        int half2[(size + 1)/2];
        int i;
        for(i = 0; i < size/2; ++i)
            half1[i] = list[i];
        for(i = size/2; i < size; ++i)
            half2[i - size/2] = list[i];

        MergeSort(half1,size/2);
        MergeSort(half2,(size + 1)/2);

        int *pos1 = &half1[0];
        int *pos2 = &half2[0];
        bool donehalf1 = false;
        bool donehalf2 = false;
        for(i = 0; i < size; ++i){
            if(*pos1 <= *pos2 && !donehalf1){
                list[i] = *pos1;
                if(pos1 == &half1[size/2 - 1]){
                    donehalf1 = true;
                }
                else{
                    ++pos1;
                }
            }
            else if (!donehalf2){
                list[i] = *pos2;
                if(pos2 == &half2[(size + 1)/2 - 1]){
                    donehalf2 = true;
                }
                else{
                    ++pos2;
                }
            }
        }
    }
}
