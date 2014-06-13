void dif(int *A, int *B, int *D, int l1, int l2){
    int k=0;
    int i=0;
    int found;
    while(i<l1){
        int j=0;
        found=0;
	while((j<l2)&&(!found)){
            if(A[i]==B[j]) found=1;
            else j++;
        }

	if (!found) {
            D[k]=A[i];
	    k++;
	}
        i++;
    }
}
