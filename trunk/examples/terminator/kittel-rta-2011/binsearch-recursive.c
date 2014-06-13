/* Recursive function*/  
int b_search_recursive(int l[],int arrayStart,int arrayEnd,int a)  
{  
    int m;
    if (arrayStart<=arrayEnd)  
    {  
        m=(arrayStart+arrayEnd)/2;  
        if (l[m]==a)  
            return m;  
        else if (a<l[m])  
            return b_search_recursive(l,arrayStart,m-1,a);  
        else  
            return b_search_recursive(l,m+1,arrayEnd,a);  
    }  
    return -1;

}
