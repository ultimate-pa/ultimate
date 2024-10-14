int this_is_a_function_with_lots_of_arguments(int a,int b, int c, int d, int e,
                                             int f, int g, int h, int i, int j, 
                                             int k, int l, int m, int n, int o, int p){
    return 5;
}

int main(){
    int x = this_is_a_function_with_lots_of_arguments(100, 53436, 4542542345, 200,
                                                    5565365,76863,868754,575,6857,
                                                    67587,42354,3524,453,54,352,532445);
    if(x>0){
        reach_error();
    }
}