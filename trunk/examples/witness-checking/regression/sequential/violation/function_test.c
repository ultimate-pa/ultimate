int get_int(){
    return 5;
}

int main(){
    int x = get_int();
    if(x>0){
        reach_error();
    }
}