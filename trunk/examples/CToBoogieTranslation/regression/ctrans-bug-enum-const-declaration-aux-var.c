//#Safe
enum
{
	A = 1==1 ? 1 : 0
};

int main(){
    if(A){
        
    } else{
        //@assert \false;
    }
    return 0;
}