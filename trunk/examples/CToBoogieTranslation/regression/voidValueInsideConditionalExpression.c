//#Safe
/*
 * author: nutz, 7.5.2014
 */

int i = 0;

void myVoid() {
    i++;
}

int main() {
    _Bool flag;
    flag ? i-- : myVoid();
    //@assert (flag == 0) ==> (i == 1);
}



