//#Safe
/*  
   Extract from bftpd_3.c 
   
*/

struct command {
	char *name;
};

const struct command commands[] = {    
    {"c1"}
};

int main(void) {
    char x = *commands[0].name;
    return 0;
}
