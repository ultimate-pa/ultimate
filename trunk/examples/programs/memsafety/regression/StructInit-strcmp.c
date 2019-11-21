//#Safe
/*  
   Extract from bftpd_3.c 
   We reported unsafe because we reordered the init statements in the translation acording to the source location, i.e., we moved the init of "c1" after the init of "commands[]", which left the struct in the array uninitialized. 
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
