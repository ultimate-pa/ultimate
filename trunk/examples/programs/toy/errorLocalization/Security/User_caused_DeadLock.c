// Security bug
// User caused deadlock
#include<stdlib.h>
void __VERIFIER_error();
int user_input(void);
int f();
int state = 0;
void lock_ufs(){
	if(state==1) __VERIFIER_error();
	state = 1;
}
int ufs_new_inode(int dir){
	if(dir == 0){
		return -1;
	}
	if(dir == 1){
		return -1;
	}
	// lock_ufs occurs without any conditions.
	// Depends only on the user input provided
	// by allocate_data
	lock_ufs();
	return 0;
}
int ufs_mkdir(int dir) {
	lock_ufs();
	return ufs_new_inode(dir);
}
void main(void) {
	int dir = user_input();
	if(ufs_mkdir(dir) == 0){
		// success
	}
}

