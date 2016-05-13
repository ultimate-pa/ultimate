//https://git.kernel.org/cgit/linux/kernel/git/torvalds/linux.git/commit/?id=9ef7db7f38d0472dd9c444e42d5c5175ccbe5451
//may be reproduced by simply calling ufs_mkdir

#include<stdlib.h>

void *malloc(size_t size);
int *p;

int copy_from_user();
int init(int a);
int f();

void __VERIFIER_error();

void inode_inc_link_count() {
//do something
}

int state = 0;

void lock_ufs() {
	if(state==1) __VERIFIER_error();
	state = 1;
}

struct inode;

struct inode {
	struct inode *inode;
	int a;
};

int ufs_new_inode(struct inode *dir) {
	if(!dir) {
		return -1;
	}
	if(!dir->inode) {
		return -1;
	}
	if(f()) {//not important condition
		dir->a=0;
	} else {
		dir->a=1;
	} 
	//security: occur without any conditions
	//depends only on initial data input provided by allocate_data
	lock_ufs();
	return 0;
}

int ufs_mkdir(struct inode *dir) {
	lock_ufs();
	inode_inc_link_count();
	return ufs_new_inode(dir);
}

struct inode *allocate_data(void);

void main(void) {
	struct inode *dir;

	dir = allocate_data();

	if(ufs_mkdir(dir)==0) {
		//success
	};
}

