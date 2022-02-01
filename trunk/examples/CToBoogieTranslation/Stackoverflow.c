/*
 * DD 2016-10-11
 * This program results in an StackOverflowError. 
 */

union listen_entry {
   int t3c_tid ;
   union listen_entry *next ;
};
union active_open_entry {
   int t3c_tid ;
   union active_open_entry *next ;
};
struct tid_info {
   union listen_entry *stid_tab ;
};

int main() 
{ 
	struct tid_info *t;
	(union active_open_entry *)t->stid_tab    ;
}