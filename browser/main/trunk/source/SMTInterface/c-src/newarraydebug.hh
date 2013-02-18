#ifndef _NEEWARRAYDEBUG_HH_
#define _NEEWARRAYDEBUG_HH_

#  ifdef DEBUG_ALLOC_DETAILED

#    include <list>

struct allocdetail;

class allocdebug {
    std::list<allocdetail*> mdetails;
public:
    ~allocdebug();
    void add(const char* file,unsigned int line,unsigned int size,void* res);
    void remove(void* res);
    void checkempty();
};

extern allocdebug global_allocdebug;

#define NEW_ARRAY(RES,SORT,SIZE) do { \
    RES = new SORT[SIZE];		   \
    global_allocdebug.add(__FILE__,__LINE__,SIZE,RES);  \
    } while (0)

#define DELETE_ARRAY(RES) do {			\
    global_allocdebug.remove(RES);		\
    delete[] RES;				\
    } while (0)

#define CHECK_MEM do { global_allocdebug.checkempty(); } while (0)

#else

#define NEW_ARRAY(RES,SORT,SIZE) do { RES = new SORT[SIZE]; } while (0)
#define DELETE_ARRAY(RES) do { delete[] RES; } while (0)
#define CHECK_MEM do { } while (0)

#  endif

#endif
