#include "newarraydebug.hh"

#ifdef DEBUG_ALLOC_DETAILED
#  include <iostream>
#  include <algorithm>

struct allocdetail {
    const char* mfilename;
    unsigned int mline;
    unsigned int msize;
    void* mallocres;
    allocdetail(const char* filename,unsigned int line,unsigned int size,
		void* allocres);
};

struct rescmp {
    void* mexpres;
    rescmp(void* expres) : mexpres(expres) {}
    bool operator()(allocdetail* ad) { return ad->mallocres == mexpres; }
};

allocdetail::allocdetail(const char* filename,unsigned int line,
			 unsigned int size,void* allocres)
    : mfilename(filename),mline(line),msize(size),mallocres(allocres) {}

typedef std::list<allocdetail*>::const_iterator citer;
typedef std::list<allocdetail*>::iterator iter;

allocdebug::~allocdebug() {
    iter end = mdetails.end();
    for (iter it = mdetails.begin(); it != end; ++it)
	delete *it;
}

void allocdebug::add(const char* name,unsigned int line,unsigned int size,
		     void* res) {
    try {
	mdetails.push_back(new allocdetail(name,line,size,res));
    } catch (...) {
	std::cerr << "Not enough memory to store allocation debug data for "
	    "allocation in file \""
		  << name << "\" line " << line << " of size " << size 
		  << " resulting in " << res << '!' << std::endl;
    }
}

void allocdebug::remove(void* res) {
    if (res) {
	iter it = std::find_if(mdetails.begin(),mdetails.end(),rescmp(res));
	if (it == mdetails.end()) {
	    std::cerr << "Freeing pointer " << res 
		      << " which has never been allocated!!!" << std::endl;
	} else {
	    delete *it;
	    mdetails.erase(it);
	}
    }
}

void allocdebug::checkempty() {
    iter end = mdetails.end();
    for (iter it = mdetails.begin(); it != end; ++it) {
	std::cerr << "Allocation in \"" << (*it)->mfilename << ':' 
		  << (*it)->mline << "\" of size " << (*it)->msize 
		  << " with result " << (*it)->mallocres << " leaked!" 
		  << std::endl;
	delete *it;
    }
    mdetails.clear();
}

allocdebug global_allocdebug;

#endif
