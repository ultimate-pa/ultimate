#ifndef STALIN_JAVAHASHMAP_HH_
#define STALIN_JAVAHASHMAP_HH_

#include <jni.h>
#include "platformdefs.hh"
#include "z3cc.hh"
#include <map>
#include "idcache.hh"
#include "exceptions.hh"
#include "helper.hh"
#ifndef NDEBUG
#  include <iostream>
#endif

template<typename T>
class STALIN_INTERNAL javahashmap {
  std::multimap<jint,std::pair<jobject,T> > rep;
 public:
  typedef typename std::multimap<jint,std::pair<jobject,T> >::iterator iterator;
  iterator insert(JNIEnv* env,jobject obj,const T& t);
  const T& get(JNIEnv* env,jobject obj) const;
  void clear(JNIEnv* env);
  void remove(JNIEnv* env,jobject obj);
  void remove(JNIEnv* env,iterator it);
  bool contains(JNIEnv* env,jobject obj) const;
 private:
  jint javahash(JNIEnv* env,jobject obj) const;
};

template<typename T>
typename javahashmap<T>::iterator 
javahashmap<T>::insert(JNIEnv* env,jobject obj,const T& t) {
  jint hash = javahash(env,obj);
  jobject gobj = env->NewGlobalRef(obj);
  if( !gobj )
    throw pendingjavaexc();
  return rep.insert(std::make_pair(hash,std::make_pair(gobj,t)));
}

template<typename T>
const T& javahashmap<T>::get(JNIEnv* env,jobject obj) const {
  typedef typename std::multimap<jint,std::pair<jobject,T> >::const_iterator ci;
  jint hash = javahash(env,obj);
  std::pair<ci,ci> range = rep.equal_range(hash);
  for( ci it = range.first; it != range.second; ++it )
    if( env->IsSameObject(it->second.first,obj) )
      return it->second.second;
  thrownativecodeexception(env,"Did not find object in hashmap");
  throw pendingjavaexc();
}

template<typename T>
void javahashmap<T>::clear(JNIEnv* env) {
  typedef typename std::multimap<jint,std::pair<jobject,T> >::const_iterator ci;
  ci end = rep.end();
  for( ci it = rep.begin(); it != end; ++it )
    env->DeleteGlobalRef(it->second.first);
  rep.clear();
}

template<typename T>
void javahashmap<T>::remove(JNIEnv* env,jobject obj) {
  typedef typename std::multimap<jint,std::pair<jobject,T> >::iterator iter;
  iter end = rep.end();
  for( iter it = rep.begin(); it != end; ++it ) {
    if( env->IsSameObject(obj,it->second.first) )
      env->DeleteGlobalRef(it->second.first);
    rep.erase(it);
    return;
  }  
}

template<typename T>
void javahashmap<T>::remove(JNIEnv* env,iterator it) {
  env->DeleteGlobalRef(it->second.first);
  rep.erase(it);
}

template<typename T>
jint javahashmap<T>::javahash(JNIEnv* env,jobject obj) const {
  return env->CallIntMethod(obj,idcache.hashcode);
}

template<typename T>
bool javahashmap<T>::contains(JNIEnv* env,jobject obj) const {
  typedef typename std::multimap<jint,std::pair<jobject,T> >::const_iterator ci;
  jint hash = javahash(env,obj);
  std::pair<ci,ci> range = rep.equal_range(hash);
  for( ci it = range.first; it != range.second; ++it )
    if( env->IsSameObject(it->second.first,obj) )
	return true;
  return false;
}

#endif
