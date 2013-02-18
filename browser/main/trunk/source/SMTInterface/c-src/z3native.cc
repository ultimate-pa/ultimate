#include "z3cc.hh"
#include "platformdefs.hh"
#include <iostream>
#include "idcache.hh"

/*
 * This file contains implementations of native methods needed by Z3 Java
 * port local.stalin.nativez3 to initialize and finalize the library.
 */

// The JNI Version we use...
  // TODO: Do we need something from 1.4 that is not in 1.2???
static const jint jniversion = JNI_VERSION_1_4;

/**
 * Hook function called after library gets loaded. I simply print out version 
 * of Z3 and return JNI version we use.
 */
STALIN_EXPORT jint STALIN_CALL JNI_OnLoad(JavaVM* vm,void*) {
  JNIEnv* env;
  if(vm->GetEnv(reinterpret_cast<void**>(&env),jniversion))
    // JNI version not supported!!!
    return JNI_ERR;
  jclass objcls = env->FindClass("java/lang/Object");
#ifndef NDEBUG
  // This will never happen!
  if( objcls == 0 )
    return JNI_ERR;
#endif
  idcache.hashcode = env->GetMethodID(objcls,"hashCode","()I");
#ifndef NDEBUG
  if( idcache.hashcode == 0 )
    return JNI_ERR;
#endif
  idcache.tostring = env->GetMethodID(objcls,"toString","()Ljava/lang/String;");
#ifndef NDEBUG
  if( idcache.tostring == 0 )
    return JNI_ERR;
#endif
  jclass stringcls = env->FindClass("java/lang/String");
#ifndef NDEBUG
  // This will never happen!!!
  if( stringcls == 0 )
    return JNI_ERR;
#endif
  // This prevents java.lang.String from beeing unloaded. Very unlikely thing...
  idcache.javastring = static_cast<jclass>(env->NewGlobalRef(stringcls));
  if( (idcache.stringconstruct = 
       env->GetMethodID(stringcls,"<init>","([B)V")) == 0 ) {
    env->DeleteGlobalRef(idcache.javastring);
    return JNI_ERR;
  }
  if( (idcache.stringgetbytes = 
       env->GetMethodID(stringcls,"getBytes","()[B")) == 0 ) {
    env->DeleteGlobalRef(idcache.javastring);
    return JNI_ERR;
  }
  // TODO: Perhaps we should find a nicer way to handle this message...
#ifndef NDEBUG
  unsigned int major,minor,build,revision;
  Z3_get_version(&major,&minor,&build,&revision);
  std::cerr << "NativeZ3 loaded with Z3 version " << major << '.' << minor <<
    '.' << build << '.' << revision << std::endl;
#endif
  return jniversion;
}

/**
 * Hook function called before library gets unloaded.
 */
STALIN_EXPORT void STALIN_CALL JNI_OnUnload(JavaVM* vm,void*) {
  JNIEnv* env;
  if(vm->GetEnv(reinterpret_cast<void**>(&env),jniversion))
    return;
  env->DeleteGlobalRef(idcache.javastring);
}
