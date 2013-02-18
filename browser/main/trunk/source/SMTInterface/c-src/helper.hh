#ifndef STALIN_HELPER_HH_
#define STALIN_HELPER_HH_

#include "platformdefs.hh"
#include <jni.h>
#include "z3cc.hh"

#define STALIN_NMETHODS(x) (sizeof(x)/sizeof(x[0]))
#define STALIN_NMETHOD(N,S,F) {const_cast<char*>(N),const_cast<char*>(S),\
      reinterpret_cast<void*>(F)}

/**
 * Helper class to manage local reference frames in an exception-safe way.
 */
class STALIN_INTERNAL localframehelper {
  JNIEnv* menv;
 public:
  localframehelper(JNIEnv* env,jint capacity);
  ~localframehelper();
  jobject popframe(jobject result);
};

/**
 * Helper class to manage UTF-8 strings
 */
class STALIN_INTERNAL utf8stringhelper {
  JNIEnv* menv;
  jstring mjstr;
  char* mcstr;
 public:
  utf8stringhelper(JNIEnv* env,jstring jstr);
  ~utf8stringhelper();
  void release();
  inline const char* cstr() const { return mcstr; }
  inline operator const char*() const { return mcstr; }
};

/**
 * Helper function to create a C string from a Java string.
 */
char* getjavastring(JNIEnv* env,jstring str) STALIN_INTERNAL;

/**
 * Helper function to create a Java string from a C string.
 */
jstring newjavastring(JNIEnv* env,const char* str) STALIN_INTERNAL;

/**
 * Helper function to create a Java string from a C string.
 */
jstring newjavastring(JNIEnv* env,const char* str,size_t length)STALIN_INTERNAL;

/**
 * Helper function to throw a local.stalin.nativez3.NativeCodeException.
 */
void thrownativecodeexception(JNIEnv* env,const char* errmsg) STALIN_INTERNAL;

/**
 * Helper function to throw a local.stalin.nativez3.Z3Exception.
 */
void throwz3exception(JNIEnv* env,Z3_error_code err) STALIN_INTERNAL;

/**
 * Helper function to savely get a class reference.
 */
jclass safegetclass(JNIEnv* env,const char* cd) STALIN_INTERNAL;

/**
 * Helper function to savely get a method id.
 */
jmethodID safegetmethodid(JNIEnv* env,jclass cls,const char* mname,
			  const char* md) STALIN_INTERNAL;

/**
 * Helper function to savely get a field id.
 */
jfieldID safegetfieldid(JNIEnv* env,jclass cls,const char* fname,
			const char* fd) STALIN_INTERNAL;

#endif
