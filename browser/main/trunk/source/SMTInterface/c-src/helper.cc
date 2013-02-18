#include "helper.hh"
#include "exceptions.hh"
#include <cstring>
#include "idcache.hh"
#include "z3cc.hh"
#ifndef NDEBUG
#  include <iostream>
#endif

#include "newarraydebug.hh"

localframehelper::localframehelper(JNIEnv* env,jint capacity)
  : menv(env) {
  if( env->PushLocalFrame(capacity) ) {
    menv = 0;
    throw pendingjavaexc();
  }
}

localframehelper::~localframehelper() {
  popframe(0);
}

utf8stringhelper::utf8stringhelper(JNIEnv* env,jstring jstr)
  : menv(env),mjstr(jstr),mcstr(0) {
  if( (mcstr = 
      const_cast<char*>(reinterpret_cast<const char*>(env->
	  GetStringUTFChars(jstr,0)))) == 0 )
    throw pendingjavaexc();
}

utf8stringhelper::~utf8stringhelper() {
  release();
}

void utf8stringhelper::release() {
  if( mcstr ) {
    menv->ReleaseStringUTFChars(mjstr,mcstr);
    mcstr = 0;
  }
}

jobject localframehelper::popframe(jobject result) {
  jobject res = 0;
  if( menv ) {
    res = menv->PopLocalFrame(result);
    menv = 0;
  }
  return res;
}

char* getjavastring(JNIEnv* env,jstring str) {
  // Ensure enough local reference space for a byte array
  if( env->EnsureLocalCapacity(1) < 0 )
    // Pending OutOfMemoryException
    throw pendingjavaexc();
  jbyteArray bytes = 
    static_cast<jbyteArray>(env->CallObjectMethod(str,idcache.stringgetbytes));
  if( env->ExceptionCheck() )
    throw pendingjavaexc();
  jint len = env->GetArrayLength(bytes);
  // Rely on operator new[] to throw std::bad_alloc exception which will only be
  // caught directly before returning to Java
  char *result;
  NEW_ARRAY(result,char,len+1);
  env->GetByteArrayRegion(bytes,0,len,reinterpret_cast<jbyte*>(result));
  result[len] = 0;
  env->DeleteLocalRef(bytes);
  return result;
}

jstring newjavastring(JNIEnv* env,const char* str) {
  return newjavastring(env,str,std::strlen(str));
}

jstring newjavastring(JNIEnv* env,const char* str,size_t len) {
  if( env->EnsureLocalCapacity(2) < 0 )
    // OutOfMemoryError pending...
    throw pendingjavaexc();
  jbyteArray bytes = env->NewByteArray(len);
  if( bytes == 0 )
    // OutOfMemoryError pending...
    throw pendingjavaexc();
  env->SetByteArrayRegion(bytes,0,len,reinterpret_cast<const jbyte*>(str));
  jstring result = 
    static_cast<jstring>(env->
			 NewObject(idcache.javastring,idcache.stringconstruct,
				   bytes));
  env->DeleteLocalRef(bytes);
  if( !result )
    throw pendingjavaexc();
  return result;
}

void thrownativecodeexception(JNIEnv* env,const char* errmsg) {
  if( env->EnsureLocalCapacity(3) < 0 )
    return;
  jclass cls = safegetclass(env,"local/stalin/nativez3/NativeCodeException");
  if( cls ) {
    jmethodID cid = safegetmethodid(env,cls,"<init>","(Ljava/lang/String;)V");
    if( cid ) {
	jstring str = newjavastring(env,errmsg);
	jobject exc = env->NewObject(cls,cid,str);
      env->Throw(static_cast<jthrowable>(exc));
      env->DeleteLocalRef(exc);
      env->DeleteLocalRef(str);
    }
  }
  env->DeleteLocalRef(cls);
}

void throwz3exception(JNIEnv* env,Z3_error_code err) {
  if( env->EnsureLocalCapacity(3) < 0 )
    return;
  jclass cls = safegetclass(env,"local/stalin/nativez3/Z3Exception");
  if( cls ) {
    jmethodID cid = safegetmethodid(env,cls,"<init>","(ILjava/lang/String;)V");
    if( cid ) {
      jstring str = newjavastring(env,Z3_get_error_msg(err));
      jobject exc = env->NewObject(cls,cid,static_cast<jint>(err),str);
      env->Throw(static_cast<jthrowable>(exc));
      env->DeleteLocalRef(exc);
      env->DeleteLocalRef(str);
    }
  }
  env->DeleteLocalRef(cls);
}

jclass safegetclass(JNIEnv* env,const char* cd) {
  jclass res = env->FindClass(cd);
  if( !res )
    throw pendingjavaexc();
  return res;
}

jmethodID safegetmethodid(JNIEnv* env,jclass cls,const char* mname,
			  const char* md) {
  jmethodID res = env->GetMethodID(cls,mname,md);
  if( !res )
    throw pendingjavaexc();
  return res;
}

jfieldID safegetfieldid(JNIEnv* env,jclass cls,const char* fname,
			const char* fd) {
  jfieldID res = env->GetFieldID(cls,fname,fd);
  if( !res )
    throw pendingjavaexc();
  return res;
}
