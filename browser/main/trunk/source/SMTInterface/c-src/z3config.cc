#include <jni.h>
#include "z3cc.hh"
#include "exceptions.hh"
#include "helper.hh"
#include "idcache.hh"

/**
 * Function corresponding to local.stalin.nativez3.Z3Config.initialize.
 */
static void STALIN_CALL initializeconfig(JNIEnv* env,jobject obj) {
  Z3_config cfg = Z3_mk_config();
  env->SetLongField(obj,idcache.configstore,reinterpret_cast<jlong>(cfg));
}

/**
 * Function corresponding to local.stalin.nativez3.Z3Config.deinitialize.
 */
static void STALIN_CALL deinitializeconfig(JNIEnv* env,jobject obj) {
  Z3_config cfg = 
    reinterpret_cast<Z3_config>(env->GetLongField(obj,idcache.configstore));
  Z3_del_config(cfg);
}

/**
 * Function corresponding to 
 * local.stalin.nativez3.Z3Config.setConfig(String,String).
 */
static void STALIN_CALL setconfig(JNIEnv* env,jobject obj,
				  jstring conf,jstring val) {
  try {
    Z3_config cfg = 
      reinterpret_cast<Z3_config>(env->GetLongField(obj,idcache.configstore));
    utf8stringhelper hconf(env,conf);
    utf8stringhelper hval(env,val);
    Z3_set_param_value(cfg,hconf,hval);
  } catch( const pendingjavaexc& exc ) {
    // This exception just tells: Let Java handle pending exception
  }
}

// Structure always has function_name function_signature function_implementation
static JNINativeMethod configmethods[] = {
  STALIN_NMETHOD("initialize","()V",initializeconfig),
  STALIN_NMETHOD("deinitialize","()V",deinitializeconfig),
  STALIN_NMETHOD("setConfig","(Ljava/lang/String;Ljava/lang/String;)V",
    setconfig)
};

// All JNI convention functions go here...
/**
 * Class used to initialize all IDs needed by class 
 * local.stalin.nativez3.Z3Config.
 */
STALIN_EXPORT void STALIN_CALL 
Java_local_stalin_nativez3_Z3Config_initIDs(JNIEnv* env,jclass cls) {
  if( (idcache.configstore = env->GetFieldID(cls,"nativestore","J")) == 0 )
    return;
  // No need to check for errors. We return nevertheless...
  env->RegisterNatives(cls,configmethods,STALIN_NMETHODS(configmethods));
}
