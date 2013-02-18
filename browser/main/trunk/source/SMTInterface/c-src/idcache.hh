#ifndef STALIN_IDCACHE_HH_
#define STALIN_IDCACHE_HH_

#include <jni.h>

/*
 * Cache for method and field ids. Store them in one cache structure to
 * 1) Save GOT-space and
 * 2) Improve generated PIC-code
 */
extern struct idcache_t {
  // java.lang.Object.hashCode
  jmethodID hashcode;
  // java.lang.Object.toString
  jmethodID tostring;
  // Java String class - This is a global reference!!!
  jclass javastring;
  // Constructor java.lang.String(byte[])
  jmethodID stringconstruct;
  // java.lang.String.getBytes method
  jmethodID stringgetbytes;
  // everything needed from local.stalin.nativez3.Z3Config
  jfieldID configstore;
  // everything needed from local.stalin.nativez3.Z3Context
  jfieldID contextstore;
  jfieldID contextfailure;
  jfieldID contextproof;
  // everything needed from local.stalin.nativez3.Z3ProofRule
  jmethodID proofconstruct;
  jmethodID proofaddrule;
  jfieldID proofresult;
  // everything needed from local.stalin.nativez3.Z3Parser
  jfieldID parserstore;
} idcache;

#endif
