#include "z3parserctx.hh"
#include <jni.h>
#ifndef NDEBUG
#  include <iostream>
#endif

#include "newarraydebug.hh"

static inline z3parserctx* getz3parserctx(JNIEnv* env,jobject obj) {
  return 
    reinterpret_cast<z3parserctx*>(env->GetLongField(obj,idcache.parserstore));
}

static void STALIN_CALL initz3parser(JNIEnv* env,jobject obj,jlong z3ctx) {
  Z3_context ctx = reinterpret_cast<Z3_context>(z3ctx);
  try {
    z3parserctx* parser = new z3parserctx(env,ctx);
    env->SetLongField(obj,idcache.parserstore,reinterpret_cast<jlong>(parser));
  } catch( const pendingjavaexc& ) {
    // Do nothing!!!
  } catch (const std::exception& e) {
      thrownativecodeexception(env,e.what());
  } catch( ... ) {
      thrownativecodeexception(env,"Non-standard C++ exception");
  }
}

static void STALIN_CALL deinitz3parser(JNIEnv* env,jobject obj) {
  z3parserctx* parser = getz3parserctx(env,obj);
  env->SetLongField(obj,idcache.parserstore,0);
  parser->deinitialize(env);
  delete parser;
}

static void STALIN_CALL assertconstraint(JNIEnv* env,jobject obj,
					 jobject formula) {
    try {
	z3parserctx* parser = getz3parserctx(env,obj);
	if( !parser ) {
#ifndef NDEBUG
	    std::cerr << "Parser is already deinitialized!" << std::endl;
#endif
	    // Parser already deinitialized...
	    thrownativecodeexception(env,"Parser already deinitialized");
	    return;
	}
	Z3_context ctx = parser->context();
	Z3_ast fast = parser->parse(env,formula);
#ifndef NDEBUG
	std::cerr << "Before asserting constraint" << std::endl;
#endif
	Z3_assert_cnstr(ctx,fast);
#ifndef NDEBUG
	std::cerr << "After asserting constraint" << std::endl;
#endif
	CHECK_MEM;
    } catch( const pendingjavaexc& ) {
	CHECK_MEM;
	// Do nothing!!!
    } catch (const z3error& z3e) {
	CHECK_MEM;
	throwz3exception(env,z3e.errorcode());
    } catch (const std::exception& e) {
	CHECK_MEM;
	thrownativecodeexception(env,e.what());
    } catch( ... ) {
	CHECK_MEM;
	thrownativecodeexception(env,"Non-standard C++ exception occurred");
    }
}

// Structure always has function_name function_signature function_implementation
static JNINativeMethod parsermethods[] = {
  STALIN_NMETHOD("init","(J)V",initz3parser),
  STALIN_NMETHOD("deinit","()V",deinitz3parser),
  STALIN_NMETHOD("assertast","(Llocal/stalin/logic/Formula;)V",
		 assertconstraint)
};

// All JNI convention functions go here...
/**
 * Class used to initialize all IDs needed by class 
 * local.stalin.nativez3.Z3Config.
 */
STALIN_EXPORT void STALIN_CALL 
Java_local_stalin_nativez3_Z3Parser_initIDs(JNIEnv* env,jclass cls) {
  if( (idcache.parserstore = env->GetFieldID(cls,"nativestore","J")) == 0 )
    return;
  // No need to check for errors. We return nevertheless...
  env->RegisterNatives(cls,parsermethods,STALIN_NMETHODS(parsermethods));
}
