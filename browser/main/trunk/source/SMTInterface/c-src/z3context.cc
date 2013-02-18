#include <jni.h>
#include "z3cc.hh"
#include "exceptions.hh"
#include "helper.hh"
#include "idcache.hh"
#include <cassert>
#include <cstring>
#include <map>
#include <iostream>
#ifndef NPROFILE
#  include <ctime>
#endif

#ifdef DEBUG_PROOFTREEPARSING
class STALIN_INTERNAL scopeprinter {
  const char* mscope;
  const unsigned long mnscope;
  static unsigned long numscopes;
 public:
  explicit scopeprinter(const char* scope);
  ~scopeprinter();
};

scopeprinter::scopeprinter(const char* scope)
  : mscope(scope),mnscope(++numscopes) {
  std::cerr << "Begin scope " << mscope << ' ' << mnscope << std::endl;
}

scopeprinter::~scopeprinter() {
  std::cerr << "End scope " << mscope << ' ' << mnscope << std::endl;
}

unsigned long scopeprinter::numscopes = 0;
#endif

/**
 * Cache structure needed during retranslation of Z3_ast to Formula.
 */
struct STALIN_INTERNAL genformulactx {
  // TLB for formulae
  std::map<Z3_ast,jobject> mknowntrans;
  // TLB for sorts
  std::map<Z3_sort,jobject> msorts;
  // TLB for proof rules
  std::map<Z3_app,jobject> mknownprs;
  // Back translation for de Bruijn-indexes
  unsigned int mnumbound;
  std::map<unsigned int,jobject> mtermvars;
  // TLB for function declarations
  std::map<Z3_func_decl,jobject> mfuncdecls;
  Z3_context mctx;
  // global reference to local.stalin.nativez3.ProofRule
  jclass mprcls;
  // global reference to an object of local.stalin.logic.Theory
  jobject mtheory;
  // global reference to local.stalin.logic.Atom.TRoUE
  jobject mtrue;
  // global reference to local.stalin.logic.Atom.FALSE
  jobject mfalse;
  // TermVariable class
  jclass mtv;
  // c'tor or factory method
  jmethodID mtvinit;
  // global reference to local.stalin.logic.Sort
  jclass msortcls;
  // global reference to local.stalin.logic.Term
  jclass mtermcls;
  // Connectives
  jmethodID mnot;
  jmethodID mand;
  jmethodID mor;
  jmethodID mimplies;
  jmethodID mxor;
  jmethodID miff;
  jmethodID moeq;
  jmethodID mitet;
  jmethodID mitef;
  // Getters
  jmethodID mgetfunc;
  jmethodID mgetpred;
  jmethodID mgetsort;
  jmethodID mcreatefunc;
  jmethodID mcreatepred;
  // Creation of parts
  jmethodID matom;
  jmethodID mterm;
  jmethodID mequals;
  jmethodID mdistinct;
  jmethodID mtvterm;
  jmethodID mrational;
  jmethodID mnumeral;
  jmethodID mexists;
  jmethodID mforall;
  unsigned int numrules;
  unsigned int numunifies;
  genformulactx(JNIEnv* env,Z3_context ctx,jobject theory);
  void release(JNIEnv* env);
  jobject convertsort(JNIEnv* env,Z3_sort sort);
  jobject convertast(JNIEnv* env,Z3_ast ast);
  jobject convertapp(JNIEnv* env,Z3_app app);
  jobject getfunc(JNIEnv* env,Z3_func_decl fd,bool& ispred);
  jobjectArray convertparams(JNIEnv* env,Z3_app app);
  typedef std::map<Z3_ast,jobject>::const_iterator transiter;
  typedef std::map<Z3_sort,jobject>::const_iterator sortiter;
  typedef std::map<unsigned int,jobject>::const_iterator termiter;
  typedef std::map<Z3_func_decl,jobject>::const_iterator funciter;
  typedef std::map<Z3_app,jobject>::const_iterator priter;
};

genformulactx::genformulactx(JNIEnv* env,Z3_context ctx,jobject theory)
    : mnumbound(0),mctx(ctx),mprcls(0),mtheory(0),mtrue(0),mfalse(0),mtv(0),
      msortcls(0),mtermcls(0),numrules(0),numunifies(0) {
  if( env->EnsureLocalCapacity(2) < 0 )
    throw pendingjavaexc();
  try {
    jclass tmp = safegetclass(env,"local/stalin/nativez3/Z3ProofRule");
    mprcls = static_cast<jclass>(env->NewGlobalRef(tmp));
    assert(mprcls);
    env->DeleteLocalRef(tmp);
    mtheory = env->NewGlobalRef(theory);
    assert(mtheory);
    tmp = safegetclass(env,"local/stalin/logic/Atom");
    jfieldID tmpid = env->GetStaticFieldID(tmp,"TRUE",
					   "Llocal/stalin/logic/Atom;");
#ifndef NDEBUG
    if( !tmpid )
      throw pendingjavaexc();
#endif
    jobject tmpo = env->GetStaticObjectField(tmp,tmpid);
    mtrue = env->NewGlobalRef(tmpo);
    assert(mtrue);
    env->DeleteLocalRef(tmpo);
    tmpid = env->GetStaticFieldID(tmp,"FALSE",
				  "Llocal/stalin/logic/Atom;");
#ifndef NDEBUG
    if( !tmpid )
      throw pendingjavaexc();
#endif
    tmpo = env->GetStaticObjectField(tmp,tmpid);
    mfalse = env->NewGlobalRef(tmpo);
    assert(mfalse);
    env->DeleteLocalRef(tmpo);
    env->DeleteLocalRef(tmp);
    tmp = safegetclass(env,"local/stalin/logic/TermVariable");
    mtv = static_cast<jclass>(env->NewGlobalRef(tmp));
    assert(mtv);
#if 0
    mtvinit = safegetmethodid(env,tmp,"<init>",
			      "(Ljava/lang/String;Llocal/stalin/logic/Sort;)V");
#else
    mtvinit = safegetmethodid(env,env->GetObjectClass(theory),
			      "createTermVariable","(Ljava/lang/String;Llocal/"
			      "stalin/logic/Sort;)Llocal/stalin/logic/"
			      "TermVariable;");
#endif
    env->DeleteLocalRef(tmp);
    tmp = safegetclass(env,"local/stalin/logic/Sort");
    msortcls = static_cast<jclass>(env->NewGlobalRef(tmp));
    assert(msortcls);
    env->DeleteLocalRef(tmp);
    tmp = safegetclass(env,"local/stalin/logic/Term");
    mtermcls = static_cast<jclass>(env->NewGlobalRef(tmp));
    assert(mtermcls);
    env->DeleteLocalRef(tmp);
    tmp = env->GetObjectClass(theory);
    mnot = safegetmethodid(env,tmp,"notz3",
			   "(Llocal/stalin/logic/Formula;)"
			   "Llocal/stalin/logic/Formula;");
    mand = safegetmethodid(env,tmp,"andz3",
			   "(Llocal/stalin/logic/Formula;"
			   "Llocal/stalin/logic/Formula;)"
			   "Llocal/stalin/logic/Formula;");
    mor = safegetmethodid(env,tmp,"orz3",
			  "(Llocal/stalin/logic/Formula;"
			  "Llocal/stalin/logic/Formula;)"
			  "Llocal/stalin/logic/Formula;");
    mimplies = safegetmethodid(env,tmp,"impliesz3",
			       "(Llocal/stalin/logic/Formula;"
			       "Llocal/stalin/logic/Formula;)"
			       "Llocal/stalin/logic/Formula;");
    mxor = safegetmethodid(env,tmp,"xorz3",
			   "(Llocal/stalin/logic/Formula;"
			   "Llocal/stalin/logic/Formula;)"
			   "Llocal/stalin/logic/Formula;");
    miff = safegetmethodid(env,tmp,"iffz3",
			   "(Llocal/stalin/logic/Formula;"
			   "Llocal/stalin/logic/Formula;)"
			   "Llocal/stalin/logic/Formula;");
    moeq = safegetmethodid(env,tmp,"oeq",
			   "(Llocal/stalin/logic/Formula;"
			   "Llocal/stalin/logic/Formula;)"
			   "Llocal/stalin/logic/Formula;");
    mitet = safegetmethodid(env,tmp,"itez3",
			    "(Llocal/stalin/logic/Formula;"
			    "Llocal/stalin/logic/Term;"
			    "Llocal/stalin/logic/Term;)"
			    "Llocal/stalin/logic/Term;");
    mitef = safegetmethodid(env,tmp,"ifthenelsez3",
			    "(Llocal/stalin/logic/Formula;"
			    "Llocal/stalin/logic/Formula;"
			    "Llocal/stalin/logic/Formula;)"
			    "Llocal/stalin/logic/Formula;");
    mgetfunc = safegetmethodid(env,tmp,"getFunction",
			       "(Ljava/lang/String;"
			       "[Llocal/stalin/logic/Sort;)"
			       "Llocal/stalin/logic/FunctionSymbol;");
    mgetpred = safegetmethodid(env,tmp,"getPredicate",
			       "(Ljava/lang/String;"
			       "[Llocal/stalin/logic/Sort;)"
			       "Llocal/stalin/logic/PredicateSymbol;");
    mgetsort = safegetmethodid(env,tmp,"getSort",
			       "(Ljava/lang/String;)Llocal/stalin/logic/Sort;");
    mcreatefunc = safegetmethodid(env,tmp,"createFunction",
				  "(Ljava/lang/String;"
				  "[Llocal/stalin/logic/Sort;"
				  "Llocal/stalin/logic/Sort;)"
				  "Llocal/stalin/logic/FunctionSymbol;");
    mcreatepred = safegetmethodid(env,tmp,"createPredicate",
				  "(Ljava/lang/String;"
				  "[Llocal/stalin/logic/Sort;)"
				  "Llocal/stalin/logic/PredicateSymbol;");
    matom = safegetmethodid(env,tmp,"atom",
			    "(Llocal/stalin/logic/PredicateSymbol;"
			    "[Llocal/stalin/logic/Term;)"
			    "Llocal/stalin/logic/Atom;");
    mterm = safegetmethodid(env,tmp,"term",
			    "(Llocal/stalin/logic/FunctionSymbol;"
			    "[Llocal/stalin/logic/Term;)"
			    "Llocal/stalin/logic/ApplicationTerm;");
    mequals = safegetmethodid(env,tmp,"equalsz3","([Llocal/stalin/logic/Term;)"
			      "Llocal/stalin/logic/Atom;");
    mdistinct = safegetmethodid(env,tmp,"distinctz3",
				"([Llocal/stalin/logic/Term;)"
				"Llocal/stalin/logic/Atom;");
    mtvterm = safegetmethodid(env,tmp,"term",
			      "(Llocal/stalin/logic/TermVariable;)"
			      "Llocal/stalin/logic/Term;");
    mrational = safegetmethodid(env,tmp,"rational","(Ljava/lang/String;"
				"Ljava/lang/String;)Llocal/stalin/logic/Term;");
    mnumeral = safegetmethodid(env,tmp,"numeral","(Ljava/lang/String;)"
			       "Llocal/stalin/logic/Term;");
    mexists = safegetmethodid(env,tmp,"exists",
			      "([Llocal/stalin/logic/TermVariable;"
			      "Llocal/stalin/logic/Formula;)"
			      "Llocal/stalin/logic/Formula;");
    mforall = safegetmethodid(env,tmp,"forall",
			      "([Llocal/stalin/logic/TermVariable;"
			      "Llocal/stalin/logic/Formula;)"
			      "Llocal/stalin/logic/Formula;");
 } catch( ... ) {
    if( mprcls )
      env->DeleteGlobalRef(mprcls);
    if( mtheory )
      env->DeleteGlobalRef(mtheory);
    if( mtrue )
      env->DeleteGlobalRef(mtrue);
    if( mfalse )
      env->DeleteGlobalRef(mfalse);
    if( mtv )
      env->DeleteGlobalRef(mtv);
    if( msortcls )
      env->DeleteGlobalRef(msortcls);
    if( mtermcls )
      env->DeleteGlobalRef(mtermcls);
    throw;
  }
}

void genformulactx::release(JNIEnv* env) {
  if( mprcls )
    env->DeleteGlobalRef(mprcls);
  if( mtheory )
    env->DeleteGlobalRef(mtheory);
  if( mtrue )
    env->DeleteGlobalRef(mtrue);
  if( mfalse )
    env->DeleteGlobalRef(mfalse);
  if( mtv )
    env->DeleteGlobalRef(mtv);
  if( msortcls )
    env->DeleteGlobalRef(msortcls);
  if( mtermcls )
    env->DeleteGlobalRef(mtermcls);
  transiter end = mknowntrans.end();
  for( transiter it = mknowntrans.begin(); it != end; ++it )
    env->DeleteGlobalRef(it->second);
  sortiter send = msorts.end();
  for( sortiter it = msorts.begin(); it != send; ++it )
    env->DeleteGlobalRef(it->second);
  termiter tend = mtermvars.end();
  for( termiter it = mtermvars.begin(); it != tend; ++it )
    env->DeleteGlobalRef(it->second);
  funciter fend = mfuncdecls.end();
  for( funciter it = mfuncdecls.begin(); it != fend; ++it )
    env->DeleteGlobalRef(it->second);
  priter pend = mknownprs.end();
  for( priter it = mknownprs.begin(); it != pend; ++it )
      env->DeleteGlobalRef(it->second);
}

static const char* getsymbolname(JNIEnv* env,Z3_context c,Z3_symbol s) {
  switch( Z3_get_symbol_kind(c,s) ) {
  case Z3_STRING_SYMBOL:
    return Z3_get_symbol_string(c,s);
  case Z3_INT_SYMBOL:
    // TODO: How to convert int symbols???
    // Z3_get_symbol_int(c,s);
  default:
      thrownativecodeexception(env,"Unknown Z3 symbol in getsymbolname");
    throw pendingjavaexc();
  }
}

/**
 * Convert a Z3 sort into a java sort.
 * Contract: Returns a local reference to the sort object.
 */
jobject genformulactx::convertsort(JNIEnv* env,Z3_sort sort) {
#ifdef DEBUG_PROOFTREEPARSING
  scopeprinter sp("convertsort");
#endif
#if 1
  sortiter it = msorts.find(sort);
  if( it != msorts.end() )
    return env->NewLocalRef(it->second);
#endif
  // Might need returnvalue and string
  localframehelper lfh(env,2);
  switch( Z3_get_sort_kind(mctx,sort) ) {
  case Z3_BOOL_SORT:
    // 0 indicates bool sort
    return 0;
  case Z3_UNINTERPRETED_SORT: {
    jstring name = 
      env->NewStringUTF(getsymbolname(env,mctx,Z3_get_sort_name(mctx,sort)));
    jobject jsort = env->CallObjectMethod(mtheory,mgetsort,name);
    if( env->ExceptionCheck() )
      throw pendingjavaexc();
    env->DeleteLocalRef(name);
    jobject gsort = env->NewGlobalRef(jsort);
    assert(gsort);
    msorts.insert(std::make_pair(sort,gsort));
    return lfh.popframe(jsort);
  }
  case Z3_INT_SORT: {
    jstring name = env->NewStringUTF("Int");
    jobject jsort = env->CallObjectMethod(mtheory,mgetsort,name);
    if( env->ExceptionCheck() )
      throw pendingjavaexc();
    env->DeleteLocalRef(name);
    jobject gsort = env->NewGlobalRef(jsort);
    assert(gsort);
    msorts.insert(std::make_pair(sort,gsort));
    return lfh.popframe(jsort);
  }
  case Z3_REAL_SORT: {
    jstring name = env->NewStringUTF("Real");
    jobject jsort = env->CallObjectMethod(mtheory,mgetsort,name);
    if( env->ExceptionCheck() )
      throw pendingjavaexc();
    env->DeleteLocalRef(name);
    jobject gsort = env->NewGlobalRef(jsort);
    assert(gsort);
    msorts.insert(std::make_pair(sort,gsort));
    return lfh.popframe(jsort);
  }
  default:
      thrownativecodeexception(env,"Unknown Z3 sort in convertsort");
    throw pendingjavaexc();
  }
}

/**
 * Convert an ast into a java formula.
 * Contract: Returns a local reference to the formula object.
 */
jobject genformulactx::convertast(JNIEnv* env,Z3_ast ast) {
#ifdef DEBUG_PROOFTREEPARSING
  scopeprinter sc("convertast");
#endif
#if 1
  transiter it = mknowntrans.find(ast);
  if( it != mknowntrans.end() )
    return env->NewLocalRef(it->second);
#endif
  switch( Z3_get_ast_kind(mctx,ast) ) {
  case Z3_NUMERAL_AST: {
#ifdef DEBUG_PROOFTREEPARSING
      std::cerr << "NUMERAL_AST" << std::endl;
#endif
    Z3_sort s = Z3_get_sort(mctx,ast);
    const char* val = Z3_get_numeral_string(mctx,ast);
    if( Z3_get_sort_kind(mctx,s) == Z3_INT_SORT ) {
      localframehelper lfh(env,2);
      jstring jstr = env->NewStringUTF(val);
      jobject res = env->CallObjectMethod(mtheory,mnumeral,jstr);
      jobject gres = env->NewGlobalRef(res);
      assert(gres);
      mknowntrans.insert(std::make_pair(ast,gres));
      return lfh.popframe(res);
    } else {
      assert(Z3_get_sort_kind(mctx,s) == Z3_REAL_SORT);
      localframehelper lfh(env,3);
      const char* denom = std::strchr(val,'/');
      jstring jnum,jdenom;
      if( denom ) {
	jnum = newjavastring(env,val,denom - val);
	jdenom = env->NewStringUTF(denom+1);
      } else {
	jnum = env->NewStringUTF(val);
	jdenom = 0;
      }
      jobject res = env->CallObjectMethod(mtheory,mrational,jnum,jdenom);
      if( env->ExceptionCheck() )
	throw pendingjavaexc();
      jobject gres = env->NewGlobalRef(res);
      assert(gres);
      mknowntrans.insert(std::make_pair(ast,gres));
      return lfh.popframe(res);
    }
  }
  case Z3_APP_AST: {
#ifdef DEBUG_PROOFTREEPARSING
      std::cerr << "APP_AST" << std::endl;
#endif
    Z3_app app = Z3_to_app(mctx,ast);
    jobject japp = convertapp(env,app);
    jobject gapp = env->NewGlobalRef(japp);
    assert(gapp);
    mknowntrans.insert(std::make_pair(ast,gapp));
    return japp;
  }
  case Z3_QUANTIFIER_AST: {
#ifdef DEBUG_PROOFTREEPARSING
      std::cerr << "QUANTIFIER_AST" << std::endl;
      std::cerr << Z3_ast_to_string(mctx,ast) << std::endl;
#endif
    // array,sort,name,var
    localframehelper lfh(env,4);
    bool isforall = Z3_is_quantifier_forall(mctx,ast);
    unsigned int numbound = Z3_get_quantifier_num_bound(mctx,ast);
    jobjectArray bvars = env->NewObjectArray(numbound,mtv,0);
    if( !bvars )
      throw pendingjavaexc();
    for( unsigned int i = 0; i < numbound; ++i ) {
      Z3_sort sort = Z3_get_quantifier_bound_sort(mctx,ast,i);
      Z3_symbol symb = Z3_get_quantifier_bound_name(mctx,ast,i);
      jobject jsort = convertsort(env,sort);
      jstring jname = env->NewStringUTF(getsymbolname(env,mctx,symb));
      if( !jname )
	throw pendingjavaexc();
#if 0
      jobject bv = env->NewObject(mtv,mtvinit,jname,jsort);
#else
      jobject bv = env->CallObjectMethod(mtheory,mtvinit,jname,jsort);
#endif
      if( !bv )
	throw pendingjavaexc();
      env->DeleteLocalRef(jsort);
      env->DeleteLocalRef(jname);
      env->SetObjectArrayElement(bvars,i,bv);
      if( env->ExceptionCheck() ) {
#ifdef DEBUG_PROOFTREEPARSING
	std::cerr << "Failed to convert " << Z3_ast_to_string(mctx,ast) << 
	  std::endl;
#endif
	throw pendingjavaexc();
      }
      jobject gbv = env->NewGlobalRef(bv);
      assert(gbv);
      env->DeleteLocalRef(bv);
      mtermvars.insert(std::make_pair(mnumbound++,gbv));
    }
    // TODO: Should patterns be converted as well???
    jobject body = convertast(env,Z3_get_quantifier_body(mctx,ast));
    jobject res = env->CallObjectMethod(mtheory,isforall ? mforall : mexists,
					bvars,body);
    env->DeleteLocalRef(bvars);
    env->DeleteLocalRef(body);
    jobject gres = env->NewGlobalRef(res);
    assert(gres);
    mknowntrans.insert(std::make_pair(ast,gres));
    for( unsigned int i = 0; i < numbound; ++i ) {
	std::map<unsigned int,jobject>::iterator it = mtermvars.find(
	    --mnumbound);
	assert(it != mtermvars.end());
	env->DeleteGlobalRef(it->second);
	mtermvars.erase(it);
    }
    return lfh.popframe(res);
  }
  case Z3_VAR_AST: {
#ifdef DEBUG_PROOFTREEPARSING
      std::cerr << "VAR_AST" << std::endl;
#endif
    unsigned int idx = Z3_get_index_value(mctx,ast);
    if( idx >= mnumbound ) {
	// string, termvariable, sort, term
	localframehelper lh(env,2);
	// Should be reasonably large
	char idxname[15];
	sprintf(idxname,"unknown%u",idx - mnumbound);
	jstring name = newjavastring(env,idxname);
	jobject ntv = env->CallObjectMethod(mtheory,mtvinit,name,0);
	env->DeleteLocalRef(name);
	jobject res = env->CallObjectMethod(mtheory,mtvterm,ntv);
	return lh.popframe(res);
    } else {
	unsigned int idx = mnumbound - Z3_get_index_value(mctx,ast) - 1;
	termiter it = mtermvars.find(idx);
	if( it == mtermvars.end() ) {
	    // TODO: How should this case be handled???
	    thrownativecodeexception(env,"Did not find term variable");
	    throw pendingjavaexc();
	}
	// No unification on indexes!!!
	return env->CallObjectMethod(mtheory,mtvterm,it->second);
    }
  }
  case Z3_UNKNOWN_AST:
      thrownativecodeexception(env,
			       "Don't know how to convert an unkown ast type");
    throw pendingjavaexc();
  }
  return 0;
}

static void replaceExclamationMark(std::string& in) {
    while (true) {
	const int pos = in.find("!");
	if (pos == -1)
	    break;
	in.replace(pos,1,"_b");
    }
}

/**
 * Translate a Z3 function declaration into a FunctionSymbol or PredicateSymbol.
 * Contract: Returns a local reference.
 */
jobject genformulactx::getfunc(JNIEnv* env,Z3_func_decl fd,bool& ispred) {
  Z3_sort range = Z3_get_range(mctx,fd);
  ispred = Z3_get_sort_kind(mctx,range) == Z3_BOOL_SORT;
#if 1
  funciter it = mfuncdecls.find(fd);
  if( it != mfuncdecls.end() )
    return env->NewLocalRef(it->second);
#endif
  // sortarray,sort,name,result
  localframehelper lfh(env,4);
  unsigned int numsorts = Z3_get_domain_size(mctx,fd);
  jobjectArray sorts = env->NewObjectArray(numsorts,msortcls,0);
  for( unsigned int i = 0; i < numsorts; ++i ) {
    jobject sort = convertsort(env,Z3_get_domain(mctx,fd,i));
    env->SetObjectArrayElement(sorts,i,sort);
#ifdef DEBUG_PROOFTREEPARSING
    if( env->ExceptionCheck() )
      throw pendingjavaexc();
#endif
    env->DeleteLocalRef(sort);
  }
  const char* tmp = getsymbolname(env,mctx,Z3_get_decl_name(mctx,fd));
  std::string buf(tmp);
  replaceExclamationMark(buf);
  jstring str = env->NewStringUTF(buf.c_str());
  if( !str )
    throw pendingjavaexc();
  jobject res = env->CallObjectMethod(mtheory,ispred ? mgetpred : mgetfunc,str,
				      sorts);
  if( env->ExceptionCheck() )
    throw pendingjavaexc();
  if( !res ) {
#if 0
      thrownativecodeexception(
	  env,"Unable to retrieve predicate of function symbol");
    throw pendingjavaexc();
#endif
    jobject ressort = convertsort(env,Z3_get_range(mctx,fd));
    res = ispred ? env->CallObjectMethod(mtheory,mcreatepred,str,sorts) : 
	env->CallObjectMethod(mtheory,mcreatefunc,str,sorts,ressort);
    env->DeleteLocalRef(ressort);
  }
  jobject gres = env->NewGlobalRef(res);
  assert(gres);
  mfuncdecls.insert(std::make_pair(fd,gres));
  return lfh.popframe(res);
}

jobjectArray genformulactx::convertparams(JNIEnv* env,Z3_app app) {
#if (defined DEBUG_PROOFTREEPARSING) && 1
  std::cerr << "Converting app " << Z3_ast_to_string(mctx,Z3_app_to_ast(mctx,app)) << std::endl;
#endif
  localframehelper lfh(env,2);
  unsigned int numargs = Z3_get_app_num_args(mctx,app);
  jobjectArray args = env->NewObjectArray(numargs,mtermcls,0);
  if( !args )
    throw pendingjavaexc();
  for( unsigned int i = 0; i < numargs; ++i ) {
    jobject arg = convertast(env,Z3_get_app_arg(mctx,app,i));
    env->SetObjectArrayElement(args,i,arg);
#ifdef DEBUG_PROOFTREEPARSING
    if( env->ExceptionCheck() ) {
      std::cerr << "Failed to convert parameters" << std::endl;
      throw pendingjavaexc();
    }
#endif
    env->DeleteLocalRef(arg);
  }
  return static_cast<jobjectArray>(lfh.popframe(args));
}

/**
 * Convert a function application into an ApplicationTerm or PredicateAtom or
 * Atom.TRUE or Atom.FALSE.
 * Contract: Returns a local reference.
 */
jobject genformulactx::convertapp(JNIEnv* env,Z3_app app) {
  Z3_func_decl d = Z3_get_app_decl(mctx,app);
  Z3_decl_kind dk = Z3_get_decl_kind(mctx,d);
#ifdef DEBUG_PROOFTREEPARSING
  std::cerr << "convertapp: " << Z3_ast_to_string(mctx,Z3_app_to_ast(mctx,app)) << "\ndk = " << dk << std::endl;
#endif
  switch( dk ) {
  case Z3_OP_UNINTERPRETED:
  case Z3_OP_LE:
  case Z3_OP_GE:
  case Z3_OP_LT:
  case Z3_OP_GT:
  case Z3_OP_ADD:
  case Z3_OP_SUB:
  case Z3_OP_UMINUS:
  case Z3_OP_MUL:
  case Z3_OP_DIV:
  case Z3_OP_IDIV: {
    localframehelper lfh(env,3);
    bool ispred;
    jobject fs = getfunc(env,d,ispred);
    jobjectArray args = convertparams(env,app);
    jobject res = env->CallObjectMethod(mtheory,ispred ? matom : mterm,fs,args);
    if( env->ExceptionCheck() )
      throw pendingjavaexc();
    return lfh.popframe(res);
  }
  case Z3_OP_TRUE:
    return env->NewLocalRef(mtrue);
  case Z3_OP_FALSE:
    return env->NewLocalRef(mfalse);
  case Z3_OP_EQ: {
    localframehelper lfh(env,2);
    jobject args = convertparams(env,app);
    jobject res = env->CallObjectMethod(mtheory,mequals,args);
    if( env->ExceptionCheck() )
      throw pendingjavaexc();
    return lfh.popframe(res);
  }
  case Z3_OP_DISTINCT: {
    localframehelper lfh(env,2);
    jobject args = convertparams(env,app);
    jobject res = env->CallObjectMethod(mtheory,mdistinct,args);
    if( env->ExceptionCheck() )
      throw pendingjavaexc();
    return lfh.popframe(res);
  }
  case Z3_OP_ITE: {
    /* Hack to disambiguate between ITETerm and ITEFormula:
     * ITETerm: if <bool> then <U> else <U>
     * ITEFormula: if <bool> then <bool> else <bool>
     */
    assert(Z3_get_app_num_args(mctx,app) == 3);
    // cond,then,else,res
    localframehelper lfh(env,4);
    bool isformula = 
      Z3_get_sort_kind(mctx,Z3_get_domain(mctx,d,1)) == Z3_BOOL_SORT;
    jobject cond = convertast(env,Z3_get_app_arg(mctx,app,0));
    jobject tc = convertast(env,Z3_get_app_arg(mctx,app,1));
    jobject ec = convertast(env,Z3_get_app_arg(mctx,app,2));
    jobject res = env->CallObjectMethod(mtheory,isformula ? mitef : mitet,
					cond,tc,ec);
    if( env->ExceptionCheck() )
      throw pendingjavaexc();
    return lfh.popframe(res);
  }
  case Z3_OP_AND: {
    // n-ary and!!!
    unsigned int numargs = Z3_get_app_num_args(mctx,app);
    assert(numargs != 0);
    if( numargs == 1 )
      return convertast(env,Z3_get_app_arg(mctx,app,0));
    // lhs,rhs,res
    localframehelper lfh(env,3);
    jobject rhs = convertast(env,Z3_get_app_arg(mctx,app,--numargs));
    jobject res;
    do {
      jobject lhs = convertast(env,Z3_get_app_arg(mctx,app,--numargs));
      res = env->CallObjectMethod(mtheory,mand,lhs,rhs);
      env->DeleteLocalRef(rhs);
      env->DeleteLocalRef(lhs);
      rhs = res;
    } while( numargs > 0 );
    return lfh.popframe(res);
  }
  case Z3_OP_OR: {
    // n-ary and!!!
    unsigned int numargs = Z3_get_app_num_args(mctx,app);
    assert(numargs > 1);
    // lhs,rhs,res
    localframehelper lfh(env,3);
    jobject rhs = convertast(env,Z3_get_app_arg(mctx,app,--numargs));
    jobject res;
    do {
      jobject lhs = convertast(env,Z3_get_app_arg(mctx,app,--numargs));
      res = env->CallObjectMethod(mtheory,mor,lhs,rhs);
      env->DeleteLocalRef(rhs);
      env->DeleteLocalRef(lhs);
      rhs = res;
    } while( numargs > 0 );
    return lfh.popframe(res);
  }
  case Z3_OP_IFF: {
    assert(Z3_get_app_num_args(mctx,app) == 2);
    // lhs,rhs,res
    localframehelper lfh(env,3);
    jobject lhs = convertast(env,Z3_get_app_arg(mctx,app,0));
    jobject rhs = convertast(env,Z3_get_app_arg(mctx,app,1));
    jobject res = env->CallObjectMethod(mtheory,miff,lhs,rhs);
    return lfh.popframe(res);
  }
  case Z3_OP_XOR: {
    assert(Z3_get_app_num_args(mctx,app) == 2);
    // lhs,rhs,res
    localframehelper lfh(env,3);
    jobject lhs = convertast(env,Z3_get_app_arg(mctx,app,0));
    jobject rhs = convertast(env,Z3_get_app_arg(mctx,app,1));
    jobject res = env->CallObjectMethod(mtheory,mxor,lhs,rhs);
    return lfh.popframe(res);
  }
  case Z3_OP_NOT: {
    assert(Z3_get_app_num_args(mctx,app) == 1);
    // sub,res
    localframehelper lfh(env,2);
    jobject sub = convertast(env,Z3_get_app_arg(mctx,app,0));
    jobject res = env->CallObjectMethod(mtheory,mnot,sub);
    return lfh.popframe(res);
  }
  case Z3_OP_IMPLIES: {
    assert(Z3_get_app_num_args(mctx,app) == 2);
    // lhs,rhs,res
    localframehelper lfh(env,3);
    jobject lhs = convertast(env,Z3_get_app_arg(mctx,app,0));
    jobject rhs = convertast(env,Z3_get_app_arg(mctx,app,1));
    jobject res = env->CallObjectMethod(mtheory,mimplies,lhs,rhs);
    return lfh.popframe(res);
  }
  case Z3_OP_OEQ: {
    assert(Z3_get_app_num_args(mctx,app) == 2);
    // lhs,rhs,res
    localframehelper lfh(env,3);
    jobject lhs = convertast(env,Z3_get_app_arg(mctx,app,0));
    jobject rhs = convertast(env,Z3_get_app_arg(mctx,app,1));
    jobject res = env->CallObjectMethod(mtheory,moeq,lhs,rhs);
    return lfh.popframe(res);
  }
  default:
      thrownativecodeexception(env,"Unkown connective");
    throw pendingjavaexc();
  }
}

/**
 * Parser for formulae asts.
 */
static jobject genformula(JNIEnv* env,Z3_context c,Z3_ast a,
			  genformulactx& gfctx) {
#ifdef DEBUG_PROOFTREEPARSING
  scopeprinter sc("genformula");
#endif
#if 0
  Z3_set_ast_print_mode(c,Z3_PRINT_SMTLIB_FULL);
  Z3_string str = Z3_ast_to_string(c,a);
  return newjavastring(env,str);
#else
  return gfctx.convertast(env,a);
#endif
}

/**
 * Parser for a proof ast.
 */
static jobject genrule(JNIEnv* env,jclass cls,Z3_context c,Z3_app app,
		       genformulactx& gfctx) {
#ifdef DEBUG_PROOFTREEPARSING
  scopeprinter sc("genrule");
#endif
  genformulactx::priter it = gfctx.mknownprs.find(app);
  if( it != gfctx.mknownprs.end() ) {
      ++gfctx.numunifies;
      return env->NewLocalRef(it->second);
  }
  unsigned int numargs = Z3_get_app_num_args(c,app);
  Z3_func_decl d = Z3_get_app_decl(c,app);
  Z3_decl_kind dk = Z3_get_decl_kind(c,d);
  assert( !(dk < Z3_OP_PR_TRUE || dk == Z3_OP_UNINTERPRETED) );
  // Try to only use 2 local references
  localframehelper lfh(env,2);
  // Local reference #1
  jobject res = env->NewObject(cls,idcache.proofconstruct,dk-Z3_OP_PR_TRUE,
    numargs-1);
  if( !res )
    throw pendingjavaexc();
  for( unsigned int i = 0; i < numargs - 1; ++i ) {
    // Local reference #2
    Z3_app arg = Z3_to_app(c,Z3_get_app_arg(c,app,i));
    jobject pr = genrule(env,cls,c,arg,gfctx);
    // pr is valid since otherwise, an exception gets thrown!!!
    env->CallVoidMethod(res,idcache.proofaddrule,pr,i);
    // #2 is not needed anymore!!!
    env->DeleteLocalRef(pr);
  }
  // Local reference #2
  jobject formula = genformula(env,c,Z3_get_app_arg(c,app,numargs - 1),gfctx);
  // formula is valid. Otherwise an exception gets thrown!!!
  env->SetObjectField(res,idcache.proofresult,formula);
  gfctx.mknownprs.insert(std::make_pair(app,env->NewGlobalRef(res)));
  ++gfctx.numrules;
  // This deletes both local references and pushes res into another frame...
  return lfh.popframe(res);
}

static void genskolemsinsts(JNIEnv* env,Z3_context c,Z3_app app,
			    genformulactx& gfctx,jobject skolems,jobject insts,
			    jmethodID addID) {
#ifdef DEBUG_PROOFTREEPARSING
  scopeprinter sc("genskolemsinsts");
#endif
  genformulactx::priter it = gfctx.mknownprs.find(app);
  if( it != gfctx.mknownprs.end() ) {
//      ++gfctx.numunifies;
//      return env->NewLocalRef(it->second);
      return;
  }
  gfctx.mknownprs.insert(std::make_pair(app,static_cast<jobject>(0)));
  unsigned int numargs = Z3_get_app_num_args(c,app);
  Z3_func_decl d = Z3_get_app_decl(c,app);
  Z3_decl_kind dk = Z3_get_decl_kind(c,d);
  assert( !(dk < Z3_OP_PR_TRUE || dk == Z3_OP_UNINTERPRETED) );
  if (dk == Z3_OP_PR_SKOLEMIZE) {
      localframehelper lfh(env,1);
      jobject formula = genformula(env,c,Z3_get_app_arg(c,app,0),
				   gfctx);
      env->CallObjectMethod(skolems,addID,lfh.popframe(formula));
      return;
  }
  if (dk == Z3_OP_PR_QUANT_INST) {
      localframehelper lfh(env,1);
      jobject formula = genformula(env,c,Z3_get_app_arg(c,app,0),
				   gfctx);
      env->CallObjectMethod(insts,addID,lfh.popframe(formula));
      return;
  }
  for( unsigned int i = 0; i < numargs - 1; ++i ) {
    Z3_app arg = Z3_to_app(c,Z3_get_app_arg(c,app,i));
    genskolemsinsts(env,c,arg,gfctx,skolems,insts,addID);
  }
}

static void getskolemsinsts(JNIEnv* env,Z3_context ctx,Z3_ast proof,
			    jobject theory,jobject skolems,jobject insts,
			    jmethodID addID) {
#ifndef NPROFILE
    time_t starttime = std::time(0);
#endif
    genformulactx gfctx(env,ctx,theory);
    assert(Z3_get_ast_kind(ctx,proof)==Z3_APP_AST);
    genskolemsinsts(env,ctx,Z3_to_app(ctx,proof),gfctx,skolems,insts,addID);
    gfctx.release(env);
#ifndef NPROFILE
    std::cerr << "Extracting skolemizations and instances took " << 
	std::time(0) - starttime << " seconds" << std::endl;
#endif
}

/**
 * Initialize recursive parsing and set result in Java object.
 */
static void parseproof(JNIEnv* env,jobject obj,Z3_context c,Z3_ast proof,
		       jobject theory) {
#if 0
  std::cerr << "Parsing Z3 proof " << Z3_ast_to_string(c,proof) << std::endl;
#endif
  jclass prcls = safegetclass(env,"local/stalin/nativez3/Z3ProofRule");
  genformulactx gfctx(env,c,theory);
  assert(Z3_get_ast_kind(c,proof)==Z3_APP_AST);
  jobject pr = genrule(env,prcls,c,Z3_to_app(c,proof),gfctx);
  gfctx.release(env);
  env->SetObjectField(obj,idcache.contextproof,pr);
  env->DeleteLocalRef(pr);
  env->DeleteLocalRef(prcls);
  std::cout << "Parsed Z3-Proof: " << gfctx.numrules << " Rules " << gfctx.numunifies << " unified!" << std::endl;
}

/**
 * The error handler function installed into Z3. It simply throws an exception
 * and hopefully runs up to our check routine where it gets caught and
 * transformed into a Java Exception of class local.stalin.nativez3.Z3Exception.
 */
static void z3errhandler(Z3_error_code e) {
#ifndef NDEBUG
    std::cerr << "z3errhandler called with errorcode " << e << std::endl;
#endif
  throw z3error(e);
}

/**
 * Helper function to retrieve the context out of an object.
 */
static inline Z3_context getz3context(JNIEnv* env,jobject obj) {
  return 
    reinterpret_cast<Z3_context>(env->GetLongField(obj,idcache.contextstore));
}

/**
 * Function corresponding to local.stalin.nativez3.Z3Context.initZ3(long).
 */
static void STALIN_CALL initz3(JNIEnv* env,jobject obj,jlong lcfg) {
  Z3_config cfg = reinterpret_cast<Z3_config>(lcfg);
  Z3_context ctx = Z3_mk_context(cfg);
  // Register our error handler
  Z3_set_error_handler(ctx,z3errhandler);
  env->SetLongField(obj,idcache.contextstore,reinterpret_cast<jlong>(ctx));
}

/**
 * Function corresponding to local.stalin.nativez3.Z3Context.deinitializeZ3().
 */
static void STALIN_CALL deinitz3(JNIEnv* env,jobject obj) {
  Z3_context ctx = getz3context(env,obj);
  Z3_del_context(ctx);
}

/**
 * Function corresponding to local.stalin.nativez3.Z3Context.push().
 */
static void STALIN_CALL ctxpush(JNIEnv* env,jobject obj) {
  try {
    Z3_context ctx = getz3context(env,obj);
    Z3_push(ctx);
  } catch( const z3error& err ) {
    throwz3exception(env,err.errorcode());
  }
}

/**
 * Function corresponding to local.stalin.nativez3.Z3Context.push().
 */
static void STALIN_CALL ctxpop(JNIEnv* env,jobject obj,jint npops) {
  try {
    Z3_context ctx = getz3context(env,obj);
    Z3_pop(ctx,npops);
  } catch( const z3error& err ) {
    throwz3exception(env,err.errorcode());
  }
}

/**
 * Function corresponding to local.stalin.nativez3.Z3Context.check()
 */
static jint STALIN_CALL z3check(JNIEnv* env,jobject obj) {
  try {
    Z3_context ctx = getz3context(env,obj);
    Z3_lbool res = Z3_check(ctx);
#ifndef NDEBUG
    std::cerr << "check returned " << res << std::endl;
#endif
    jint failure = Z3_NO_FAILURE;
    if( res == Z3_L_UNDEF )
      // Here, we have a search failure
      failure = static_cast<jint>(Z3_get_search_failure(ctx));
    env->SetIntField(obj,idcache.contextfailure,failure);
    return static_cast<jint>(res);
  } catch( const z3error& err ) {
    throwz3exception(env,err.errorcode());
  }
  // Need this for the compiler...
  return 0;
}

/**
 * Function corresponding to local.stalin.nativez3.Z3Context.checkAndGetProof()
 */
static jint STALIN_CALL z3checkgetproof(JNIEnv* env,jobject obj,
					jobject theory) {
  try {
    Z3_context ctx = getz3context(env,obj);
    Z3_ast proof;
    Z3_model model;
    Z3_lbool res = Z3_check_assumptions(ctx,0,0,&model,&proof,0,0);
#ifndef NDEBUG
    std::cerr << "check returned " << res << std::endl;
#endif
    jint failure = Z3_NO_FAILURE;
    if( res == Z3_L_UNDEF )
      // Here, we have a search failure
      failure = static_cast<jint>(Z3_get_search_failure(ctx));
    env->SetIntField(obj,idcache.contextfailure,failure);
    if( res == Z3_L_FALSE ) {
	if( proof ) {
#ifndef NDEBUG
	    std::cerr << "Start parsing proof" << std::endl;
#endif
	    parseproof(env,obj,ctx,proof,theory);
#ifndef NDEBUG
	    std::cerr << "Finished parsing proof" << std::endl;
#endif
	}
    } else {
      if( model ) {
#ifndef NDEBUG
	std::cerr << "Model:\n" << Z3_model_to_string(ctx,model) << std::endl;
#endif
	Z3_del_model(ctx,model);
      }
    }
    return static_cast<jint>(res);
  } catch( const z3error& err ) {
    throwz3exception(env,err.errorcode());
  } catch( const pendingjavaexc& exc ) {
    // Just says: There is an exception to be handled in Java!!!
  }
  return 0;
}

/**
 * Function corresponding to local.stalin.nativez3.Z3Context.checkAndGetProof()
 */
static jint STALIN_CALL z3checkgetskolemsinsts(JNIEnv* env,jobject obj,
					       jobject theory,
					       jobject skolems,jobject insts) {
    try {
	Z3_context ctx = getz3context(env,obj);
	Z3_ast proof;
	Z3_model model;
	Z3_lbool res = Z3_check_assumptions(ctx,0,0,&model,&proof,0,0);
#ifndef NDEBUG
	std::cerr << "check returned " << res << std::endl;
#endif
	jint failure = Z3_NO_FAILURE;
	if( res == Z3_L_UNDEF )
	    // Here, we have a search failure
	    failure = static_cast<jint>(Z3_get_search_failure(ctx));
	env->SetIntField(obj,idcache.contextfailure,failure);
	if( res == Z3_L_FALSE ) {
	    if( proof ) {
		jmethodID addID;
		{
		    localframehelper lfh(env,1);
		    jclass cls = env->GetObjectClass(insts);
		    addID = safegetmethodid(env,cls,"add",
					    "(Ljava/lang/Object;)Z");
		}
		getskolemsinsts(env,ctx,proof,theory,skolems,insts,addID);
	    }
	} else {
	    if( model ) {
#ifndef NDEBUG
		std::cerr << "Model:\n" << Z3_model_to_string(ctx,model) << 
		    std::endl;
#endif
		Z3_del_model(ctx,model);
	    }
	}
	return static_cast<jint>(res);
    } catch( const z3error& err ) {
	throwz3exception(env,err.errorcode());
    } catch( const pendingjavaexc& exc ) {
	// Just says: There is an exception to be handled in Java!!!
    }
    return 0;
}

/**
 * Function corresponding to local.stalin.nativez3.Z3Context.cancelCheck()
 */
static void STALIN_CALL z3cancelcheck(JNIEnv* env,jobject obj) {
  Z3_context ctx = getz3context(env,obj);
  Z3_soft_check_cancel(ctx);
}

// Structure always has function_name function_signature function_implementation
static JNINativeMethod contextmethods[] = {
  STALIN_NMETHOD("initZ3","(J)V",initz3),
  STALIN_NMETHOD("deinitializeZ3","()V",deinitz3),
  STALIN_NMETHOD("push","()V",ctxpush),
  STALIN_NMETHOD("pop","(I)V",ctxpop),
  STALIN_NMETHOD("check","()I",z3check),
  STALIN_NMETHOD("checkGetProof","(Llocal/stalin/logic/Theory;)I",
		 z3checkgetproof),
  STALIN_NMETHOD("checkGetSkolemsInsts","(Llocal/stalin/logic/Theory;"
		 "Ljava/util/Set;Ljava/util/Set;)I",z3checkgetskolemsinsts),
  STALIN_NMETHOD("cancelCheck","()V",z3cancelcheck)
};

// All JNI convention functions go here...
/**
 * Class used to initialize all IDs needed by class 
 * local.stalin.nativez3.Z3Config.
 */
STALIN_EXPORT void STALIN_CALL 
Java_local_stalin_nativez3_Z3Context_initIDs(JNIEnv* env,jclass cls) {
  if( (idcache.contextstore = env->GetFieldID(cls,"nativestore","J")) == 0 )
    return;
  if( (idcache.contextfailure = env->GetFieldID(cls,"mlastfailure","I")) == 0 )
    return;
  if( (idcache.contextproof = env->GetFieldID(cls,"mproof",
	"Llocal/stalin/nativez3/Z3ProofRule;")) == 0 )
    return;
  // Also initialize fields for class local.stalin.nativez3.Z3ProofRule
  jclass prcls = env->FindClass("local/stalin/nativez3/Z3ProofRule");
  if( !prcls )
    return;
  if( (idcache.proofconstruct = env->GetMethodID(prcls,"<init>","(II)V")) == 0 )
    return;
  if( (idcache.proofaddrule = env->GetMethodID(prcls,"addProofRule",
	"(Llocal/stalin/nativez3/Z3ProofRule;I)V")) == 0 )
    return;
  if( (idcache.proofresult = env->GetFieldID(prcls,"mres",
	"Llocal/stalin/logic/Formula;")) == 0 )
    return;
  // No need to check for errors. We return nevertheless...
  env->RegisterNatives(cls,contextmethods,STALIN_NMETHODS(contextmethods));
}

