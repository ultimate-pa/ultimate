#include "z3parserctx.hh"
#include "helper.hh"
#include "exceptions.hh"
#include "idcache.hh"
#include <algorithm>
#include <vector>
#include <cstring>
#include <cassert>
#ifndef NDEBUG
#  include <iostream>
#  include <cstdlib>
#endif

#include "newarraydebug.hh"

enum stalin_cf_con {
  cf_or,
  cf_and,
  cf_implies,
  cf_iff,
  cf_xor
};

z3parserctx::z3parserctx(JNIEnv* env,Z3_context ctx)
  : mctx(ctx),mboolsort(Z3_mk_bool_sort(ctx)),mnumbound(0),gqf(0),gcf(0),
    gatom(0),gtrueatom(0),gda(0),gea(0),gff(0),gitef(0),glf(0),gnf(0),
    gpa(0),gva(0),gat(0),gitet(0),gnt(0),grt(0),gvt(0) {
  jclass func = safegetclass(env,"local/stalin/logic/FunctionSymbol");
  funcparamsort = safegetfieldid(env,func,"paramSort",
				 "[Llocal/stalin/logic/Sort;");
  funcreturnsort = safegetfieldid(env,func,"returnSort",
				  "Llocal/stalin/logic/Sort;");
  funcname = safegetfieldid(env,func,"name","Ljava/lang/String;");
  funcintern = safegetfieldid(env,func,"isIntern","Z");
  env->DeleteLocalRef(func);
  jclass pred = safegetclass(env,"local/stalin/logic/PredicateSymbol");
  predparamsort = safegetfieldid(env,pred,"paramSort",
				 "[Llocal/stalin/logic/Sort;");
  predname = safegetfieldid(env,pred,"name","Ljava/lang/String;");
  predintern = safegetfieldid(env,pred,"isIntern","Z");
  env->DeleteLocalRef(pred);
  jclass jsort = safegetclass(env,"local/stalin/logic/Sort");
  sortname = safegetfieldid(env,jsort,"name","Ljava/lang/String;");
  sortintern = safegetfieldid(env,jsort,"isIntern","Z");
  env->DeleteLocalRef(jsort);
  // Initialize formulae
  jclass qf = safegetclass(env,"local/stalin/logic/QuantifiedFormula");
  gqf = static_cast<jclass>(env->NewGlobalRef(qf));
  if (!gqf)
      throw pendingjavaexc();
  jfieldID existsconstf = env->GetStaticFieldID(qf,"EXISTS","I");
  if( !existsconstf )
    throw pendingjavaexc();
  qfexistsconst = env->GetStaticIntField(qf,existsconstf);
  jfieldID forallconstf = env->GetStaticFieldID(qf,"FORALL","I");
  if( !forallconstf )
    throw pendingjavaexc();
  qfforallconst = env->GetStaticIntField(qf,forallconstf);
  qfquantifier = safegetfieldid(env,qf,"quantifier","I");
  qfvars = safegetfieldid(env,qf,"variables",
			  "[Llocal/stalin/logic/TermVariable;");
  qfsubformula = safegetfieldid(env,qf,"subformula",
				"Llocal/stalin/logic/Formula;");
  qftrigger = safegetfieldid(env,qf,"triggers",
			     "[[Llocal/stalin/logic/SMTLibBase;");
  env->DeleteLocalRef(qf);
  jclass cf = safegetclass(env,"local/stalin/logic/ConnectedFormula");
  gcf = static_cast<jclass>(env->NewGlobalRef(cf));
  if (!gcf)
      throw pendingjavaexc();
  cflhs = safegetfieldid(env,cf,"lhs","Llocal/stalin/logic/Formula;");
  cfrhs = safegetfieldid(env,cf,"rhs","Llocal/stalin/logic/Formula;");
  cfcon = safegetfieldid(env,cf,"connector","I");
  env->DeleteLocalRef(cf);
  jclass atom = safegetclass(env,"local/stalin/logic/Atom");
  gatom = static_cast<jclass>(env->NewGlobalRef(atom));
  if (!gatom)
      throw pendingjavaexc();
  env->DeleteLocalRef(atom);
  jfieldID tatomf = env->GetStaticFieldID(gatom,"TRUE",
					  "Llocal/stalin/logic/Atom;");
  if( !tatomf )
    throw pendingjavaexc();
  jobject tatom = env->GetStaticObjectField(gatom,tatomf);
  gtrueatom = env->NewGlobalRef(tatom);
  if (!gtrueatom)
      throw pendingjavaexc();
  env->DeleteLocalRef(tatom);
  jclass da = safegetclass(env,"local/stalin/logic/DistinctAtom");
  gda = static_cast<jclass>(env->NewGlobalRef(da));
  if (!gda)
      throw pendingjavaexc();
  daterms = safegetfieldid(env,da,"terms","[Llocal/stalin/logic/Term;");
  env->DeleteLocalRef(da);
  jclass ea = safegetclass(env,"local/stalin/logic/EqualsAtom");
  gea = static_cast<jclass>(env->NewGlobalRef(ea));
  if (!gea)
      throw pendingjavaexc();
  eaterms = safegetfieldid(env,ea,"terms","[Llocal/stalin/logic/Term;");
  env->DeleteLocalRef(ea);
  jclass ff = safegetclass(env,"local/stalin/logic/FletFormula");
  gff = static_cast<jclass>(env->NewGlobalRef(ff));
  if (!gff)
      throw pendingjavaexc();
  ffvar = safegetfieldid(env,ff,"variable",
			 "Llocal/stalin/logic/FormulaVariable;");
  ffval = safegetfieldid(env,ff,"value","Llocal/stalin/logic/Formula;");
  ffsub = safegetfieldid(env,ff,"subformula","Llocal/stalin/logic/Formula;");
  env->DeleteLocalRef(ff);
  jclass itef = safegetclass(env,"local/stalin/logic/ITEFormula");
  gitef = static_cast<jclass>(env->NewGlobalRef(itef));
  if (!gitef)
      throw pendingjavaexc();
  itefcond = safegetfieldid(env,itef,"condition",
			    "Llocal/stalin/logic/Formula;");
  iteftrue = safegetfieldid(env,itef,"trueCase",
			    "Llocal/stalin/logic/Formula;");
  iteffalse = safegetfieldid(env,itef,"falseCase",
			     "Llocal/stalin/logic/Formula;");
  env->DeleteLocalRef(itef);
  jclass lf = safegetclass(env,"local/stalin/logic/LetFormula");
  glf = static_cast<jclass>(env->NewGlobalRef(lf));
  if (!glf)
      throw pendingjavaexc();
  lfvar = safegetfieldid(env,lf,"variable","Llocal/stalin/logic/TermVariable;");
  lfval = safegetfieldid(env,lf,"value","Llocal/stalin/logic/Term;");
  lfsub = safegetfieldid(env,lf,"subformula","Llocal/stalin/logic/Formula;");
  env->DeleteLocalRef(lf);
  jclass nf = safegetclass(env,"local/stalin/logic/NegatedFormula");
  gnf = static_cast<jclass>(env->NewGlobalRef(nf));
  if (!gnf)
      throw pendingjavaexc();
  nfsub = safegetfieldid(env,nf,"subformula","Llocal/stalin/logic/Formula;");
  env->DeleteLocalRef(nf);
  jclass pa = safegetclass(env,"local/stalin/logic/PredicateAtom");
  gpa = static_cast<jclass>(env->NewGlobalRef(pa));
  if (!gpa)
      throw pendingjavaexc();
  papred = safegetfieldid(env,pa,"predicate",
			  "Llocal/stalin/logic/PredicateSymbol;");
  paparams = safegetfieldid(env,pa,"parameters",
			    "[Llocal/stalin/logic/Term;");
  env->DeleteLocalRef(pa);
  jclass va = safegetclass(env,"local/stalin/logic/VariableAtom");
  gva = static_cast<jclass>(env->NewGlobalRef(va));
  if (!gva)
      throw pendingjavaexc();
  vavar = safegetfieldid(env,va,"var","Llocal/stalin/logic/FormulaVariable;");
  env->DeleteLocalRef(va);
  // Initialize terms
  jclass tv = safegetclass(env,"local/stalin/logic/TermVariable");
  tvname = safegetfieldid(env,tv,"name","Ljava/lang/String;");
  tvsort = safegetfieldid(env,tv,"sort","Llocal/stalin/logic/Sort;");
  env->DeleteLocalRef(tv);
  jclass at = safegetclass(env,"local/stalin/logic/ApplicationTerm");
  gat = static_cast<jclass>(env->NewGlobalRef(at));
  if (!gat)
      throw pendingjavaexc();
  atfunc = safegetfieldid(env,at,"function",
			  "Llocal/stalin/logic/FunctionSymbol;");
  atparams = safegetfieldid(env,at,"parameters",
			    "[Llocal/stalin/logic/Term;");
  env->DeleteLocalRef(at);
  jclass itet = safegetclass(env,"local/stalin/logic/ITETerm");
  gitet = static_cast<jclass>(env->NewGlobalRef(itet));
  if (!gitet)
      throw pendingjavaexc();
  itetcond = safegetfieldid(env,itet,"condition",
			    "Llocal/stalin/logic/Formula;");
  itettrue = safegetfieldid(env,itet,"trueCase","Llocal/stalin/logic/Term;");
  itetfalse = safegetfieldid(env,itet,"falseCase","Llocal/stalin/logic/Term;");
  env->DeleteLocalRef(itet);
  jclass nt = safegetclass(env,"local/stalin/logic/NumeralTerm");
  gnt = static_cast<jclass>(env->NewGlobalRef(nt));
  if (!gnt)
      throw pendingjavaexc();
  ntpv = safegetmethodid(env,nt,"pureValue","()Ljava/lang/String;");
  ntsort = safegetfieldid(env,nt,"sort","Llocal/stalin/logic/Sort;");
  env->DeleteLocalRef(nt);
  jclass rt = safegetclass(env,"local/stalin/logic/RationalTerm");
  grt = static_cast<jclass>(env->NewGlobalRef(rt));
  if (!grt)
      throw pendingjavaexc();
  rtpv = safegetmethodid(env,rt,"pureValue","()Ljava/lang/String;");
  rtsort = safegetfieldid(env,rt,"sort","Llocal/stalin/logic/Sort;");
  env->DeleteLocalRef(rt);
  jclass vt = safegetclass(env,"local/stalin/logic/VariableTerm");
  gvt = static_cast<jclass>(env->NewGlobalRef(vt));
  vtvar = safegetfieldid(env,vt,"var","Llocal/stalin/logic/TermVariable;");
  env->DeleteLocalRef(vt);
}

void z3parserctx::deinitialize(JNIEnv* env) {
  // First uninitialized global reference indicates error position!!!
#define STALIN_SAFE_DELETE_GREF(X) if(X) env->DeleteGlobalRef(X); else return
  STALIN_SAFE_DELETE_GREF(gqf);
  STALIN_SAFE_DELETE_GREF(gcf);
  STALIN_SAFE_DELETE_GREF(gatom);
  STALIN_SAFE_DELETE_GREF(gtrueatom);
  STALIN_SAFE_DELETE_GREF(gda);
  STALIN_SAFE_DELETE_GREF(gea);
  STALIN_SAFE_DELETE_GREF(gff);
  STALIN_SAFE_DELETE_GREF(gitef);
  STALIN_SAFE_DELETE_GREF(glf);
  STALIN_SAFE_DELETE_GREF(gnf);
  STALIN_SAFE_DELETE_GREF(gpa);
  STALIN_SAFE_DELETE_GREF(gva);
  STALIN_SAFE_DELETE_GREF(gat);
  STALIN_SAFE_DELETE_GREF(gitet);
  STALIN_SAFE_DELETE_GREF(gnt);
  STALIN_SAFE_DELETE_GREF(grt);
  STALIN_SAFE_DELETE_GREF(gvt);
#undef STALIN_SAFE_DELETE_GREF
}

Z3_ast z3parserctx::parse(JNIEnv* env,jobject obj) {
#ifndef NDEBUG
  jstring jstr =
    static_cast<jstring>(env->CallObjectMethod(obj,idcache.tostring));
  utf8stringhelper nh(env,jstr);
  std::cerr << "Converting formula " << nh << std::endl;
  nh.release();
  env->DeleteLocalRef(jstr);
#endif
  Z3_ast res = convertformula(env,obj);
#ifndef NDEBUG
  std::cerr << "Result: " << Z3_ast_to_string(mctx,res) << std::endl;
#endif
  return res;
}

// Assume func symbol is not internal!!!
Z3_func_decl z3parserctx::funcsymbol(JNIEnv* env,jobject func) const {
  jobjectArray params = 
    static_cast<jobjectArray>(env->GetObjectField(func,funcparamsort));
  jsize domsize = env->GetArrayLength(params);
  Z3_sort* dom = sorts(env,params,domsize);
  env->DeleteLocalRef(params);
  jobject jsort = env->GetObjectField(func,funcreturnsort);
  Z3_sort range = sort(env,jsort);
  env->DeleteLocalRef(jsort);
  jstring name = static_cast<jstring>(env->GetObjectField(func,funcname));
  utf8stringhelper namehelper(env,name);
#ifndef NDEBUG
//  std::cerr << "Creating function symbol " << namehelper << std::endl;
#endif
  Z3_func_decl res = Z3_mk_func_decl(mctx,Z3_mk_string_symbol(mctx,namehelper),
				     static_cast<unsigned int>(domsize),dom,
				     range);
  namehelper.release();
  env->DeleteLocalRef(name);
  //delete[] dom;
  DELETE_ARRAY(dom);
  return res;
}
    
// Assumes predicate is not intern
Z3_func_decl z3parserctx::predsymbol(JNIEnv* env,jobject pred) const {
  jobjectArray params = 
    static_cast<jobjectArray>(env->GetObjectField(pred,predparamsort));
  jsize domsize = env->GetArrayLength(params);
  Z3_sort* dom = sorts(env,params,domsize);
  env->DeleteLocalRef(params);
  jstring name = static_cast<jstring>(env->GetObjectField(pred,predname));
  utf8stringhelper namehelper(env,name);
#ifndef NDEBUG
//  std::cerr << "Creating predicate symbol " << namehelper << std::endl;
#endif
  Z3_func_decl res = Z3_mk_func_decl(mctx,Z3_mk_string_symbol(mctx,namehelper),
				     static_cast<unsigned int>(domsize),dom,
				     Z3_mk_bool_sort(mctx));
  namehelper.release();
  env->DeleteLocalRef(name);
  //delete[] dom;
  DELETE_ARRAY(dom);
  return res;
}

Z3_sort z3parserctx::sort(JNIEnv* env,jobject jsort) const {
  jboolean intern = env->GetBooleanField(jsort,sortintern);
  jstring name = static_cast<jstring>(env->GetObjectField(jsort,sortname));
  utf8stringhelper namehelper(env,name);
#ifndef NDEBUG
//  std::cerr << "Creating sort " << namehelper << std::endl;
#endif
  Z3_sort res;
  if( intern ) {
    if( std::strcmp("Int",namehelper) == 0 )
      res = Z3_mk_int_sort(mctx);
    else if( std::strcmp("Real",namehelper) == 0 )
      res = Z3_mk_real_sort(mctx);
    else {
	res = 
	    Z3_mk_uninterpreted_sort(mctx,Z3_mk_string_symbol(mctx,namehelper));
    }
  } else {
    res = Z3_mk_uninterpreted_sort(mctx,Z3_mk_string_symbol(mctx,namehelper));
  }
  namehelper.release();
  env->DeleteLocalRef(name);
  return res;
}

Z3_sort* z3parserctx::sorts(JNIEnv* env,jobjectArray dom,jsize domsize) const {
  Z3_sort* res = 0;
  try {
      //res = new Z3_sort[domsize];
      NEW_ARRAY(res,Z3_sort,domsize);
    for( jsize i = 0; i < domsize; ++i ) {
      jobject jsort = env->GetObjectArrayElement(dom,i);
      // No exception check here since I iterate over the array!!!
      res[i] = sort(env,jsort);
      env->DeleteLocalRef(jsort);
    }
    return res;
  } catch( ... ) {
    if( res )
	//delete[] res;
	DELETE_ARRAY(res);
    // Rethrow exception
    throw;
  }
}

Z3_ast z3parserctx::apply_intern(JNIEnv* env,const char* name,
				 unsigned int numargs,Z3_ast args[]) const {
  if( std::strcmp("<=",name) == 0 ) {
    assert(numargs == 2);
    return Z3_mk_le(mctx,args[0],args[1]);
  }
  if( std::strcmp(">=",name) == 0 ) {
    assert(numargs == 2);
    return Z3_mk_ge(mctx,args[0],args[1]);
  }
  if( std::strncmp("ass",name,3) == 0 ) {
      // I assume, this is an internal assumption
      Z3_func_decl res = Z3_mk_func_decl(mctx,Z3_mk_string_symbol(mctx,name),
					 0,0,Z3_mk_bool_sort(mctx));
      return Z3_mk_app(mctx,res,0,0);
  }
  switch( *name ) {
  case '<' :
    assert(numargs == 2);
    return Z3_mk_lt(mctx,args[0],args[1]);
  case '>':
    assert(numargs == 2);
    return Z3_mk_gt(mctx,args[0],args[1]);
  case '+':
    return Z3_mk_add(mctx,numargs,args);
  case '-':
    return (numargs == 1) ? Z3_mk_unary_minus(mctx,args[0]) : 
      Z3_mk_sub(mctx,numargs,args);
  case '~':
    assert(numargs == 1);
    return Z3_mk_unary_minus(mctx,args[0]);
  case '*':
    return Z3_mk_mul(mctx,numargs,args);
  case '/':
    assert(numargs == 2);
    return Z3_mk_div(mctx,args[0],args[1]);
  default:
// TODO: Our assertion predicates are internals!!!

      thrownativecodeexception(env,"Unknown Internal Predicate");
    throw pendingjavaexc();
  }
}

Z3_pattern* z3parserctx::convertpatterns(JNIEnv* env,jobjectArray patterns) 
  const {
  Z3_pattern* res = 0;
  // Count invalid patterns
  jsize diff = 0;
  jsize numpattern = env->GetArrayLength(patterns);
  try {
      //res = new Z3_pattern[numpattern];
      NEW_ARRAY(res,Z3_pattern,numpattern);
    for( jsize i = 0; i < numpattern; ++i ) {
      jobjectArray terms = 
	static_cast<jobjectArray>(env->GetObjectArrayElement(patterns,i));
      Z3_pattern cp = convertpattern(env,terms);
      if( cp )
	res[i-diff] = cp;
      else
	++diff;
      env->DeleteLocalRef(terms);
    }
    // All patterns were invalid!
    if( numpattern == diff ) {
	//delete[] res;
	DELETE_ARRAY(res);
      res = 0;
    }
    return res;
  } catch( ... ) {
    if( res )
	//delete[] res;
	DELETE_ARRAY(res);
    throw;
  }
}

// term might actually be a PredicateAtom
Z3_ast z3parserctx::convertpattern(JNIEnv* env,jobject term) const {
    if( env->IsInstanceOf(term,gpa) ) {
	// PredicateAtom
	localframehelper lh(env,3);
	jobjectArray jargs = 
	    static_cast<jobjectArray>(env->GetObjectField(term,paparams));
	jsize numargs = env->GetArrayLength(jargs);
	Z3_ast* args = 0;
	try {
	    //args = new Z3_ast[numargs];
	    NEW_ARRAY(args,Z3_ast,numargs);
	    for( jsize i = 0; i < numargs; ++i ) {
		jobject arg = env->GetObjectArrayElement(jargs,i);
		// No exception check since I iterate over the array...
		args[i] = convertterm(env,arg);
		env->DeleteLocalRef(arg);
	    }
	} catch( ... ) {
	    if( args )
		//delete[] args;
		DELETE_ARRAY(args);
	    throw;
	}
	// If we reach here, args is valid!!!
	jobject pred = env->GetObjectField(term,papred);
	if( env->GetBooleanField(pred,predintern) ) {
	    jstring pname = static_cast<jstring>(env->GetObjectField(pred,
								     predname));
	    utf8stringhelper namehelper(env,pname);
	    Z3_ast res = apply_intern(env,namehelper,numargs,args);
	    //delete[] args;
	    DELETE_ARRAY(args);
	    return res;
	} else {
	    Z3_func_decl fd = predsymbol(env,pred);
	    Z3_ast res = Z3_mk_app(mctx,fd,numargs,args);
	    //delete[] args;
	    DELETE_ARRAY(args);
	    return res;
	}
    }
    return convertterm(env,term);
}

Z3_pattern z3parserctx::convertpattern(JNIEnv* env,jobjectArray terms) const {
  jsize numterms = env->GetArrayLength(terms);
  // No pattern given!!!
  if( numterms == 0 )
    return 0;
  Z3_ast* res = 0;
  try {
      //res = new Z3_ast[numterms];
      NEW_ARRAY(res,Z3_ast,numterms);
    for( jsize i = 0; i < numterms; ++i ) {
      jobject term = env->GetObjectArrayElement(terms,i);
      // No exception check here since I iterate over the array.
      res[i] = convertpattern(env,term);
      env->DeleteLocalRef(term);
    }
    Z3_pattern pres = Z3_mk_pattern(mctx,numterms,res);
    //delete[] res;
    DELETE_ARRAY(res);
    return pres;
  } catch( ... ) {
    if( res )
	//delete[] res;
	DELETE_ARRAY(res);
    throw;
  }
}

Z3_ast z3parserctx::convertterm(JNIEnv* env,jobject term) const {
  if( env->IsInstanceOf(term,gat) ) {
    // Application Term
    localframehelper lh(env,3);
    jobjectArray jterms = 
      static_cast<jobjectArray>(env->GetObjectField(term,atparams));
    jsize numterms = env->GetArrayLength(jterms);
    Z3_ast* args = 0;
    try {
	//args = new Z3_ast[numterms];
	NEW_ARRAY(args,Z3_ast,numterms);
      for( jsize i = 0; i < numterms; ++i ) {
	jobject arg = env->GetObjectArrayElement(jterms,i);
	args[i] = convertterm(env,arg);
	env->DeleteLocalRef(arg);
      }
    } catch( ... ) {
      if( args )
	  //delete[] args;
	  DELETE_ARRAY(args);
      throw;
    }
    jobject jfs = env->GetObjectField(term,atfunc);
    if( env->GetBooleanField(jfs,funcintern) ) {
      jstring jname = static_cast<jstring>(env->GetObjectField(jfs,funcname));
      utf8stringhelper namehelper(env,jname);
      Z3_ast res = apply_intern(env,namehelper,numterms,args);
      //delete[] args;
      DELETE_ARRAY(args);
      namehelper.release();
      return res;
    }
    Z3_func_decl fd = funcsymbol(env,jfs);
    env->DeleteLocalRef(jfs);
    Z3_ast res = Z3_mk_app(mctx,fd,numterms,args);
    //delete[] args;
    DELETE_ARRAY(args);
    return res;
  } else if( env->IsInstanceOf(term,gitet) ) {
    // ITETerm
    localframehelper lh(env,1);
    jobject jcond = env->GetObjectField(term,itetcond);
    Z3_ast cond = convertformula(env,jcond);
    env->DeleteLocalRef(jcond);
    jobject jtc = env->GetObjectField(term,itettrue);
    Z3_ast tc = convertterm(env,jtc);
    env->DeleteLocalRef(jtc);
    jobject jfc = env->GetObjectField(term,itetfalse);
    Z3_ast fc = convertterm(env,jfc);
    env->DeleteLocalRef(jfc);
    return Z3_mk_ite(mctx,cond,tc,fc);
  } else if( env->IsInstanceOf(term,gnt) ) {
    // NumeralTerm
    localframehelper lh(env,1);
    jobject jsort = env->GetObjectField(term,ntsort);
    Z3_sort s = sort(env,jsort);
    env->DeleteLocalRef(jsort);
    jstring pv = static_cast<jstring>(env->CallObjectMethod(term,ntpv));
    utf8stringhelper val(env,pv);
    return Z3_mk_numeral(mctx,val,s);
  } else if( env->IsInstanceOf(term,grt) ) {
    // RationalTerm
    localframehelper lh(env,1);
    jobject jsort = env->GetObjectField(term,rtsort);
    Z3_sort s = sort(env,jsort);
    env->DeleteLocalRef(jsort);
    jstring pv = static_cast<jstring>(env->CallObjectMethod(term,rtpv));
    utf8stringhelper val(env,pv);
    return Z3_mk_numeral(mctx,val,s);
  } else if( env->IsInstanceOf(term,gvt) ) {
    // VariableTerm
    localframehelper lh(env,2);
    jobject tv = env->GetObjectField(term,vtvar);
    if( mqfmap.contains(env,tv) ) {
	unsigned int debruijnidx = mnumbound - 1 - mqfmap.get(env,tv);
	jobject jsort = env->GetObjectField(tv,tvsort);
	Z3_sort s = sort(env,jsort);
	return Z3_mk_bound(mctx,debruijnidx,s);
    }
    if( mlfmap.contains(env,tv) ) {
	return mlfmap.get(env,tv);
    }
    jstring jname =
	  static_cast<jstring>(env->GetObjectField(tv,tvname));
    utf8stringhelper namehelper(env,jname);
    thrownativecodeexception(env,namehelper);
    namehelper.release();
    env->DeleteLocalRef(jname);
    throw pendingjavaexc();
  }
#ifndef NDEBUG
  jclass cls = env->GetObjectClass(term);
  jmethodID getnameid = safegetmethodid(env,env->GetObjectClass(cls),"getName",
					"()Ljava/lang/String;");
  jstring str = static_cast<jstring>(env->CallObjectMethod(cls,getnameid));
  utf8stringhelper nh(env,str);
  std::cerr << nh << std::endl;
  nh.release();
  env->DeleteLocalRef(str);
  env->DeleteLocalRef(cls);
#endif
  thrownativecodeexception(env,
			   "Unknown Term class occurred in term conversion");
  throw pendingjavaexc();
}

Z3_ast z3parserctx::convertformula(JNIEnv* env,jobject formula) const {
  // TODO: local frame helper...
  if( env->IsInstanceOf(formula,gcf) ) {
    // ConnectedFormula
    localframehelper lfh(env,2);
    jint con = env->GetIntField(formula,cfcon);
    jobject jlhs = env->GetObjectField(formula,cflhs);
    Z3_ast lhs = convertformula(env,jlhs);
    env->DeleteLocalRef(jlhs);
    switch( con ) {
    case cf_or:
    case cf_and: {
      std::vector<Z3_ast> argsv;
      argsv.push_back(lhs);
      jobject jrhs = env->GetObjectField(formula,cfrhs);
      while( env->IsInstanceOf(jrhs,gcf) &&
	     env->GetIntField(jrhs,cfcon) == con ) {
	jobject jlhs = env->GetObjectField(jrhs,cflhs);
	argsv.push_back(convertformula(env,jlhs));
	env->DeleteLocalRef(jlhs);
	jobject tmp = env->GetObjectField(jrhs,cfrhs);
	env->DeleteLocalRef(jrhs);
	jrhs = tmp;
      }
      argsv.push_back(convertformula(env,jrhs));
      env->DeleteLocalRef(jrhs);
      Z3_ast* args;
      //= new Z3_ast[argsv.size()];
      NEW_ARRAY(args,Z3_ast,argsv.size());
      std::copy(argsv.begin(),argsv.end(),args);
      Z3_ast res = con == cf_or ? Z3_mk_or(mctx,argsv.size(),args) :
	Z3_mk_and(mctx,argsv.size(),args);
      //delete[] args;
      DELETE_ARRAY(args);
      return res;
    }
    case cf_implies: {
      jobject jrhs = env->GetObjectField(formula,cfrhs);
      Z3_ast rhs = convertformula(env,jrhs);
      return Z3_mk_implies(mctx,lhs,rhs);
    }
    case cf_iff: {
      jobject jrhs = env->GetObjectField(formula,cfrhs);
      while( env->IsInstanceOf(jrhs,gcf) &&
	     env->GetIntField(jrhs,cfcon) == cf_iff ) {
	jlhs = env->GetObjectField(jrhs,cflhs);
	Z3_ast rlhs = convertformula(env,jlhs);
	env->DeleteLocalRef(jlhs);
	lhs = Z3_mk_iff(mctx,lhs,rlhs);
	jobject tmp = env->GetObjectField(jrhs,cfrhs);
	env->DeleteLocalRef(jrhs);
	jrhs = tmp;
      }
      lhs = Z3_mk_iff(mctx,lhs,convertformula(env,jrhs));
      env->DeleteLocalRef(jrhs);
      return lhs;
    }
    case cf_xor: {
      jobject jrhs = env->GetObjectField(formula,cfrhs);
      while( env->IsInstanceOf(jrhs,gcf) &&
	     env->GetIntField(jrhs,cfcon) == cf_xor ) {
	jlhs = env->GetObjectField(jrhs,cflhs);
	Z3_ast rlhs = convertformula(env,jlhs);
	env->DeleteLocalRef(jlhs);
	lhs = Z3_mk_xor(mctx,lhs,rlhs);
	jobject tmp = env->GetObjectField(jrhs,cfrhs);
	env->DeleteLocalRef(jrhs);
	jrhs = tmp;
      }
      lhs = Z3_mk_xor(mctx,lhs,convertformula(env,jrhs));
      env->DeleteLocalRef(jrhs);
      return lhs;
    }
    default:
	thrownativecodeexception(env,"Unknown logical connective");
      throw pendingjavaexc();
    }
  } else if( env->IsInstanceOf(formula,gnf) ) {
    // NegatedFormula
    localframehelper lh(env,1);
    jobject subform = env->GetObjectField(formula,nfsub);
    return Z3_mk_not(mctx,convertformula(env,subform));
  } else if( env->IsInstanceOf(formula,gpa) ) {
    // PredicateAtom
    localframehelper lh(env,3);
    jobjectArray jargs = 
      static_cast<jobjectArray>(env->GetObjectField(formula,paparams));
    jsize numargs = env->GetArrayLength(jargs);
    Z3_ast* args = 0;
    try {
	// Is args leaked here???
	//args = new Z3_ast[numargs];
	NEW_ARRAY(args,Z3_ast,numargs);
      for( jsize i = 0; i < numargs; ++i ) {
	jobject arg = env->GetObjectArrayElement(jargs,i);
	// No exception check since I iterate over the array...
	args[i] = convertterm(env,arg);
	env->DeleteLocalRef(arg);
      }
    } catch( ... ) {
      if( args )
	  //delete[] args;
	  DELETE_ARRAY(args);
      throw;
    }
    // If we reach here, args is valid!!!
    jobject pred = env->GetObjectField(formula,papred);
    if( env->GetBooleanField(pred,predintern) ) {
      jstring pname = static_cast<jstring>(env->GetObjectField(pred,predname));
      utf8stringhelper namehelper(env,pname);
      Z3_ast res = apply_intern(env,namehelper,numargs,args);
      //delete[] args;
      DELETE_ARRAY(args);
      return res;
    } else {
      Z3_func_decl fd = predsymbol(env,pred);
      Z3_ast res = Z3_mk_app(mctx,fd,numargs,args);
      //delete[] args;
      DELETE_ARRAY(args);
      return res;
    }
  } else if( env->IsInstanceOf(formula,gqf) ) {
    // QuantifiedFormula
    localframehelper lh(env,3);
    jint quant = env->GetIntField(formula,qfquantifier);
    // TODO: Need to create de-Bruijn index for variables...
    jobjectArray vars =
      static_cast<jobjectArray>(env->GetObjectField(formula,qfvars));
    jsize numvars = env->GetArrayLength(vars);
    // TODO: perhaps a two-way parse to separate memory allocation from 
    // transformation
    Z3_sort* sorts = 0;
    Z3_symbol* symbs = 0;
    javahashmap<unsigned int>::iterator* iterators;
    try {
	//sorts = new Z3_sort[numvars];
	NEW_ARRAY(sorts,Z3_sort,numvars);
	//symbs = new Z3_symbol[numvars];
	NEW_ARRAY(symbs,Z3_symbol,numvars);
	//iterators = new javahashmap<unsigned int>::iterator[numvars];
	NEW_ARRAY(iterators,javahashmap<unsigned int>::iterator,numvars);
      for( jsize i = 0; i < numvars; ++i ) {
	jobject var = env->GetObjectArrayElement(vars,i);
	jobject jsort = env->GetObjectField(var,tvsort);
	sorts[i] = sort(env,jsort);
	env->DeleteLocalRef(jsort);
	jstring jname =
	  static_cast<jstring>(env->GetObjectField(var,tvname));
	utf8stringhelper namehelper(env,jname);
	symbs[i] = Z3_mk_string_symbol(mctx,namehelper);
	namehelper.release();
	env->DeleteLocalRef(jname);
	iterators[i] = mqfmap.insert(env,var,mnumbound++);
	env->DeleteLocalRef(var);
      }
    } catch( ... ) {
      if( sorts )
	  //delete[] sorts;
	  DELETE_ARRAY(sorts);
      if( symbs )
	  //delete[] symbs;
	  DELETE_ARRAY(symbs);
      throw;
    }
    env->DeleteLocalRef(vars);
    jobject jsub = env->GetObjectField(formula,qfsubformula);
    Z3_ast body = convertformula(env,jsub);
    env->DeleteLocalRef(jsub);
    jobjectArray triggers =
      static_cast<jobjectArray>(env->GetObjectField(formula,qftrigger));
    jsize numtriggers = env->GetArrayLength(triggers);
    Z3_pattern* patterns = 0;
    try {
      patterns = convertpatterns(env,triggers);
    } catch( ... ) {
	//delete[] iterators;
	DELETE_ARRAY(iterators);
	//delete[] sorts;
	DELETE_ARRAY(sorts);
	//delete[] symbs;
	DELETE_ARRAY(symbs);
	throw;
    }
    env->DeleteLocalRef(triggers);
    for( jsize i = 0; i < numvars; ++i )
      mqfmap.remove(env,iterators[i]);
    //delete[] iterators;
    DELETE_ARRAY(iterators);
    mnumbound -= numvars;
    Z3_ast res = Z3_mk_quantifier(mctx,quant == qfforallconst,0,numtriggers,
				  patterns,numvars,sorts,symbs,body);
    //delete[] sorts;
    DELETE_ARRAY(sorts);
    //delete[] symbs;
    DELETE_ARRAY(symbs);
    //delete[] patterns;
    DELETE_ARRAY(patterns);
    return res;
  } else if( env->IsInstanceOf(formula,gitef) ) {
    // ITEFormula
    localframehelper lh(env,1);
    jobject jcond = env->GetObjectField(formula,itefcond);
    Z3_ast cond = convertformula(env,jcond);
    env->DeleteLocalRef(jcond);
    jobject jtc = env->GetObjectField(formula,iteftrue);
    Z3_ast tc = convertformula(env,jtc);
    env->DeleteLocalRef(jtc);
    jobject jfc = env->GetObjectField(formula,iteffalse);
    Z3_ast fc = convertformula(env,jfc);
    return Z3_mk_ite(mctx,cond,tc,fc);
  } else if( env->IsInstanceOf(formula,gff) ) {
    // FletFormula
    localframehelper lh(env,2);
    jobject jval = env->GetObjectField(formula,ffval);
    Z3_ast val = convertformula(env,jval);
    env->DeleteLocalRef(jval);
    jobject jvar = env->GetObjectField(formula,ffvar);
    javahashmap<Z3_ast>::iterator it = mlfmap.insert(env,jvar,val);
    env->DeleteLocalRef(jvar);
    jobject jform = env->GetObjectField(formula,ffsub);
    Z3_ast res;
    try {
      res = convertformula(env,jform);
    } catch( ... ) {
      mlfmap.remove(env,it);
      throw;
    }
    env->DeleteLocalRef(jform);
    mlfmap.remove(env,it);
    return res;
  } else if( env->IsInstanceOf(formula,glf) ) {
    // LetFormula
    localframehelper lh(env,2);
    jobject jval = env->GetObjectField(formula,lfval);
    Z3_ast val = convertterm(env,jval);
    env->DeleteLocalRef(jval);
    jobject jvar = env->GetObjectField(formula,lfvar);
    javahashmap<Z3_ast>::iterator it = mlfmap.insert(env,jvar,val);
    env->DeleteLocalRef(jvar);
    jobject jform = env->GetObjectField(formula,lfsub);
    Z3_ast res;
    try {
      res = convertformula(env,jform);
    } catch( ... ) {
      mlfmap.remove(env,it);
      throw;
    }
    env->DeleteLocalRef(jform);
    mlfmap.remove(env,it);
    return res;
  } else if( env->IsInstanceOf(formula,gea) ) {
    // EqualityAtom
    localframehelper lh(env,3);
    jobjectArray jterms =
      static_cast<jobjectArray>(env->GetObjectField(formula,eaterms));
    jsize numterms = env->GetArrayLength(jterms);
    if( numterms == 0 ) {
	thrownativecodeexception(env,"0 Terms are equal?");
      throw pendingjavaexc();
    }
    jsize end = numterms - 1;
    Z3_ast* conj = 0;
    try {
	//conj = new Z3_ast[end];
	NEW_ARRAY(conj,Z3_ast,end);
      for( jsize i = 0; i < end; ++i ) {
	jobject e1 = env->GetObjectArrayElement(jterms,i);
	jobject e2 = env->GetObjectArrayElement(jterms,i+1);
	conj[i] = Z3_mk_eq(mctx,convertterm(env,e1),convertterm(env,e2));
	env->DeleteLocalRef(e1);
	env->DeleteLocalRef(e2);
      }
    } catch( ... ) {
      if( conj )
	  //delete[] conj;
	  DELETE_ARRAY(conj);
      throw;
    }
    env->DeleteLocalRef(jterms);
    Z3_ast res;
    // Z3 does not optimize one elementary ands directly...
    if( end == 1 )
	res = conj[0];
    else
	res = Z3_mk_and(mctx,end,conj);
    //delete[] conj;
    DELETE_ARRAY(conj);
    return res;
  } else if( env->IsInstanceOf(formula,gda) ) {
    // DistinctAtom
    localframehelper lh(env,2);
    jobjectArray jterms =
      static_cast<jobjectArray>(env->GetObjectField(formula,daterms));
    jsize numterms = env->GetArrayLength(jterms);
    if( numterms == 0 ) {
	thrownativecodeexception(env,"0 Terms are distinct");
      throw pendingjavaexc();
    }
    Z3_ast* args = 0;
    try {
	//args = new Z3_ast[numterms];
	NEW_ARRAY(args,Z3_ast,numterms);
      for( jsize i = 0; i < numterms; ++i ) {
	jobject jt = env->GetObjectArrayElement(jterms,i);
	args[i] = convertterm(env,jt);
	env->DeleteLocalRef(jt);
      }
    } catch( ... ) {
      if( args )
	  //delete[] args;
	  DELETE_ARRAY(args);
      throw;
    }
    env->DeleteLocalRef(jterms);
    Z3_ast res = Z3_mk_distinct(mctx,numterms,args);
    //delete[] args;
    DELETE_ARRAY(args);
    return res;
  } else if( env->IsInstanceOf(formula,gva) ) {
    // VariableAtom
    localframehelper lh(env,1);
    jobject var = env->GetObjectField(formula,vavar);
    return mlfmap.get(env,var);
  } else if( env->IsInstanceOf(formula,gatom) ) {
    // Atom
    return env->IsSameObject(formula,gtrueatom) ? Z3_mk_true(mctx) : 
      Z3_mk_false(mctx);
  }
  thrownativecodeexception(env,"Unknown Formula Class in convertformula");
  throw pendingjavaexc();
}
