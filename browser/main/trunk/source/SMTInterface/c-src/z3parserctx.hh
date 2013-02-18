#ifndef STALIN_Z3PARSERCTX_HH_
#define STALIN_Z3PARSERCTX_HH_

#include "platformdefs.hh"
#include <jni.h>
#include "z3cc.hh"
#include "javahashmap.hh"

/**
 * Stores function and predicate symbols along with some additional objects.
 */
class STALIN_INTERNAL z3parserctx {
  Z3_context mctx;
  Z3_sort mboolsort;
  mutable unsigned int mnumbound;
  /* Let/flet map. This is a simulated Java hash map mapping TermVariables or
     FormulaVariables to Z3_asts. No changes will be seen from outside... */
  mutable javahashmap<Z3_ast> mlfmap;
  /* Map storing quantified variables to ints. The ints are the inverted de 
     Bruijn indexes. To get current index for var use 
     \code mnumbound - mqfmap.get(x) - 1\endcode */
  mutable javahashmap<unsigned int> mqfmap;
  // FunctionsSymbol
  jfieldID funcparamsort,funcreturnsort,funcname,funcintern;
  // PredicateSymbols
  jfieldID predparamsort,predname,predintern;
  // Sort
  jfieldID sortname,sortintern;
  // QuantifiedFormula
  jclass gqf;
  jint qfexistsconst;// Assumed to be const!
  jint qfforallconst;// Assumed to be const!
  jfieldID qfquantifier;
  jfieldID qfvars;
  jfieldID qfsubformula;
  jfieldID qftrigger;
  // ConnectedFormula
  jclass gcf;
  jfieldID cflhs,cfrhs,cfcon;
  // Atom
  jclass gatom;
  jobject gtrueatom;
  // DistinctAtom
  jclass gda;
  jfieldID daterms;
  // EqualsAtom
  jclass gea;
  jfieldID eaterms;
  // FletFormula
  jclass gff;
  jfieldID ffvar,ffval,ffsub;
  // ITEFormula
  jclass gitef;
  jfieldID itefcond,iteftrue,iteffalse;
  // LetFormula
  jclass glf;
  jfieldID lfvar,lfval,lfsub;
  // NegatedFormula
  jclass gnf;
  jfieldID nfsub;
  // PredicateAtom
  jclass gpa;
  jfieldID papred,paparams;
  // VariableAtom
  jclass gva;
  jfieldID vavar;
  // TermVariable
  jfieldID tvname,tvsort;
  // ApplicationTerm
  jclass gat;
  jfieldID atfunc,atparams;
  // ITETerm
  jclass gitet;
  jfieldID itetcond,itettrue,itetfalse;
  // NumeralTerm
  jclass gnt;
  jmethodID ntpv;
  jfieldID ntsort;
  // RationalTerm
  jclass grt;
  jmethodID rtpv;
  jfieldID rtsort;
  // VariableTerm
  jclass gvt;
  jfieldID vtvar;
 public:
  z3parserctx(JNIEnv* env,Z3_context ctx);
  void deinitialize(JNIEnv* env);
  Z3_ast parse(JNIEnv* env,jobject obj);
  inline Z3_context context() const { return mctx; }
 private:
  // Helper functions for the parser
  Z3_func_decl funcsymbol(JNIEnv* env,jobject func) const;
  Z3_func_decl predsymbol(JNIEnv* env,jobject pred) const;
  Z3_sort sort(JNIEnv* env,jobject jsort) const;
  Z3_sort* sorts(JNIEnv* env,jobjectArray dom,jsize domsize) const;
  Z3_ast apply_intern(JNIEnv* env,const char* name,
		      unsigned int numargs,Z3_ast args[]) const;
  Z3_pattern* convertpatterns(JNIEnv* env,jobjectArray patterns) const;
  Z3_pattern convertpattern(JNIEnv* env,jobjectArray terms) const;
  Z3_ast convertpattern(JNIEnv* env,jobject obj) const;
  Z3_ast convertterm(JNIEnv* env,jobject term) const;
  Z3_ast convertformula(JNIEnv* env,jobject formula) const;
};

#endif
