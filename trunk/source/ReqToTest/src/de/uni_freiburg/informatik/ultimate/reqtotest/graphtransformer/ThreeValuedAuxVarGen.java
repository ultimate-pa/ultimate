package de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;

public class ThreeValuedAuxVarGen {
	
	private final Sort mSortBool;
	private final Sort mSortReal;
		
	private final ReqSymbolTable mReqSymbolTable;
	private final ILogger mLogger;
	private final Script mScript;
	
	private final Map<TermVariable, Term> mVariableToUseTerm;
	private final Map<TermVariable, List<Term>> mVariableToDefineTerm;
	private final Map<ReqGuardGraph, Integer> mReqToId;
	private int mReqId = 0;
	private final Set<Term> mEffects;
	
	private final Map<ReqGuardGraph,Term> mReqToDefineAnnotation;
	private final Map<ReqGuardGraph,Term> mReqToNonDefineAnnotation;   
	
	public ThreeValuedAuxVarGen(ILogger logger, Script script, ReqSymbolTable reqSymbolTable) {
		mReqSymbolTable = reqSymbolTable;
		mLogger = logger;
		mScript = script;
		mEffects = new HashSet<>();
		mVariableToUseTerm = new LinkedHashMap<>();
		mVariableToDefineTerm = new LinkedHashMap<>();
		mReqToDefineAnnotation = new LinkedHashMap<>();
		mReqToNonDefineAnnotation = new LinkedHashMap<>();
		mReqToId = new LinkedHashMap<>();
		mSortBool = mScript.sort("Bool");
		mSortReal = mScript.sort("Real");
	}
	
	
	public void setEffectLabel(ReqGuardGraph req, Term effectTerm) {
		TermVariable[] idents = {};
		if(SmtUtils.getDisjuncts(effectTerm).length <= 1) {
			mEffects.add(effectTerm);
			idents = effectTerm.getFreeVars();
		} 
		final List<TermVariable> effectVars = getNonInputNonConstantVars(idents);
		final int reqId = getReqToId(req);
		final Term effectGuard = SmtUtils.and(mScript, varsToDefineAnnotations(effectVars, reqId));
		mReqToDefineAnnotation.put(req, effectGuard);
		final Term notEffectGuard = SmtUtils.or(mScript, varsToDefineAnnotations(effectVars, reqId));
		mReqToNonDefineAnnotation.put(req, SmtUtils.not(mScript, notEffectGuard));
	}	
	
	private List<TermVariable> getNonInputNonConstantVars(TermVariable[] vars){
		final List<TermVariable> nonInputNonConstVars = new ArrayList<>();
		for(TermVariable var: vars) {
			if (mReqSymbolTable.isNonInputNonConstVar(var.toString())) {
				nonInputNonConstVars.add(var);
			}
		}
		return nonInputNonConstVars;
	}
	
	public Term getDefineGuard(ReqGuardGraph req) {
		return mReqToDefineAnnotation.get(req);
	}
	
	public Term getNonDefineGuard(ReqGuardGraph req) {
		return mReqToNonDefineAnnotation.get(req);
	}
	
	public Term getUseGuard(Term label) {
		final TermVariable[] idents = label.getFreeVars();
		final List<TermVariable> effectVars = getNonInputNonConstantVars(idents);
		return SmtUtils.and(mScript, varsToUseAnnotations(effectVars));
	}
	
	public List<Term> varsToUseAnnotations(List<TermVariable> vars){
		final List<Term> effectVars = new ArrayList<>();
		for(TermVariable var: vars) {
			effectVars.add(createUseAnnotation(var));
		}
		return effectVars;
	}
	
	public Term createUseAnnotation(TermVariable ident) {
		if (mVariableToUseTerm.containsKey(ident)) {
			return mVariableToUseTerm.get(ident);
		} else {
			final Term annotation = createUseTerm(ident);
			mVariableToUseTerm.put(ident, annotation);
			return annotation;
		}
	}
	
	public TermVariable generateClockIdent(ReqGuardGraph req) {
		final String auxIdent = "t_" + Integer.toString(getReqToId(req));
		mReqSymbolTable.addClockVar(auxIdent,  BoogieType.TYPE_REAL);
		return mScript.variable(auxIdent,  mSortReal);
	}
	
	private Term createUseTerm(TermVariable ident) {
		final String auxIdent = "u_" + ident.toString();
		mReqSymbolTable.addAuxVar(auxIdent,  BoogieType.TYPE_BOOL);
		return mScript.variable(auxIdent,  mSortBool);
	}
	
	public List<Term> varsToDefineAnnotations(List<TermVariable> vars, int reqId){
		final List<Term> effectVars = new ArrayList<>();
		for(TermVariable var: vars) {
			effectVars.add(createDefineAnnotation(var, reqId));
			//TODO: to guarantee that there is always a use guard for which we can test.
			getUseGuard(var);
		}
		return effectVars;
	}
	
	public Term createDefineAnnotation(TermVariable ident, int reqId) {
		final Term annotation = createDefineTerm(ident, reqId);
		if (!mVariableToDefineTerm.containsKey(ident)) {
			mVariableToDefineTerm.put(ident, new ArrayList<Term>());
		}
		mVariableToDefineTerm.get(ident).add(annotation);
		return annotation;
	}
	
	private Term createDefineTerm(TermVariable ident, int reqId) {
		final String auxIdent = "d_" + Integer.toString(reqId) + "_" + ident.toString();
		mReqSymbolTable.addAuxVar(auxIdent,  BoogieType.TYPE_BOOL);
		return mScript.variable(auxIdent,  mSortBool);
	}
	
	private int getReqToId(ReqGuardGraph req) {
		if (!mReqToId.containsKey(req)) {
			mReqToId.put(req, mReqId);
			mReqId++;
		}
		return mReqToId.get(req);
	}
	
	public List<Term> getDefineAssumeGuards(){
		final List<Term> guards = new ArrayList<>();
		for(TermVariable var: mVariableToUseTerm.keySet()) {
			final Term usevar = mVariableToUseTerm.get(var);
			if (mVariableToDefineTerm.containsKey(var)) {
				final Term define = SmtUtils.or(mScript, mVariableToDefineTerm.get(var));
				guards.add(SmtUtils.binaryBooleanEquality(mScript, usevar, define));	
			} else {
				guards.add(SmtUtils.not(mScript, usevar));
			}
		}
		return guards;
	}
	
	public List<Term> getOracleGuards(){
		final List<Term> guards = new ArrayList<>();
		for(Term effect: mEffects) {
			Term use =  effect;
			for(TermVariable var: effect.getFreeVars()) {
				if (!mReqSymbolTable.isOutput(var.toString())) {
					continue;
				} 
				use = SmtUtils.and(mScript, use, getUseGuard(var));
				
			}
			if (use != effect) {
				guards.add(SmtUtils.not( mScript,use));	
			}
		}
		return guards;
	}
	
}
























