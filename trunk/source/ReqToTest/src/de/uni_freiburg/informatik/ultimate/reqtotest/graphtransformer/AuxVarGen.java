package de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.Req2TestReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;

public class AuxVarGen {

	public final static String DEFINE_PREFIX = "d_";
	public final static String USE_PREFIX = "u_";
	public final static String CLOCK_PREFIX = "t_";

	private final Sort mSortBool;
	private final Sort mSortInt;
	private final Term mSmtTrue;
	private final Term mSmtFalse;

	private final Req2TestReqSymbolTable mReqSymbolTable;
	private final ILogger mLogger;
	private final Script mScript;

	private final Map<TermVariable, Term> mVariableToUseTerm;
	private final Map<TermVariable, Set<Term>> mVariableToDefineTerm;
	private final Map<ReqGuardGraph, Integer> mReqToId;
	private int mReqId = 0;
	private final HashMap<ReqGuardGraph, Term> mEffects;

	private final Map<ReqGuardGraph, Term> mReqToDefineAnnotation;
	private final Map<ReqGuardGraph, Term> mReqToNonDefineAnnotation;

	public AuxVarGen(final ILogger logger, final Script script, final Req2TestReqSymbolTable reqSymbolTable) {
		mReqSymbolTable = reqSymbolTable;
		mLogger = logger;
		mScript = script;
		mEffects = new HashMap<>();
		mVariableToUseTerm = new LinkedHashMap<>();
		mVariableToDefineTerm = new LinkedHashMap<>();
		mReqToDefineAnnotation = new LinkedHashMap<>();
		mReqToNonDefineAnnotation = new LinkedHashMap<>();
		mReqToId = new LinkedHashMap<>();
		mSortInt = mScript.sort("Int");
		mSortBool = mScript.sort("Bool");
		mSmtTrue = mScript.term("true");
		mSmtFalse = mScript.term("false");
	}

	public void setEffectLabel(final ReqGuardGraph req, final Term effectEdge) {
		TermVariable[] idents = {};
		// if there is a disjunct in the effect, disregard the effect.
		// TODO: disregard intervals or encode intervals as individual partially ordered effects
		if (SmtUtils.getDisjuncts(effectEdge).length <= 1) {
			mEffects.put(req, effectEdge);
			idents = effectEdge.getFreeVars();
		} else {
			mLogger.error("Nondeterministic requirement: " + req.getName());
		}
		final List<TermVariable> effectVars = getNonInputNonConstantVars(idents);
		final int reqId = getReqToId(req);
		final Term effectGuard = SmtUtils.and(mScript, varsToDefineAnnotations(effectVars, reqId));
		mReqToDefineAnnotation.put(req, effectGuard);
		final Term notEffectGuard = SmtUtils.or(mScript, varsToDefineAnnotations(effectVars, reqId));
		mReqToNonDefineAnnotation.put(req, SmtUtils.not(mScript, notEffectGuard));
	}

	public Collection<TermVariable> getEffectVariables(final ReqGuardGraph reqId) {
		final List<Term> temp = new ArrayList<>();
		if (mEffects.containsKey(reqId)) {
			temp.add(mEffects.get(reqId));
		}
		return SmtUtils.getFreeVars(temp);
	}

	private List<TermVariable> getNonInputNonConstantVars(final TermVariable[] vars) {
		final List<TermVariable> nonInputNonConstVars = new ArrayList<>();
		for (final TermVariable var : vars) {
			final String varname = var.toString();
			if (!mReqSymbolTable.isConstVar(varname) && !mReqSymbolTable.isInput(varname)) {
				nonInputNonConstVars.add(var);
			}

		}
		return nonInputNonConstVars;
	}

	public Term getDefineGuard(final ReqGuardGraph req) {
		return mReqToDefineAnnotation.get(req);
	}

	public Term getNonDefineGuard(final ReqGuardGraph req) {
		return mReqToNonDefineAnnotation.get(req);
	}

	public Term getUseGuard(final Term label) {
		final TermVariable[] idents = label.getFreeVars();
		final List<TermVariable> effectVars = getNonInputNonConstantVars(idents);
		return SmtUtils.and(mScript, varsToUseAnnotations(effectVars));
	}

	public List<Term> varsToUseAnnotations(final List<TermVariable> vars) {
		final List<Term> effectVars = new ArrayList<>();
		for (final TermVariable var : vars) {
			effectVars.add(createUseAnnotation(var));
		}
		return effectVars;
	}

	public Term createUseAnnotation(final TermVariable ident) {
		if (mVariableToUseTerm.containsKey(ident)) {
			return mVariableToUseTerm.get(ident);
		} else {
			final Term annotation = createUseTerm(ident);
			mVariableToUseTerm.put(ident, annotation);
			return annotation;
		}
	}

	public TermVariable generateClockIdent(final ReqGuardGraph req) {
		final String auxIdent = AuxVarGen.CLOCK_PREFIX + Integer.toString(getReqToId(req));
		mReqSymbolTable.addClockVar(auxIdent, BoogieType.TYPE_REAL);
		return mScript.variable(auxIdent, mSortInt);
	}

	private Term createUseTerm(final TermVariable ident) {
		final String auxIdent = AuxVarGen.USE_PREFIX + ident.toString();
		mReqSymbolTable.addAuxVar(auxIdent, BoogieType.TYPE_BOOL);
		return mScript.variable(auxIdent, mSortBool);
	}

	public List<Term> varsToDefineAnnotations(final List<TermVariable> vars, final int reqId) {
		final List<Term> effectVars = new ArrayList<>();
		for (final TermVariable var : vars) {
			effectVars.add(createDefineAnnotation(var, reqId));
			// TODO: to guarantee that there is always a use guard for which we can test.
			getUseGuard(var);
		}
		return effectVars;
	}

	public Term createDefineAnnotation(final TermVariable ident, final int reqId) {
		final Term annotation = createDefineTerm(ident, reqId);
		if (!mVariableToDefineTerm.containsKey(ident)) {
			mVariableToDefineTerm.put(ident, new HashSet<>());
		}
		mVariableToDefineTerm.get(ident).add(annotation);
		return annotation;
	}

	private Term createDefineTerm(final TermVariable ident, final int reqId) {
		final String auxIdent = AuxVarGen.DEFINE_PREFIX + Integer.toString(reqId) + "_" + ident.toString();
		mReqSymbolTable.addAuxVar(auxIdent, BoogieType.TYPE_BOOL);
		return mScript.variable(auxIdent, mSortBool);
	}

	public int getReqToId(final ReqGuardGraph req) {
		if (!mReqToId.containsKey(req)) {
			mReqToId.put(req, mReqId);
			mReqId++;
		}
		return mReqToId.get(req);
	}

	public List<Term> getDefineAssumeGuards() {
		final List<Term> guards = new ArrayList<>();
		for (final TermVariable var : mVariableToUseTerm.keySet()) {
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

	/*
	 * For each requirement, build a negated Term which combines the effect of the requirement and the define guard of
	 * the requirement, so that the assertion can only be violated if the effect is set, and it is set by the
	 * requirement itself.
	 */
	public Map<ReqGuardGraph, Term> getOracleAssertions() {
		final Map<ReqGuardGraph, Term> guards = new HashMap<>();
		for (final ReqGuardGraph reqId : mEffects.keySet()) {
			final Term guard = getOracleAssertion(reqId);
			if (guard != null && guard != mSmtTrue && guard != mSmtFalse) {
				guards.put(reqId, guard);
			}

		}
		return guards;
	}

	public Term getOracleAssertion(final ReqGuardGraph reqId) {
		final Term effect = mEffects.get(reqId);
		final Term guard = getOracleEffectAssertionTerm(reqId, effect);
		final Term denyOthersGuard = getOracleDenyOthers(reqId, effect);
		return SmtUtils.not(mScript, SmtUtils.and(mScript, guard, denyOthersGuard));
	}

	public Term getOracleEffectAssertionTerm(final ReqGuardGraph reqId, final Term effect) {
		Term guard = mSmtTrue;
		for (final TermVariable var : effect.getFreeVars()) {
			if (!mReqSymbolTable.isOutput(var.toString())) {
				continue;
			}
			final Set<TermVariable> effectVar = new HashSet<>();
			effectVar.add(var);
			final Term varTerm = SmtUtils.and(mScript, SmtUtils.filterFormula(effect, effectVar, mScript),
					createDefineAnnotation(var, mReqToId.get(reqId)));
			guard = SmtUtils.and(mScript, guard, varTerm);
		}
		return guard;
	}

	public Term getOracleDenyOthers(final ReqGuardGraph reqId, final Term effect) {
		Term guard = mSmtTrue;
		for (final TermVariable var : effect.getFreeVars()) {
			if (!mReqSymbolTable.isOutput(var.toString())) {
				continue;
			}
			final Term exclude = createDefineAnnotation(var, mReqToId.get(reqId));
			for (final Term defineTerm : mVariableToDefineTerm.get(var)) {
				if (defineTerm == exclude) {
					continue;
				}
				guard = SmtUtils.and(mScript, guard, SmtUtils.not(mScript, defineTerm));
			}
		}
		return guard;
	}

}
