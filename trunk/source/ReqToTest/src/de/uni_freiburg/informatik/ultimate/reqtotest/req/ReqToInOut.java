package de.uni_freiburg.informatik.ultimate.reqtotest.req;

import java.util.LinkedHashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlobally;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndInvariancePattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternTT;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternTU;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternUT;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InstAbsPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InvariantPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.UniversalityPattern;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;

public class ReqToInOut {

	private final ILogger mLogger;
	private final Req2TestReqSymbolTable mReqSymbolTable;

	private final CddToSmt mCddToSmt;

	private final LinkedHashSet<TermVariable> mInputs;
	private final LinkedHashSet<TermVariable> mHidden;
	private final LinkedHashSet<TermVariable> mOutputs;

	private static final boolean UNIVERSALITY_IS_DEFINITNG = false;

	public ReqToInOut(final ILogger logger, final Req2TestReqSymbolTable reqSymbolExpressionTable,
			final CddToSmt cddToSmt) {
		mLogger = logger;
		mReqSymbolTable = reqSymbolExpressionTable;
		mCddToSmt = cddToSmt;

		mInputs = new LinkedHashSet<>();
		mHidden = new LinkedHashSet<>();
		mOutputs = new LinkedHashSet<>();
	}

	public void requirementToInOut(final List<PatternType<?>> patternList) {
		for (final PatternType<?> pattern : patternList) {
			if (!(pattern instanceof InitializationPattern)) {
				addRequirement(pattern);
			}
		}
		mLogger.warn("Guessing In/Out/Hidden, please verify the Resluts.");
		mLogger.warn("Inputs:");
		mLogger.warn(mInputs.toString());
		mLogger.warn("Hidden:");
		mLogger.warn(mHidden.toString());
		mLogger.warn("Output:");
		mLogger.warn(mOutputs.toString());
		for (final TermVariable var : mInputs) {
			mReqSymbolTable.updateVariableCategoryInput(var.toString());
		}
		for (final TermVariable var : mHidden) {
			mReqSymbolTable.updateVariableCategoryHidden(var.toString());
		}
		for (final TermVariable var : mOutputs) {
			mReqSymbolTable.updateVariableCategoryOutput(var.toString());
		}
	}

	/*
	 * Global After Until After Until BndInvariancePattern X BndResponsePatternTT X BndResponsePatternUT X
	 * BndResponsePatternTU X InvariantPattern X InstAbsPattern X UniversalityPattern X TogglePatternDelayed X
	 */

	public void addRequirement(final PatternType<?> pattern) {
		if (pattern instanceof InvariantPattern) {
			addInvariantPattern(pattern);
		} else if (pattern instanceof BndResponsePatternUT) {
			addBndResponsePatternUTPattern(pattern);
		} else if (pattern instanceof BndInvariancePattern) {
			addBndInvariance(pattern);
		} else if (pattern instanceof BndResponsePatternTT) {
			addBndResponsePatternTTPattern(pattern);
		} else if (pattern instanceof UniversalityPattern) {
			addUniversalityPattern(pattern);
		} else if (pattern instanceof InstAbsPattern) {
			addInstAbsPattern(pattern);
		} else if (pattern instanceof BndResponsePatternTU) {
			addBndResponsePatternTUPattern(pattern);
		} else {
			throw new RuntimeException("Pattern type is not supported at:" + pattern.toString());
		}
	}

	private void addTriggerSet(final TermVariable[] vars) {
		for (final TermVariable var : vars) {
			addTriggerVariable(var);
		}
	}

	private void addTriggerVariable(final TermVariable var) {
		if (mReqSymbolTable.isConstVar(var.toString())) {
			return;
		}
		if (mHidden.contains(var)) {
			// do nothing
		} else if (mOutputs.contains(var)) {
			mOutputs.remove(var);
			mHidden.add(var);
		} else {
			mInputs.add(var);
		}
	}

	private void addEffectSet(final TermVariable[] vars) {
		for (final TermVariable var : vars) {
			addEffectVariable(var);
		}
	}

	private void addEffectVariable(final TermVariable var) {
		if (mReqSymbolTable.isConstVar(var.toString())) {
			return;
		}
		if (mHidden.contains(var)) {
			// do nothing
		} else if (mInputs.contains(var)) {
			mInputs.remove(var);
			mHidden.add(var);
		} else {
			mOutputs.add(var);
		}
	}

	/*
	 * "{scope}, it is always the case that if "R" holds for at least "c1" time units, then "S" holds afterwards for at
	 * least "c2" time units
	 */
	private void addBndResponsePatternTTPattern(final PatternType<?> pattern) {
		if (pattern.getScope() instanceof SrParseScopeGlobally) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			addTriggerSet(R.getFreeVars());
			addEffectSet(S.getFreeVars());
		} else {
			scopeNotImplementedWarning(pattern);
		}
	}

	/*
	 * {scope}, it is always the case that if "R" holds for at least "c1" time units, then "S" holds afterwards.
	 */
	private void addBndResponsePatternTUPattern(final PatternType<?> pattern) {
		if (pattern.getScope() instanceof SrParseScopeGlobally) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			addTriggerSet(R.getFreeVars());
			addEffectSet(S.getFreeVars());
		} else {
			scopeNotImplementedWarning(pattern);
		}
	}

	/*
	 * * {scope}, it is always the case that if "R" holds, then "S" holds for at least "c1" time units.
	 */
	private void addBndInvariance(final PatternType<?> pattern) {
		if (pattern.getScope() instanceof SrParseScopeGlobally) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			addTriggerSet(R.getFreeVars());
			addEffectSet(S.getFreeVars());

		} else {
			scopeNotImplementedWarning(pattern);
		}
	}

	/*
	 * {scope}, it is always the case that if "R" holds, then "S" holds after at most "c1" time units.
	 *
	 * Assuming stability of output ( R, R & S, R & !S, R & S,.....) not intended behavior
	 */
	private void addBndResponsePatternUTPattern(final PatternType<?> pattern) {
		if (pattern.getScope() instanceof SrParseScopeGlobally) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			addTriggerSet(R.getFreeVars());
			addEffectSet(S.getFreeVars());
		} else if (pattern.getScope() instanceof SrParseScopeAfter) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			final Term Q = mCddToSmt.toSmt(pattern.getScope().getCdd1());
			addTriggerSet(Q.getFreeVars());
			addTriggerSet(R.getFreeVars());
			addEffectSet(S.getFreeVars());
		} else {
			scopeNotImplementedWarning(pattern);
		}
	}

	/*
	 * * {scope}, it is always the case that if "R" holds, then "S" holds as well.
	 */
	private void addInvariantPattern(final PatternType<?> pattern) {
		if (UNIVERSALITY_IS_DEFINITNG) {
			return;
		}
		if (pattern.getScope() instanceof SrParseScopeGlobally) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			addTriggerSet(R.getFreeVars());
			addEffectSet(S.getFreeVars());
		} else if (pattern.getScope() instanceof SrParseScopeAfter) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			final Term Q = mCddToSmt.toSmt(pattern.getScope().getCdd1());
			addTriggerSet(R.getFreeVars());
			addEffectSet(S.getFreeVars());
			addTriggerSet(Q.getFreeVars());
		} else {
			scopeNotImplementedWarning(pattern);
		}
	}

	/*
	 * * {scope}, it is always the case that if "S" holds.
	 */
	private void addUniversalityPattern(final PatternType<?> pattern) {
		if (pattern.getScope() instanceof SrParseScopeGlobally) {
			final List<CDD> args = pattern.getCdds();
			final Term S = mCddToSmt.toSmt(args.get(0));
			addEffectSet(S.getFreeVars());
		} else {
			scopeNotImplementedWarning(pattern);
		}
	}

	/*
	 * * {scope}, it is never the case that if "S" holds.
	 */
	private void addInstAbsPattern(final PatternType<?> pattern) {
		if (pattern.getScope() instanceof SrParseScopeGlobally) {
			final List<CDD> args = pattern.getCdds();
			final Term S = mCddToSmt.toSmt(args.get(0));
			addEffectSet(S.getFreeVars());
		} else {
			scopeNotImplementedWarning(pattern);
			;
		}
	}

	/*
	 * This pattern is for discrete Step LTL * {scope}, it is always the case that if "R" holds, then "S" holds in the
	 * next Step.
	 */
	private void getImmediateResponsePatternToAutomaton(final PatternType<?> pattern) {
		if (pattern.getScope() instanceof SrParseScopeGlobally) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			addTriggerSet(R.getFreeVars());
			addEffectSet(S.getFreeVars());
		} else {
			scopeNotImplementedWarning(pattern);
		}
	}

	private void addTogglePatternDelayed(final PatternType<?> pattern) {
		if (pattern.getScope() instanceof SrParseScopeGlobally) {
			final List<CDD> args = pattern.getCdds();
			final Term P = mCddToSmt.toSmt(args.get(0));
			final Term S = mCddToSmt.toSmt(args.get(1));
			final Term T = mCddToSmt.toSmt(args.get(2));
			addTriggerSet(P.getFreeVars());
			addTriggerSet(S.getFreeVars());
			addEffectSet(T.getFreeVars());
		} else {
			scopeNotImplementedWarning(pattern);
		}
	}

	private void scopeNotImplementedWarning(final PatternType<?> pattern) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Scope not implemented: ");
		sb.append(pattern.getScope().toString());
		sb.append(" [in: ");
		sb.append(pattern.getId());
		sb.append(" ]");
		mLogger.warn(sb.toString());
	}

}
