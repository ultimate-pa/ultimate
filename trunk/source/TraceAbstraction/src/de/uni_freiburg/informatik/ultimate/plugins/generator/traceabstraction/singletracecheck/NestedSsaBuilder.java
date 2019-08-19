/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.MultiElementCounter;

/**
 * A trace has single static assignment form (SSA) is each variable is assigned exactly once (
 * http://en.wikipedia.org/wiki/Static_single_assignment_form).
 *
 * This class transforms a trace to an SSA representation by renaming variables.
 *
 * Roughly variable x is renamed to x_j, where j is the position where j is the last position where x obtained a new
 * value.
 *
 * We use the SSA for checking satisfiability with an SMT solver, therefore we represent the indexed variables by
 * constants. Furthermore we replace all auxiliary variables and branch encoders in the TransFormulas by fresh
 * constants.
 *
 * We rename inVars of a variable x at trace position i+1 according to the following scheme.
 * <ul>
 * <li>if x is local: we rename the inVar to x_j, where j is the largest position <= i in the same calling context,
 * where x is assigned. If x was not assigned in this calling context up to position i, j is the start of the calling
 * context.
 * <li>if x is global and not oldvar: we rename the inVar to x_j, where j is the largest position <=i where x is
 * assigned. If x was not assigned up to position i, j is the start of the lowest calling context (which is -1 if there
 * are no pending returns and numberOfPendingReturns-1 otherwise).
 * <li>if x is global and oldvar: if x is modifiable in the current calling context we rename the inVar to x_j, where j
 * is the start of the current calling context, if x is not modifiable in the current calling context we threat this
 * variable as a non-oldVar
 * </ul>
 * If x is assigned at position i+1, we rename the outVar to x_{x+1}. If x in not assigned at position i+1, the outVar
 * does not exist or coincides with the inVar and was already renamed above.
 *
 * @author Matthias Heizmann
 *
 */
public class NestedSsaBuilder {

	private final ILogger mLogger;

	private final Script mScript;

	/**
	 * Map global BoogieVar bv to the constant bv_j that represents bv at the moment.
	 */
	private final Map<IProgramVar, Term> currentGlobalVarVersion = new HashMap<>();
	/**
	 * Map local or oldVar BoogieVar bv to the constant bv_j that represents bv at the moment.
	 */
	protected Map<IProgramVar, Term> currentLocalAndOldVarVersion;

	/**
	 * Stores current versions for local or oldVar that are not visible at the moment.
	 */
	protected final Stack<Map<IProgramVar, Term>> mCurrentVersionStack = new Stack<>();

	private Integer mStartOfCallingContext;
	private final Stack<Integer> mStartOfCallingContextStack = new Stack<>();

	private final Map<IProgramVar, TreeMap<Integer, Term>> mIndexedVarRepresentative = new HashMap<>();

	protected final Map<Term, IProgramVar> mConstants2BoogieVar = new HashMap<>();

	protected final NestedFormulas<UnmodifiableTransFormula, IPredicate> mFormulas;

	protected final ModifiableNestedFormulas<Term, Term> mSsa;
	protected final ModifiableNestedFormulas<Map<Term, Term>, Map<Term, Term>> mVariable2Constant;

	private final ModifiableGlobalsTable mModGlobVarManager;

	private final Map<String, Term> mIndexedConstants = new HashMap<>();

	protected String mCurrentProcedure;

	/**
	 * maps position of pending context to position of pending return the positions of pending contexts are -2,-3,-4,...
	 */
	protected final Map<Integer, Integer> mPendingContext2PendingReturn = new HashMap<>();

	/**
	 * True iff the NestedSsaBuilder has to use a different Script than the Script that was used to construct the Term
	 * that occur in the NestedFormulas that are the input for the SSA construction.
	 */
	private final boolean mTransferToScriptNeeded;
	private final TermTransferrer mTermTransferrer;

	/**
	 * Counter that helps us to ensure that we construct a fresh constant for each occurrence of an aux var.
	 */
	private final MultiElementCounter<TermVariable> mConstForTvCounter = new MultiElementCounter<>();

	public NestedSsaBuilder(final NestedWord<? extends IAction> trace, final ManagedScript managedScript,
			final NestedFormulas<UnmodifiableTransFormula, IPredicate> nestedTransFormulas,
			final ModifiableGlobalsTable modifiableGlobalsTable, final ILogger logger,
			final boolean transferToScriptNeeded) {
		mLogger = logger;
		mScript = managedScript.getScript();
		mFormulas = nestedTransFormulas;
		mModGlobVarManager = modifiableGlobalsTable;
		mSsa = new ModifiableNestedFormulas<>(trace, new TreeMap<Integer, Term>());
		mVariable2Constant = new ModifiableNestedFormulas<>(trace, new TreeMap<Integer, Map<Term, Term>>());
		mTransferToScriptNeeded = transferToScriptNeeded;
		if (mTransferToScriptNeeded) {
			mTermTransferrer = new TermTransferrer(mScript);
		} else {
			mTermTransferrer = null;
		}
		buildSSA();
	}

	protected void buildSSA() {
		/*
		 * Step 1: We rename the formulas in each pending context. The index starts from (-1 - numberPendingContexts)
		 * and ends at -2. Furthermore we need the oldVarAssignment and the globalVarAssignment they will link the
		 * pending context with the pending return.
		 */
		final Set<Integer> pendingReturnsRaw = mFormulas.getTrace().getPendingReturns().keySet();
		final Integer[] pendingReturns = pendingReturnsRaw.toArray(new Integer[pendingReturnsRaw.size()]);
		final int numberPendingContexts = pendingReturns.length;

		mStartOfCallingContext = -1 - numberPendingContexts;
		currentLocalAndOldVarVersion = new HashMap<>();

		for (int i = numberPendingContexts - 1; i >= 0; i--) {
			final int pendingReturnPosition = pendingReturns[i];
			mPendingContext2PendingReturn.put(mStartOfCallingContext, pendingReturnPosition);
			final IIcfgReturnTransition<?, ?> ret =
					(IIcfgReturnTransition<?, ?>) mFormulas.getTrace().getSymbol(pendingReturnPosition);
			final IIcfgCallTransition<?> correspondingCall = ret.getCorrespondingCall();
			mCurrentProcedure = correspondingCall.getPrecedingProcedure();

			reVersionModifiableGlobals();
			if (i == numberPendingContexts - 1) {
				reVersionModifiableOldVars();
			} else {
				// have already been reversioned at the last oldVarAssignment
			}

			final IPredicate pendingContext = mFormulas.getPendingContext(pendingReturnPosition);
			final VariableVersioneer pendingContextVV = new VariableVersioneer(pendingContext);
			pendingContextVV.versionPredicate();
			mSsa.setPendingContext(pendingReturnPosition, pendingContextVV.getVersioneeredTerm());
			mVariable2Constant.setPendingContext(pendingReturnPosition, pendingContextVV.getSubstitutionMapping());

			final UnmodifiableTransFormula localVarAssignment = correspondingCall.getTransformula();
			final VariableVersioneer initLocalVarsVV = new VariableVersioneer(localVarAssignment);
			initLocalVarsVV.versionInVars();

			final String calledProcedure = correspondingCall.getSucceedingProcedure();
			final UnmodifiableTransFormula oldVarAssignment = mFormulas.getOldVarAssignment(pendingReturnPosition);
			final VariableVersioneer initOldVarsVV = new VariableVersioneer(oldVarAssignment);
			initOldVarsVV.versionInVars();

			mStartOfCallingContextStack.push(mStartOfCallingContext);
			mStartOfCallingContext++;
			mCurrentProcedure = calledProcedure;
			mCurrentVersionStack.push(currentLocalAndOldVarVersion);
			currentLocalAndOldVarVersion = new HashMap<>();

			/*
			 * Parameters and oldVars of procedure form that the pending return returns get the index of the next
			 * pending context.
			 */
			initOldVarsVV.versionAssignedVars(mStartOfCallingContext);
			initLocalVarsVV.versionAssignedVars(mStartOfCallingContext);

			mSsa.setOldVarAssignmentAtPos(pendingReturnPosition, initOldVarsVV.getVersioneeredTerm());
			mVariable2Constant.setOldVarAssignmentAtPos(pendingReturnPosition, initOldVarsVV.getSubstitutionMapping());
			mSsa.setLocalVarAssignmentAtPos(pendingReturnPosition, initLocalVarsVV.getVersioneeredTerm());
			mVariable2Constant.setLocalVarAssignmentAtPos(pendingReturnPosition,
					initLocalVarsVV.getSubstitutionMapping());
		}

		assert mStartOfCallingContext == -1;

		/*
		 * Step 2: We rename the formula of the precondition. We use as index -1.
		 */
		if (mCurrentProcedure == null) {
			assert numberPendingContexts == 0;
			final IAction firstCodeBlock = mFormulas.getTrace().getSymbol(0);
			mCurrentProcedure = firstCodeBlock.getPrecedingProcedure();
		}
		reVersionModifiableGlobals();
		if (pendingReturns.length == 0) {
			reVersionModifiableOldVars();
		} else {
			// have already been reversioned at the last oldVarAssignment
		}
		final VariableVersioneer precondVV = new VariableVersioneer(mFormulas.getPrecondition());
		precondVV.versionPredicate();
		mSsa.setPrecondition(precondVV.getVersioneeredTerm());
		mVariable2Constant.setPrecondition(precondVV.getSubstitutionMapping());

		/*
		 * Step 3: We rename the TransFormulas of the traces CodeBlocks
		 */
		int numberOfPendingCalls = 0;
		for (int i = 0; i < mFormulas.getTrace().length(); i++) {
			final IAction symbol = mFormulas.getTrace().getSymbol(i);
			// if (symbol instanceof GotoEdge) {
			// throw new IllegalArgumentException(s_GotosUnsupportedMessage);
			// }

			UnmodifiableTransFormula tf;
			if (mFormulas.getTrace().isCallPosition(i)) {
				tf = mFormulas.getLocalVarAssignment(i);
			} else {
				tf = mFormulas.getFormulaFromNonCallPos(i);
			}
			assert tf != null : "CodeBlock " + symbol + " has no TransFormula";
			final VariableVersioneer tfVV = new VariableVersioneer(tf);
			tfVV.versionInVars();

			if (mFormulas.getTrace().isCallPosition(i)) {
				assert symbol instanceof IIcfgCallTransition<?> : "current implementation supports only Call";
				if (mFormulas.getTrace().isPendingCall(i)) {
					numberOfPendingCalls++;
				}
				final IIcfgCallTransition<?> call = (IIcfgCallTransition<?>) symbol;
				final String calledProcedure = call.getSucceedingProcedure();
				mCurrentProcedure = calledProcedure;
				final UnmodifiableTransFormula oldVarAssignment = mFormulas.getOldVarAssignment(i);
				final VariableVersioneer initOldVarsVV = new VariableVersioneer(oldVarAssignment);
				initOldVarsVV.versionInVars();
				mStartOfCallingContextStack.push(mStartOfCallingContext);
				mStartOfCallingContext = i;

				mCurrentVersionStack.push(currentLocalAndOldVarVersion);
				currentLocalAndOldVarVersion = new HashMap<>();

				initOldVarsVV.versionAssignedVars(i);
				mSsa.setOldVarAssignmentAtPos(i, initOldVarsVV.getVersioneeredTerm());
				mVariable2Constant.setOldVarAssignmentAtPos(i, initOldVarsVV.getSubstitutionMapping());

				final UnmodifiableTransFormula globalVarAssignment = mFormulas.getGlobalVarAssignment(i);
				final VariableVersioneer initGlobalVarsVV = new VariableVersioneer(globalVarAssignment);
				initGlobalVarsVV.versionInVars();
				initGlobalVarsVV.versionAssignedVars(i);
				mSsa.setGlobalVarAssignmentAtPos(i, initGlobalVarsVV.getVersioneeredTerm());
				mVariable2Constant.setGlobalVarAssignmentAtPos(i, initGlobalVarsVV.getSubstitutionMapping());

			}
			if (mFormulas.getTrace().isReturnPosition(i)) {
				final IIcfgReturnTransition<?, ?> ret = (IIcfgReturnTransition<?, ?>) symbol;
				mCurrentProcedure = ret.getCallerProgramPoint().getProcedure();
				currentLocalAndOldVarVersion = mCurrentVersionStack.pop();
				mStartOfCallingContext = mStartOfCallingContextStack.pop();
			}
			tfVV.versionAssignedVars(i);
			tfVV.versionBranchEncoders(i);
			tfVV.replaceAuxVars();
			if (mFormulas.getTrace().isCallPosition(i)) {
				mSsa.setLocalVarAssignmentAtPos(i, tfVV.getVersioneeredTerm());
				mVariable2Constant.setLocalVarAssignmentAtPos(i, tfVV.getSubstitutionMapping());
			} else {
				mSsa.setFormulaAtNonCallPos(i, tfVV.getVersioneeredTerm());
				mVariable2Constant.setFormulaAtNonCallPos(i, tfVV.getSubstitutionMapping());
			}
		}

		/*
		 * Step 4: We rename the postcondition.
		 */
		assert mCurrentVersionStack.size() == numberOfPendingCalls;
		assert numberOfPendingCalls > 0 || mStartOfCallingContext == -1 - numberPendingContexts;
		assert numberOfPendingCalls == 0 || numberPendingContexts == 0;

		final VariableVersioneer postCondVV = new VariableVersioneer(mFormulas.getPostcondition());
		postCondVV.versionPredicate();
		mSsa.setPostcondition(postCondVV.getVersioneeredTerm());
		mVariable2Constant.setPostcondition(postCondVV.getSubstitutionMapping());

	}

	/**
	 * Set new var version for all globals that are modifiable by the current procedure.
	 */
	protected void reVersionModifiableGlobals() {
		final Set<IProgramNonOldVar> modifiable = mModGlobVarManager.getModifiedBoogieVars(mCurrentProcedure);
		for (final IProgramVar bv : modifiable) {
			setCurrentVarVersion(bv, mStartOfCallingContext);
		}
	}

	/**
	 * Set new var version for all oldVars that are modifiable by the current procedure.
	 */
	protected void reVersionModifiableOldVars() {
		final Set<IProgramNonOldVar> modifiable = mModGlobVarManager.getModifiedBoogieVars(mCurrentProcedure);
		for (final IProgramNonOldVar bv : modifiable) {
			final IProgramOldVar oldVar = bv.getOldVar();
			setCurrentVarVersion(oldVar, mStartOfCallingContext);
		}
	}

	/**
	 * Compute identifier of the Constant that represents the branch encoder tv at position pos.
	 */
	public static String branchEncoderConstantName(final TermVariable tv, final int pos) {
		final String name = tv.getName() + "_" + pos;
		return name;
	}

	public Map<Term, IProgramVar> getConstants2BoogieVar() {
		return mConstants2BoogieVar;
	}

	public Map<IProgramVar, TreeMap<Integer, Term>> getIndexedVarRepresentative() {
		return mIndexedVarRepresentative;
	}

	public NestedFormulas<Term, Term> getSsa() {
		return mSsa;
	}

	public ModifiableNestedFormulas<Map<Term, Term>, Map<Term, Term>> getVariable2Constant() {
		return mVariable2Constant;
	}

	/**
	 * Get the current version of BoogieVariable bv. Construct this version if it does not exist yet.
	 */
	private Term getCurrentVarVersion(final IProgramVar bv) {
		Term result;
		if (bv.isGlobal()) {
			if (bv instanceof IProgramOldVar) {
				assert bv.isOldvar();
				final IProgramOldVar oldVar = (IProgramOldVar) bv;
				if (mModGlobVarManager.isModifiable(oldVar, mCurrentProcedure)) {
					result = currentLocalAndOldVarVersion.get(oldVar);
				} else {
					// not modifiable in current procedure
					// according to semantics value of oldvar is value of
					// non-oldvar at beginning of procedure
					// we use current var version of non-oldvar
					if (oldVar.getNonOldVar() == null) {
						throw new IllegalStateException("missing non-old var for oldVar " + oldVar);
					}
					result = getOrSetCurrentGlobalVarVersion(oldVar.getNonOldVar());
				}
			} else if (bv instanceof IProgramNonOldVar) {
				final IProgramNonOldVar bnov = (IProgramNonOldVar) bv;
				result = getOrSetCurrentGlobalVarVersion(bnov);
			} else if (bv instanceof IProgramConst) {
				result = getOrSetCurrentGlobalVarVersion(bv);
			} else {
				throw new AssertionError("unknown kind of IProgramVar " + bv.getClass().getSimpleName());
			}
		} else {
			result = currentLocalAndOldVarVersion.get(bv);
			if (result == null) {
				// variable was not yet assigned in the calling context
				result = setCurrentVarVersion(bv, mStartOfCallingContext);
			}
		}
		return result;
	}

	/**
	 * Get current version for global variable. Set current var version if it has not yet been set.
	 */
	private Term getOrSetCurrentGlobalVarVersion(final IProgramVar bv) {
		assert bv instanceof IProgramNonOldVar || bv instanceof IProgramConst : "not global";
		Term result;
		result = currentGlobalVarVersion.get(bv);
		if (result == null) {
			// variable was not yet assigned in trace
			// FIXME: in oder to be compliant with the documentation
			// we should use an initial calling context
			// -1-numberOfCallingContexts. But this should not have
			// an impact on correctness.
			result = setCurrentVarVersion(bv, -1);
		}
		return result;
	}

	/**
	 * Set the current version of BoogieVariable bv to the constant b_index and return b_index.
	 */
	private Term setCurrentVarVersion(final IProgramVar bv, final int index) {
		final Term var = buildVersion(bv, index);
		if (bv.isGlobal()) {
			if (bv.isOldvar()) {
				assert index == mStartOfCallingContext : "oldVars may only be assigned at entry of procedure";
				currentLocalAndOldVarVersion.put(bv, var);
			} else {
				currentGlobalVarVersion.put(bv, var);
			}
		} else {
			currentLocalAndOldVarVersion.put(bv, var);
		}
		return var;
	}

	/**
	 * Build constant bv_index that represents BoogieVar bv that obtains a new value at position index.
	 */
	private Term buildVersion(final IProgramVar bv, final int index) {
		TreeMap<Integer, Term> index2constant = mIndexedVarRepresentative.get(bv);
		if (index2constant == null) {
			index2constant = new TreeMap<>();
			mIndexedVarRepresentative.put(bv, index2constant);
		}
		assert !index2constant.containsKey(index) : "version was already constructed";
		final Term constant;
		if (bv instanceof IProgramConst) {
			constant = transferToCurrentScriptIfNecessary(bv.getDefaultConstant());
		} else {
			final Sort sort = transferToCurrentScriptIfNecessary(bv.getTermVariable()).getSort();
			constant = PredicateUtils.getIndexedConstant(bv.getGloballyUniqueId(), sort, index, mIndexedConstants,
					mScript);
		}
		index2constant.put(index, constant);
		return constant;
	}

	/**
	 * May the corresponding global var of the oldvar bv be modified in in the current calling context (according to
	 * modifies clauses?)
	 */
	private boolean modifiedInCurrentCallingContext(final IProgramVar bv) {
		if (!bv.isGlobal()) {
			throw new IllegalArgumentException(bv + " no global var");
		}
		UnmodifiableTransFormula oldVarAssignment;
		if (mStartOfCallingContext >= 0) {
			oldVarAssignment = mFormulas.getOldVarAssignment(mStartOfCallingContext);
		} else if (mStartOfCallingContext == -1) {
			// from some point of view each variable is modified in the
			// initial calling context, because variables get their
			// initial values here
			return true;
		} else {
			assert mStartOfCallingContext < -1;
			final int pendingReturnPosition = mPendingContext2PendingReturn.get(mStartOfCallingContext);
			oldVarAssignment = mFormulas.getOldVarAssignment(pendingReturnPosition);
		}
		boolean isModified;
		if (bv.isOldvar()) {
			isModified = oldVarAssignment.getAssignedVars().contains(bv);
		} else {
			isModified = oldVarAssignment.getInVars().keySet().contains(bv);
		}
		return isModified;
	}

	private Term transferToCurrentScriptIfNecessary(final Term term) {
		final Term result;
		if (mTransferToScriptNeeded) {
			result = mTermTransferrer.transform(term);
		} else {
			result = term;
		}
		return result;
	}

	private TermVariable transferToCurrentScriptIfNecessary(final TermVariable tv) {
		final TermVariable result;
		if (mTransferToScriptNeeded) {
			result = (TermVariable) mTermTransferrer.transform(tv);
		} else {
			result = tv;
		}
		return result;
	}

	class VariableVersioneer {
		private final UnmodifiableTransFormula mTF;
		private final IPredicate mPred;
		private final Map<Term, Term> mSubstitutionMapping = new HashMap<>();
		private final Term mFormula;

		public VariableVersioneer(final UnmodifiableTransFormula tf) {
			mTF = Objects.requireNonNull(tf);
			mPred = null;
			mFormula = transferToCurrentScriptIfNecessary(tf.getFormula());
		}

		public VariableVersioneer(final IPredicate pred) {
			mTF = null;
			mPred = pred;
			mFormula = transferToCurrentScriptIfNecessary(pred.getFormula());
		}

		public void versionInVars() {
			for (final IProgramVar bv : mTF.getInVars().keySet()) {
				final TermVariable tv = transferToCurrentScriptIfNecessary(mTF.getInVars().get(bv));
				final Term versioneered = getCurrentVarVersion(bv);
				mConstants2BoogieVar.put(versioneered, bv);
				mSubstitutionMapping.put(tv, versioneered);
			}
		}

		public void versionAssignedVars(final int currentPos) {
			for (final IProgramVar bv : mTF.getAssignedVars()) {
				final TermVariable tv = transferToCurrentScriptIfNecessary(mTF.getOutVars().get(bv));
				final Term versioneered = setCurrentVarVersion(bv, currentPos);
				mConstants2BoogieVar.put(versioneered, bv);
				mSubstitutionMapping.put(tv, versioneered);
			}
		}

		public void versionBranchEncoders(final int currentPos) {
			for (TermVariable tv : mTF.getBranchEncoders()) {
				tv = transferToCurrentScriptIfNecessary(tv);
				final String name = branchEncoderConstantName(tv, currentPos);
				mScript.declareFun(name, new Sort[0], tv.getSort());
				mSubstitutionMapping.put(tv, mScript.term(name));
			}
		}

		public void replaceAuxVars() {
			for (TermVariable tv : mTF.getAuxVars()) {
				tv = transferToCurrentScriptIfNecessary(tv);
				// construct constant only after variable was translated
				// in order to use the Sort of the right Script for the
				// construction
				final Term freshConst = constructFreshConstant(tv);
				mSubstitutionMapping.put(tv, freshConst);
			}
		}

		private Term constructFreshConstant(final TermVariable tv) {
			final Integer newIndex = mConstForTvCounter.increment(tv);
			final String name = SmtUtils.removeSmtQuoteCharacters(tv.getName()) + "_fresh_" + newIndex;
			final Sort resultSort = tv.getSort();
			mScript.declareFun(name, new Sort[0], resultSort);
			return mScript.term(name);
		}

		public void versionPredicate() {
			for (final IProgramVar bv : mPred.getVars()) {
				final TermVariable tv = transferToCurrentScriptIfNecessary(bv.getTermVariable());
				final Term versioneered = getCurrentVarVersion(bv);
				mConstants2BoogieVar.put(versioneered, bv);
				mSubstitutionMapping.put(tv, versioneered);
			}
		}

		public Term getVersioneeredTerm() {
			final Substitution subst = new Substitution(mScript, mSubstitutionMapping);
			final Term result = subst.transform(mFormula);
			assert result.getFreeVars().length == 0 : "free vars in versioneered term: " + result.getFreeVars();
			return result;
		}

		public Map<Term, Term> getSubstitutionMapping() {
			return mSubstitutionMapping;
		}

	}

}
