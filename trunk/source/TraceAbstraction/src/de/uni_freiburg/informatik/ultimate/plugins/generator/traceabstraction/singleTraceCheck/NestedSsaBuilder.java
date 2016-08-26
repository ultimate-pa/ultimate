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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.MultiElementCounter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * A trace has single static assignment form (SSA) is each variable is assigned
 * exactly once ( http://en.wikipedia.org/wiki/Static_single_assignment_form).
 * 
 * This class transforms a trace to an SSA representation by renaming variables.
 * 
 * Roughly variable x is renamed to x_j, where j is the position where j is the
 * last position where x obtained a new value.
 * 
 * We use the SSA for checking satisfiability with an SMT solver, therefore we
 * represent the indexed variables by constants. Furthermore we replace all
 * auxiliary variables and branch encoders in the TransFormulas by fresh
 * constants.
 * 
 * We rename inVars of a variable x at trace position i+1 according to the
 * following scheme.
 * <ul>
 * <li>if x is local: we rename the inVar to x_j, where j is the largest
 * position <= i in the same calling context, where x is assigned. If x was not
 * assigned in this calling context up to position i, j is the start of the
 * calling context.
 * <li>if x is global and not oldvar: we rename the inVar to x_j, where j is the
 * largest position <=i where x is assigned. If x was not assigned up to
 * position i, j is the start of the lowest calling context (which is -1 if
 * there are no pending returns and numberOfPendingReturns-1 otherwise).
 * <li>if x is global and oldvar: if x is modifiable in the current calling
 * context we rename the inVar to x_j, where j is the start of the current
 * calling context, if x is not modifiable in the current calling context we
 * threat this variable as a non-oldVar
 * </ul>
 * If x is assigned at position i+1, we rename the outVar to x_{x+1}. If x in
 * not assigned at position i+1, the outVar does not exist or coincides with the
 * inVar and was already renamed above.
 * 
 * @author Matthias Heizmann
 * 
 */
public class NestedSsaBuilder {

	private final ILogger mLogger;

	private final static String s_GotosUnsupportedMessage = "TraceChecker is only applicable to RCFGs whose auxilliary goto edges have been removed";

	private final Script mScript;
	private final SmtManager mSmtManager;

	/**
	 * Map global BoogieVar bv to the constant bv_j that represents bv at the
	 * moment.
	 */
	final private Map<IProgramVar, Term> currentGlobalVarVersion = new HashMap<IProgramVar, Term>();
	/**
	 * Map local or oldVar BoogieVar bv to the constant bv_j that represents bv
	 * at the moment.
	 */
	protected Map<IProgramVar, Term> currentLocalAndOldVarVersion;

	/**
	 * Stores current versions for local or oldVar that are not visible at the
	 * moment.
	 */
	protected final Stack<Map<IProgramVar, Term>> currentVersionStack = new Stack<Map<IProgramVar, Term>>();

	private Integer startOfCallingContext;
	private final Stack<Integer> startOfCallingContextStack = new Stack<Integer>();

	private final Map<IProgramVar, TreeMap<Integer, Term>> mIndexedVarRepresentative = new HashMap<IProgramVar, TreeMap<Integer, Term>>();

	public Map<IProgramVar, TreeMap<Integer, Term>> getIndexedVarRepresentative() {
		return mIndexedVarRepresentative;
	}

	protected final Map<Term, IProgramVar> mConstants2BoogieVar = new HashMap<Term, IProgramVar>();

	public Map<Term, IProgramVar> getConstants2BoogieVar() {
		return mConstants2BoogieVar;
	}

	protected final NestedFormulas<TransFormula, IPredicate> mFormulas;

	protected final ModifiableNestedFormulas<Term, Term> mSsa;
	protected final ModifiableNestedFormulas<Map<Term, Term>, Map<Term, Term>> mVariable2Constant;

	private final ModifiableGlobalVariableManager mModGlobVarManager;

	private final Map<String, Term> mIndexedConstants = new HashMap<String, Term>();

	public NestedFormulas<Term, Term> getSsa() {
		return mSsa;
	}

	public ModifiableNestedFormulas<Map<Term, Term>, Map<Term, Term>> getVariable2Constant() {
		return mVariable2Constant;
	}

	protected String mcurrentProcedure;

	/**
	 * maps position of pending context to position of pending return the
	 * positions of pending contexts are -2,-3,-4,...
	 */
	protected final Map<Integer, Integer> mPendingContext2PendingReturn = new HashMap<Integer, Integer>();
	
	/**
	 * True iff the NestedSsaBuilder has to use a different Script than the
	 * Script that was used to construct the Term that occur in the
	 * NestedFormulas that are the input for the SSA construction.
	 */
	private final boolean mTransferToScriptNeeded;
	private final TermTransferrer mTermTransferrer;
	
	/**
	 * Counter that helps us to ensure that we construct a fresh constant
	 * for each occurrence of an aux var.
	 */
	private final MultiElementCounter<TermVariable> mConstForTvCounter =
			new MultiElementCounter<TermVariable>();
	

	public NestedSsaBuilder(final NestedWord<? extends IAction> trace, final SmtManager smtManager,
			final NestedFormulas<TransFormula, IPredicate> nestedTransFormulas,
			final ModifiableGlobalVariableManager globModVarManager, final ILogger logger,
			final boolean transferToScriptNeeded) {
		mLogger = logger;
		mScript = smtManager.getScript();
		mSmtManager = smtManager;
		mFormulas = nestedTransFormulas;
		mModGlobVarManager = globModVarManager;
		mSsa = new ModifiableNestedFormulas<Term, Term>(trace, new TreeMap<Integer, Term>());
		mVariable2Constant = new ModifiableNestedFormulas<Map<Term, Term>, Map<Term, Term>>(trace,
				new TreeMap<Integer, Map<Term, Term>>());
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
		 * Step 1: We rename the formulas in each pending context. The index
		 * starts from (-1 - numberPendingContexts) and ends at -2. Furthermore
		 * we need the oldVarAssignment and the globalVarAssignment they will
		 * link the pending context with the pending return.
		 */
		final Set<Integer> pendingReturnsRaw = mFormulas.getTrace().getPendingReturns().keySet();
		final Integer[] pendingReturns = pendingReturnsRaw.toArray(new Integer[pendingReturnsRaw.size()]);
		final int numberPendingContexts = pendingReturns.length;

		startOfCallingContext = -1 - numberPendingContexts;
		currentLocalAndOldVarVersion = new HashMap<IProgramVar, Term>();

		for (int i = numberPendingContexts - 1; i >= 0; i--) {
			final int pendingReturnPosition = pendingReturns[i];
			mPendingContext2PendingReturn.put(startOfCallingContext, pendingReturnPosition);
			final Return ret = (Return) mFormulas.getTrace().getSymbol(pendingReturnPosition);
			final Call correspondingCall = ret.getCorrespondingCall();
			mcurrentProcedure = correspondingCall.getPreceedingProcedure();

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

			final TransFormula localVarAssignment = correspondingCall.getTransitionFormula();
			final VariableVersioneer initLocalVarsVV = new VariableVersioneer(localVarAssignment);
			initLocalVarsVV.versionInVars();

			final String calledProcedure = correspondingCall.getCallStatement().getMethodName();
			final TransFormula oldVarAssignment = mFormulas.getOldVarAssignment(pendingReturnPosition);
			final VariableVersioneer initOldVarsVV = new VariableVersioneer(oldVarAssignment);
			initOldVarsVV.versionInVars();

			startOfCallingContextStack.push(startOfCallingContext);
			startOfCallingContext++;
			mcurrentProcedure = calledProcedure;
			currentVersionStack.push(currentLocalAndOldVarVersion);
			currentLocalAndOldVarVersion = new HashMap<IProgramVar, Term>();

			/*
			 * Parameters and oldVars of procedure form that the pending return
			 * returns get the index of the next pending context.
			 */
			initOldVarsVV.versionAssignedVars(startOfCallingContext);
			initLocalVarsVV.versionAssignedVars(startOfCallingContext);

			mSsa.setOldVarAssignmentAtPos(pendingReturnPosition, initOldVarsVV.getVersioneeredTerm());
			mVariable2Constant.setOldVarAssignmentAtPos(pendingReturnPosition, initOldVarsVV.getSubstitutionMapping());
			mSsa.setLocalVarAssignmentAtPos(pendingReturnPosition, initLocalVarsVV.getVersioneeredTerm());
			mVariable2Constant.setLocalVarAssignmentAtPos(pendingReturnPosition,
					initLocalVarsVV.getSubstitutionMapping());
		}

		assert (startOfCallingContext == -1);

		/*
		 * Step 2: We rename the formula of the precondition. We use as index
		 * -1.
		 */
		if (mcurrentProcedure == null) {
			assert numberPendingContexts == 0;
			final IAction firstCodeBlock = mFormulas.getTrace().getSymbolAt(0);
			mcurrentProcedure = firstCodeBlock.getPreceedingProcedure();
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
			final IAction symbol = mFormulas.getTrace().getSymbolAt(i);
//			if (symbol instanceof GotoEdge) {
//				throw new IllegalArgumentException(s_GotosUnsupportedMessage);
//			}

			TransFormula tf;
			if (mFormulas.getTrace().isCallPosition(i)) {
				tf = mFormulas.getLocalVarAssignment(i);
			} else {
				tf = mFormulas.getFormulaFromNonCallPos(i);
			}
			assert tf != null : "CodeBlock " + symbol + " has no TransFormula";
			final VariableVersioneer tfVV = new VariableVersioneer(tf);
			tfVV.versionInVars();

			if (mFormulas.getTrace().isCallPosition(i)) {
				assert (symbol instanceof Call) : "current implementation supports only Call";
				if (mFormulas.getTrace().isPendingCall(i)) {
					numberOfPendingCalls++;
				}
				final Call call = (Call) symbol;
				final String calledProcedure = call.getCallStatement().getMethodName();
				mcurrentProcedure = calledProcedure;
				final TransFormula oldVarAssignment = mFormulas.getOldVarAssignment(i);
				final VariableVersioneer initOldVarsVV = new VariableVersioneer(oldVarAssignment);
				initOldVarsVV.versionInVars();
				startOfCallingContextStack.push(startOfCallingContext);
				startOfCallingContext = i;

				currentVersionStack.push(currentLocalAndOldVarVersion);
				currentLocalAndOldVarVersion = new HashMap<IProgramVar, Term>();

				initOldVarsVV.versionAssignedVars(i);
				mSsa.setOldVarAssignmentAtPos(i, initOldVarsVV.getVersioneeredTerm());
				mVariable2Constant.setOldVarAssignmentAtPos(i, initOldVarsVV.getSubstitutionMapping());

				final TransFormula globalVarAssignment = mFormulas.getGlobalVarAssignment(i);
				final VariableVersioneer initGlobalVarsVV = new VariableVersioneer(globalVarAssignment);
				initGlobalVarsVV.versionInVars();
				initGlobalVarsVV.versionAssignedVars(i);
				mSsa.setGlobalVarAssignmentAtPos(i, initGlobalVarsVV.getVersioneeredTerm());
				mVariable2Constant.setGlobalVarAssignmentAtPos(i, initGlobalVarsVV.getSubstitutionMapping());

			}
			if (mFormulas.getTrace().isReturnPosition(i)) {
				final Return ret = (Return) symbol;
				mcurrentProcedure = ret.getCallerProgramPoint().getProcedure();
				currentLocalAndOldVarVersion = currentVersionStack.pop();
				startOfCallingContext = startOfCallingContextStack.pop();
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
		assert currentVersionStack.size() == numberOfPendingCalls;
		assert numberOfPendingCalls > 0 || startOfCallingContext == -1 - numberPendingContexts;
		assert numberOfPendingCalls == 0 || numberPendingContexts == 0;

		final VariableVersioneer postCondVV = new VariableVersioneer(mFormulas.getPostcondition());
		postCondVV.versionPredicate();
		mSsa.setPostcondition(postCondVV.getVersioneeredTerm());
		mVariable2Constant.setPostcondition(postCondVV.getSubstitutionMapping());

	}

	/**
	 * Set new var version for all globals that are modifiable by the current
	 * procedure.
	 */
	protected void reVersionModifiableGlobals() {
		final Set<IProgramVar> modifiable = mModGlobVarManager.getGlobalVarsAssignment(mcurrentProcedure).getAssignedVars();
		for (final IProgramVar bv : modifiable) {
			setCurrentVarVersion(bv, startOfCallingContext);
		}
	}

	/**
	 * Set new var version for all oldVars that are modifiable by the current
	 * procedure.
	 */
	protected void reVersionModifiableOldVars() {
		final Set<IProgramVar> modifiable = mModGlobVarManager.getOldVarsAssignment(mcurrentProcedure).getAssignedVars();
		for (final IProgramVar bv : modifiable) {
			setCurrentVarVersion(bv, startOfCallingContext);
		}
	}

	/**
	 * Compute identifier of the Constant that represents the branch encoder tv
	 * at position pos.
	 */
	public static String branchEncoderConstantName(final TermVariable tv, final int pos) {
		final String name = tv.getName() + "_" + pos;
		return name;
	}

	class VariableVersioneer {
		private final TransFormula mTF;
		private final IPredicate mPred;
		private final Map<Term, Term> mSubstitutionMapping = new HashMap<>();
		private final Term mformula;

		public VariableVersioneer(final TransFormula tf) {
			mTF = tf;
			mPred = null;
			mformula = transferToCurrentScriptIfNecessary(tf.getFormula());
		}

		public VariableVersioneer(final IPredicate pred) {
			mTF = null;
			mPred = pred;
			mformula = transferToCurrentScriptIfNecessary(pred.getFormula());
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
			final Integer newIndex = mConstForTvCounter.increase(tv);
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
			final Term result = subst.transform(mformula);
			assert result.getFreeVars().length == 0 : "free vars in versioneered term: " + String.valueOf(result.getFreeVars());
			return result;
		}

		public Map<Term, Term> getSubstitutionMapping() {
			return mSubstitutionMapping;
		}

	}

	/**
	 * Get the current version of BoogieVariable bv. Construct this version if
	 * it does not exist yet.
	 */
	private Term getCurrentVarVersion(final IProgramVar bv) {
		Term result;
		if (bv.isGlobal()) {
			if (bv instanceof IProgramOldVar) {
				assert bv.isOldvar();
				final IProgramOldVar oldVar = (IProgramOldVar) bv;
				if (mModGlobVarManager.isModifiable(oldVar, mcurrentProcedure)) {
					result = currentLocalAndOldVarVersion.get(oldVar);
				} else {
					// not modifiable in current procedure
					// according to semantics value of oldvar is value of
					// non-oldvar at beginning of procedure
					// we use current var version of non-oldvar
					result = getOrSetCurrentGlobalVarVersion(oldVar.getNonOldVar());
				}
			} else {
				final IProgramNonOldVar bnov = (IProgramNonOldVar) bv;
				result = getOrSetCurrentGlobalVarVersion(bnov);
			}
		} else {
			result = currentLocalAndOldVarVersion.get(bv);
			if (result == null) {
				// variable was not yet assigned in the calling context
				result = setCurrentVarVersion(bv, startOfCallingContext);
			}
		}
		return result;
	}

	/**
	 * Get current version for global variable. Set current var version if it
	 * has not yet been set.
	 */
	private Term getOrSetCurrentGlobalVarVersion(final IProgramNonOldVar bv) {
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
	 * Set the current version of BoogieVariable bv to the constant b_index and
	 * return b_index.
	 */
	private Term setCurrentVarVersion(final IProgramVar bv, final int index) {
		final Term var = buildVersion(bv, index);
		if (bv.isGlobal()) {
			if (bv.isOldvar()) {
				assert (index == startOfCallingContext) : "oldVars may only be assigned at entry of procedure";
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
	 * Build constant bv_index that represents BoogieVar bv that obtains a new
	 * value at position index.
	 */
	private Term buildVersion(final IProgramVar bv, final int index) {
		TreeMap<Integer, Term> index2constant = mIndexedVarRepresentative.get(bv);
		if (index2constant == null) {
			index2constant = new TreeMap<Integer, Term>();
			mIndexedVarRepresentative.put(bv, index2constant);
		}
		assert !index2constant.containsKey(index) : "version was already constructed";
		final Sort sort = transferToCurrentScriptIfNecessary(bv.getTermVariable()).getSort();
		final Term constant = PredicateUtils.getIndexedConstant(bv.getGloballyUniqueId(),
				sort, index, mIndexedConstants, mScript);
		index2constant.put(index, constant);
		return constant;
	}

	/**
	 * May the corresponding global var of the oldvar bv be modified in in the
	 * current calling context (according to modifies clauses?)
	 */
	private boolean modifiedInCurrentCallingContext(final IProgramVar bv) {
		if (!bv.isGlobal()) {
			throw new IllegalArgumentException(bv + " no global var");
		}
		TransFormula oldVarAssignment;
		if (startOfCallingContext >= 0) {
			oldVarAssignment = mFormulas.getOldVarAssignment(startOfCallingContext);
		} else if (startOfCallingContext == -1) {
			// from some point of view each variable is modified in the
			// initial calling context, because variables get their
			// initial values here
			return true;
		} else {
			assert startOfCallingContext < -1;
			final int pendingReturnPosition = mPendingContext2PendingReturn.get(startOfCallingContext);
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
}
