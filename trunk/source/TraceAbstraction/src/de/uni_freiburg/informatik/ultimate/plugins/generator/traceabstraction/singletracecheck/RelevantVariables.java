/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.GlobalBoogieVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.RelationWithTreeSet;

/**
 * TODO: documentation, support for pending contexts
 *
 * @author Matthias Heizmann
 */
public class RelevantVariables {
	private final NestedFormulas<UnmodifiableTransFormula, IPredicate> mTraceWithFormulas;
	private final Set<IProgramVar>[] mForwardRelevantVariables;
	private final Set<IProgramVar>[] mBackwardRelevantVariables;
	private final Set<IProgramVar>[] mRelevantVariables;
	private final ModifiableGlobalsTable mModifiableGlobals;
	private final NestedConstraintAnalysis mNestedConstraintAnalysis;
	private final VariableOccurrence mOccurrence;

	@SuppressWarnings("unchecked")
	public RelevantVariables(final NestedFormulas<UnmodifiableTransFormula, IPredicate> traceWithFormulas,
			final ModifiableGlobalsTable modifiableGlobalsTable) {
		super();
		mModifiableGlobals = modifiableGlobalsTable;
		mTraceWithFormulas = traceWithFormulas;
		mNestedConstraintAnalysis = new NestedConstraintAnalysis(traceWithFormulas.getTrace(),
				new TreeMap<Integer, IPredicate>(), traceWithFormulas);
		mOccurrence = new VariableOccurrence();
		mForwardRelevantVariables = new Set[mTraceWithFormulas.getTrace().length() + 1];
		computeForwardRelevantVariables();
		mBackwardRelevantVariables = new Set[mTraceWithFormulas.getTrace().length() + 1];
		computeBackwardRelevantVariables();
		mRelevantVariables = new Set[mTraceWithFormulas.getTrace().length() + 1];
		computeRelevantVariables();
		// assert checkRelevantVariables() : " relevant variables incorrect";
	}

	/**
	 * Check if the sets of relevant variables are not too large. Each relevant variable has to occur before and after
	 * position i.
	 */
	private boolean checkRelevantVariables() {
		boolean result = true;
		for (int i = 0; i < mTraceWithFormulas.getTrace().length(); i++) {
			final Set<IProgramVar> relevantVars = mRelevantVariables[i + 1];
			for (final IProgramVar bv : relevantVars) {
				result &= mOccurrence.occursBefore(bv, i);
				assert result : "superfluous variable";
				result &= mOccurrence.occursAfter(bv, i);
				assert result : "superfluous variable";
			}
		}
		return result;
	}

	/**
	 * Efficient data structure that stores where variable occurs. Stores this separately for "in" and "out".
	 * Precondition gets index -1. Postcondition gets index trace.length()
	 */
	private class VariableOccurrence {
		RelationWithTreeSet<IProgramVar, Integer> inRelation = new RelationWithTreeSet<>();
		RelationWithTreeSet<IProgramVar, Integer> outRelation = new RelationWithTreeSet<>();

		public VariableOccurrence() {
			computeOccurrenceRelations();
		}

		/**
		 * Returns true iff set contains number between lower and upper (inclusive lower, inclusive upper).
		 */
		public boolean containsNumberBetween(final int lower, final int upper, final TreeSet<Integer> set) {
			final Integer ceiling = set.ceiling(lower);
			if (ceiling == null) {
				return false;
			}
			return ceiling <= upper;
		}

		public boolean occurs(final IProgramVar bv, final int start, final int end) {
			boolean result = false;
			final TreeSet<Integer> inSet = (TreeSet<Integer>) inRelation.getImage(bv);
			if (inSet != null) {
				result = result || containsNumberBetween(start + 1, end, inSet);
				if (result) {
					return result;
				}
			}
			final TreeSet<Integer> outSet = (TreeSet<Integer>) outRelation.getImage(bv);
			if (outSet != null) {
				result = result || containsNumberBetween(start, end - 1, outSet);
			}
			return result;
		}

		public boolean occursAfter(final IProgramVar bv, final int start) {
			boolean result = false;
			final TreeSet<Integer> inSet = (TreeSet<Integer>) inRelation.getImage(bv);
			if (inSet != null) {
				result = result || inSet.ceiling(start + 1) != null;
				if (result) {
					return result;
				}
			}
			final TreeSet<Integer> outSet = (TreeSet<Integer>) outRelation.getImage(bv);
			if (outSet != null) {
				result = result || outSet.ceiling(start) != null;
			}
			return result;
		}

		public boolean occursBefore(final IProgramVar bv, final int end) {
			boolean result = false;
			final TreeSet<Integer> inSet = (TreeSet<Integer>) inRelation.getImage(bv);
			if (inSet != null) {
				result = result || inSet.floor(end) != null;
				if (result) {
					return result;
				}
			}
			final TreeSet<Integer> outSet = (TreeSet<Integer>) outRelation.getImage(bv);
			if (outSet != null) {
				result = result || outSet.ceiling(end - 1) != null;
			}
			return result;
		}

		private void computeOccurrenceRelations() {
			addVars(outRelation, -1, mTraceWithFormulas.getPrecondition());
			addVars(inRelation, mTraceWithFormulas.getTrace().length(), mTraceWithFormulas.getPostcondition());
			for (int i = 0; i < mTraceWithFormulas.getTrace().length(); i++) {
				if (mTraceWithFormulas.getTrace().isInternalPosition(i)) {
					final ConstraintAnalysis ca = mNestedConstraintAnalysis.getFormulaFromNonCallPos(i);
					addVars(inRelation, i, ca.getConstraintIn());
					addVars(outRelation, i, ca.getConstraintOut());
				} else if (mTraceWithFormulas.getTrace().isCallPosition(i)) {
					final ConstraintAnalysis localVarAssignment = mNestedConstraintAnalysis.getLocalVarAssignment(i);
					final ConstraintAnalysis oldVarAssignment = mNestedConstraintAnalysis.getOldVarAssignment(i);
					final ConstraintAnalysis globalVarAssignment = mNestedConstraintAnalysis.getGlobalVarAssignment(i);
					addVars(inRelation, i, localVarAssignment.getConstraintIn());
					addVars(inRelation, i, oldVarAssignment.getConstraintIn());
					addVars(outRelation, i, globalVarAssignment.getConstraintOut());

					if (mTraceWithFormulas.getTrace().isPendingCall(i)) {
						addVars(inRelation, i, oldVarAssignment.getConstraintIn());
						addVars(outRelation, i, localVarAssignment.getConstraintOut());
					} else {
						// nothing more. The return has to take care of it
					}
				} else if (mTraceWithFormulas.getTrace().isReturnPosition(i)) {
					final int correspondingCallPosition = mNestedConstraintAnalysis.getTrace().getCallPosition(i);
					final ConstraintAnalysis oldVarAssignment =
							mNestedConstraintAnalysis.getOldVarAssignment(correspondingCallPosition);
					final ConstraintAnalysis localVarAssignment =
							mNestedConstraintAnalysis.getLocalVarAssignment(correspondingCallPosition);
					final ConstraintAnalysis tfReturn = mNestedConstraintAnalysis.getFormulaFromNonCallPos(i);

					// outVars from call become members of inRelation here
					addVars(inRelation, i, localVarAssignment.getConstraintOut());
					addVars(inRelation, i, oldVarAssignment.getConstraintOut());
					addVars(inRelation, i, tfReturn.getConstraintIn());
					addVars(outRelation, i, tfReturn.getConstraintOut());
				} else {
					throw new AssertionError();
				}
			}

		}

		private void addVars(final RelationWithTreeSet<IProgramVar, Integer> relation, final int i,
				final IPredicate precondition) {
			for (final IProgramVar bv : precondition.getVars()) {
				relation.addPair(bv, i);
			}

		}

		private void addVars(final RelationWithTreeSet<IProgramVar, Integer> relation, final int i,
				final Set<IProgramVar> set) {
			for (final IProgramVar bv : set) {
				relation.addPair(bv, i);
			}
		}
	}

	public Set<IProgramVar>[] getForwardRelevantVariables() {
		return mForwardRelevantVariables;
	}

	public Set<IProgramVar>[] getBackwardRelevantVariables() {
		return mBackwardRelevantVariables;
	}

	public Set<IProgramVar>[] getRelevantVariables() {
		return mRelevantVariables;
	}

	private void computeRelevantVariables() {
		for (int i = 0; i <= mTraceWithFormulas.getTrace().length(); i++) {
			mRelevantVariables[i] = new HashSet<>(mForwardRelevantVariables[i]);
			mRelevantVariables[i].retainAll(mBackwardRelevantVariables[i]);
		}
	}

	private void computeForwardRelevantVariables() {
		assert mForwardRelevantVariables[0] == null : "already computed";
		mForwardRelevantVariables[0] = new HashSet<>(mTraceWithFormulas.getPrecondition().getVars());
		for (int i = 1; i <= mTraceWithFormulas.getTrace().length(); i++) {
			assert mForwardRelevantVariables[i] == null : "already computed";
			mForwardRelevantVariables[i] = computeForwardRelevantVariables(i);
		}
	}

	private Set<IProgramVar> computeForwardRelevantVariables(final int i) {
		Set<IProgramVar> result;
		final Set<IProgramVar> currentRelevantVariables = mForwardRelevantVariables[i - 1];
		if (mTraceWithFormulas.getTrace().isInternalPosition(i - 1)) {
			final UnmodifiableTransFormula tf = mTraceWithFormulas.getFormulaFromNonCallPos(i - 1);
			result = computeSuccessorRvInternal(currentRelevantVariables, tf, i - 1);
		} else if (mTraceWithFormulas.getTrace().isCallPosition(i - 1)) {
			final UnmodifiableTransFormula oldVarAssignment = mTraceWithFormulas.getOldVarAssignment(i - 1);
			final UnmodifiableTransFormula localVarAssignment = mTraceWithFormulas.getLocalVarAssignment(i - 1);
			final UnmodifiableTransFormula globalVarAssignment = mTraceWithFormulas.getGlobalVarAssignment(i - 1);
			final String callee = mTraceWithFormulas.getTrace().getSymbol(i - 1).getSucceedingProcedure();
			final boolean isPendingCall = mTraceWithFormulas.getTrace().isPendingCall(i - 1);
			final int posOfCorrespondingReturn = mTraceWithFormulas.getTrace().getReturnPosition(i - 1);
			result = computeSuccessorRvCall(currentRelevantVariables, localVarAssignment, oldVarAssignment,
					globalVarAssignment, isPendingCall, callee, i - 1, posOfCorrespondingReturn);
		} else if (mTraceWithFormulas.getTrace().isReturnPosition(i - 1)) {
			final int correspondingCallPosition = mTraceWithFormulas.getTrace().getCallPosition(i - 1);
			final Set<IProgramVar> relevantVariablesBeforeCall = mForwardRelevantVariables[correspondingCallPosition];
			final UnmodifiableTransFormula tfReturn = mTraceWithFormulas.getFormulaFromNonCallPos(i - 1);
			final UnmodifiableTransFormula localVarAssignmentAtCall =
					mTraceWithFormulas.getLocalVarAssignment(correspondingCallPosition);
			final String callee = mTraceWithFormulas.getTrace().getSymbol(i - 1).getPrecedingProcedure();
			result = computeSuccessorRvReturn(currentRelevantVariables, relevantVariablesBeforeCall, tfReturn,
					localVarAssignmentAtCall, callee, correspondingCallPosition, i - 1);
		} else {
			throw new AssertionError();
		}
		return result;
	}

	private Set<IProgramVar> computeSuccessorRvInternal(final Set<IProgramVar> predRv,
			final UnmodifiableTransFormula tf, final int i) {
		final Set<IProgramVar> result = new HashSet<>(predRv.size());
		final Set<IProgramVar> alternativeResult = new HashSet<>(predRv);
		final ConstraintAnalysis tfConstraints = mNestedConstraintAnalysis.getFormulaFromNonCallPos(i);
		alternativeResult.removeAll(tfConstraints.getUnconstraintOut());
		alternativeResult.addAll(tfConstraints.getConstraintOut());

		for (final IProgramVar bv : predRv) {
			if (!tf.isHavocedOut(bv)) {
				result.add(bv);
			}
		}
		for (final IProgramVar bv : tf.getOutVars().keySet()) {
			if (!tf.isHavocedOut(bv)) {
				result.add(bv);
			}

		}
		assert result.equals(alternativeResult) : "not equal";
		return result;
	}

	private Set<IProgramVar> computeSuccessorRvCall(final Set<IProgramVar> predRv,
			final UnmodifiableTransFormula localVarAssignment, final UnmodifiableTransFormula oldVarAssignment,
			final UnmodifiableTransFormula globalVarAssignment, final boolean isPendingCall, final String callee,
			final int posOfCall, final int posOfCorrespondingReturn) {
		assert !isPendingCall || posOfCorrespondingReturn == Integer.MAX_VALUE;
		final Set<IProgramVar> result = new HashSet<>(predRv.size());
		addAllNonModifiableGlobals(predRv, callee, result);

		final ConstraintAnalysis globalVarAssignmentCa = mNestedConstraintAnalysis.getGlobalVarAssignment(posOfCall);
		result.addAll(globalVarAssignmentCa.getConstraintOut());

		final ConstraintAnalysis localVarAssignmentCa = mNestedConstraintAnalysis.getLocalVarAssignment(posOfCall);
		result.addAll(localVarAssignmentCa.getConstraintOut());

		final ConstraintAnalysis oldVarAssignmentCa = mNestedConstraintAnalysis.getOldVarAssignment(posOfCall);
		result.addAll(oldVarAssignmentCa.getConstraintOut());

		return result;
	}

	private void addAllNonModifiableGlobals(final Set<IProgramVar> bvSet, final String proc, final int startPos,
			final int endPos, final Set<IProgramVar> nonModifiableSet) {
		for (final IProgramVar bv : bvSet) {
			if (bv.isGlobal()) {
				if (bv instanceof IProgramConst) {
					if (occursBetween(bv, startPos, endPos)) {
						nonModifiableSet.add(bv);
					}
				} else {
					IProgramNonOldVar bnov;
					if (bv instanceof IProgramOldVar) {
						bnov = ((IProgramOldVar) bv).getNonOldVar();
					} else {
						bnov = (IProgramNonOldVar) bv;
					}
					if (!mModifiableGlobals.isModifiable(bnov, proc)) {
						if (occursBetween(bnov, startPos, endPos)) {
							nonModifiableSet.add(bnov);
						}
					}
				}
			}
		}
	}

	/**
	 * Copy all variables from sourceSet to targetSet if they are globals that are not modifiable by proc.
	 */
	private void addAllNonModifiableGlobals(final Set<IProgramVar> sourceSet, final String proc,
			final Set<IProgramVar> targetSet) {
		for (final IProgramVar bv : sourceSet) {
			if (bv.isGlobal()) {
				if (bv instanceof IProgramConst) {
					targetSet.add(bv);
				} else {
					IProgramNonOldVar bnov;
					if (bv instanceof IProgramOldVar) {
						bnov = ((IProgramOldVar) bv).getNonOldVar();
					} else {
						bnov = (IProgramNonOldVar) bv;
					}
					if (!mModifiableGlobals.isModifiable(bnov, proc)) {
						targetSet.add(bv);
					}
				}
			}
		}
	}

	private boolean occursBetween(final IProgramVar bv, final int lower, final int upper) {
		// return true;
		return mOccurrence.occurs(bv, lower, upper);
	}

	private Set<IProgramVar> computeSuccessorRvReturn(final Set<IProgramVar> returnPredRv,
			final Set<IProgramVar> callPredRv, final UnmodifiableTransFormula returnTF,
			final UnmodifiableTransFormula localVarAssignment, final String callee, final int posOfCall,
			final int posOfCorrespondingReturn) {
		final Set<IProgramVar> alternativeResult = new HashSet<>(callPredRv);
		final ConstraintAnalysis localVarAssignmentCa = mNestedConstraintAnalysis.getLocalVarAssignment(posOfCall);
		final ConstraintAnalysis returnTfCa =
				mNestedConstraintAnalysis.getFormulaFromNonCallPos(posOfCorrespondingReturn);
		// final ConstraintAnalysis oldVarAssignmentCa = mNestedConstraintAnalysis.getOldVarAssignment(posOfCall);

		// final ConstraintAnalysis globalVarAssignmentCa = mNestedConstraintAnalysis.getGlobalVarAssignment(posOfCall);

		alternativeResult.addAll(localVarAssignmentCa.getConstraintIn());
		// remove all modifiable (non-old) globals
		// they are only part of result if contained in the return pred
		final Iterator<IProgramVar> it = alternativeResult.iterator();
		while (it.hasNext()) {
			final IProgramVar bv = it.next();
			if (bv instanceof IProgramNonOldVar) {
				if (mModifiableGlobals.isModifiable((IProgramNonOldVar) bv, callee)) {
					it.remove();
				}
			}
		}

		// alternativeResult.addAll(oldVarAssignmentCa.getConstraintOut());
		// add all global vars cannot be modified by the callee -- NO! add all global nonOld vars!
		for (final IProgramVar bv : returnPredRv) {
			if (bv instanceof IProgramNonOldVar) {
				alternativeResult.add(bv);
			}
			// if (bv.isGlobal()) {
			// BoogieNonOldVar bnov;
			// if (bv instanceof BoogieOldVar) {
			// bnov = ((BoogieOldVar) bv).getNonOldVar();
			// } else {
			// bnov = (BoogieNonOldVar) bv;
			// }
			// if (!mModifiableGlobals.isModifiable(bnov, callee)) {
			// alternativeResult.add(bv);
			// }
			// }
		}
		// remove all that are havoced by the return
		alternativeResult.removeAll(returnTfCa.getUnconstraintOut());
		alternativeResult.addAll(returnTfCa.getConstraintOut());

		// add all vars that were relevant before the call
		final Set<IProgramVar> result = new HashSet<>();

		for (final IProgramVar bv : callPredRv) {
			if (!returnTF.isHavocedOut(bv)) {
				if (bv instanceof IProgramNonOldVar) {
					if (!mModifiableGlobals.isModifiable((IProgramNonOldVar) bv, callee)) {
						// add only if not modifiable
						result.add(bv);
					}
				} else {
					result.add(bv);
				}
			}
		}

		// add all global vars that are relevant before the return
		for (final IProgramVar bv : returnPredRv) {
			if (bv instanceof IProgramNonOldVar) {
				if (!returnTF.isHavocedOut(bv) && true) {
					result.add(bv);
				}
			}
		}
		// add all vars that are assigned by the call
		for (final IProgramVar bv : returnTF.getOutVars().keySet()) {
			if (!returnTF.isHavocedOut(bv) && true) {
				result.add(bv);
			}
		}
		// add all arguments of the call
		for (final IProgramVar bv : localVarAssignment.getInVars().keySet()) {
			if (!returnTF.isHavocedOut(bv) && true) {
				result.add(bv);
			}
		}
		assert alternativeResult.equals(result) : "new rsult ist differtn";
		return alternativeResult;
	}

	private void computeBackwardRelevantVariables() {
		assert mBackwardRelevantVariables[mTraceWithFormulas.getTrace().length()] == null : "already computed";
		mBackwardRelevantVariables[mTraceWithFormulas.getTrace().length()] =
				new HashSet<>(mTraceWithFormulas.getPostcondition().getVars());
		for (int i = mTraceWithFormulas.getTrace().length() - 1; i >= 0; i--) {
			assert mBackwardRelevantVariables[i] == null : "already computed";
			mBackwardRelevantVariables[i] = computeBackwardRelevantVariables(i);
		}
	}

	private Set<IProgramVar> computeBackwardRelevantVariables(final int i) {
		Set<IProgramVar> result;
		final Set<IProgramVar> currentRelevantVariables = mBackwardRelevantVariables[i + 1];
		if (mTraceWithFormulas.getTrace().isInternalPosition(i)) {
			final UnmodifiableTransFormula tf = mTraceWithFormulas.getFormulaFromNonCallPos(i);
			result = computePredecessorRvInternal(currentRelevantVariables, tf, i);
		} else if (mTraceWithFormulas.getTrace().isCallPosition(i)) {
			final UnmodifiableTransFormula localVarAssignment = mTraceWithFormulas.getLocalVarAssignment(i);
			final UnmodifiableTransFormula oldVarAssignment = mTraceWithFormulas.getOldVarAssignment(i);
			final UnmodifiableTransFormula globalVarAssignment = mTraceWithFormulas.getGlobalVarAssignment(i);
			final String callee = mTraceWithFormulas.getTrace().getSymbol(i).getSucceedingProcedure();
			if (mTraceWithFormulas.getTrace().isPendingCall(i)) {
				result = computePredecessorRvCall_Pending(currentRelevantVariables, localVarAssignment,
						oldVarAssignment, globalVarAssignment, callee, i);
			} else {
				final int correspondingReturnPosition = mTraceWithFormulas.getTrace().getReturnPosition(i);
				final Set<IProgramVar> relevantVariablesAfterReturn =
						mBackwardRelevantVariables[correspondingReturnPosition + 1];
				final UnmodifiableTransFormula returnTF =
						mTraceWithFormulas.getFormulaFromNonCallPos(correspondingReturnPosition);
				result = computePredecessorRvCall_NonPending(currentRelevantVariables, relevantVariablesAfterReturn,
						localVarAssignment, returnTF, oldVarAssignment, globalVarAssignment, callee, i,
						correspondingReturnPosition);
				addNonModifiableGlobalsAlongCalledProcedure(result, i);
			}
		} else if (mTraceWithFormulas.getTrace().isReturnPosition(i)) {
			final int correspondingCallPosition = mTraceWithFormulas.getTrace().getCallPosition(i);
			final UnmodifiableTransFormula oldVarAssignment =
					mTraceWithFormulas.getOldVarAssignment(correspondingCallPosition);
			final UnmodifiableTransFormula localVarAssignment =
					mTraceWithFormulas.getLocalVarAssignment(correspondingCallPosition);
			final UnmodifiableTransFormula tfReturn = mTraceWithFormulas.getFormulaFromNonCallPos(i);
			final String callee = mTraceWithFormulas.getTrace().getSymbol(i).getPrecedingProcedure();
			result = computePredecessorRvReturn(currentRelevantVariables, tfReturn, oldVarAssignment,
					localVarAssignment, callee, correspondingCallPosition, i);
		} else {
			throw new AssertionError();
		}
		return result;
	}

	/**
	 * Relevant variables directly before the call that are global are also relevant during the whole procedure.
	 * Variables that are modifiable by the procedure (and corresponding oldvars) have already been added (we have to
	 * add the others.
	 */
	private void addNonModifiableGlobalsAlongCalledProcedure(final Set<IProgramVar> relevantVariablesBeforeCall,
			final int i) {
		assert mTraceWithFormulas.getTrace().isCallPosition(i);
		assert !mTraceWithFormulas.getTrace().isPendingCall(i);
		final Set<IProgramVar> modifiableGlobals = mTraceWithFormulas.getGlobalVarAssignment(i).getOutVars().keySet();
		final Set<IProgramVar> oldVarsOfModifiableGlobals =
				mTraceWithFormulas.getOldVarAssignment(i).getOutVars().keySet();
		final Set<IProgramVar> varsThatWeHaveToAdd = new HashSet<>();
		for (final IProgramVar bv : relevantVariablesBeforeCall) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					if (!oldVarsOfModifiableGlobals.contains(bv)) {
						varsThatWeHaveToAdd.add(bv);
					}
				} else {
					if (!modifiableGlobals.contains(bv)) {
						varsThatWeHaveToAdd.add(bv);
					}
				}
			}
		}
		if (!varsThatWeHaveToAdd.isEmpty()) {
			final int returnPosition = mTraceWithFormulas.getTrace().getReturnPosition(i);
			for (int pos = i + 1; pos <= returnPosition; pos++) {
				mBackwardRelevantVariables[pos].addAll(varsThatWeHaveToAdd);
			}
		}
	}

	private Set<IProgramVar> computePredecessorRvInternal(final Set<IProgramVar> succRv,
			final UnmodifiableTransFormula tf, final int pos) {
		final Set<IProgramVar> alternativeResult = new HashSet<>(succRv);
		final ConstraintAnalysis tfConstraints = mNestedConstraintAnalysis.getFormulaFromNonCallPos(pos);
		alternativeResult.removeAll(tfConstraints.getUnconstraintIn());
		alternativeResult.addAll(tfConstraints.getConstraintIn());

		final Set<IProgramVar> result = new HashSet<>(succRv.size());
		for (final IProgramVar bv : succRv) {
			if (!tf.isHavocedIn(bv)) {
				result.add(bv);
			}
		}
		for (final IProgramVar bv : tf.getInVars().keySet()) {
			if (!tf.isHavocedIn(bv)) {
				result.add(bv);
			}
		}
		assert result.equals(alternativeResult) : "notEqual";
		return result;
	}

	// private boolean containsSomeNonHavocedOutVar(Set<BoogieVar> bvs, TransFormula tf) {
	// for (BoogieVar bv : tf.getOutVars().keySet()) {
	// if (!isHavoced(bv, tf) && bvs.contains(bv)) {
	// return true;
	// }
	// }
	// return false;
	// }

	private Set<IProgramVar> computePredecessorRvCall_NonPending(final Set<IProgramVar> callPredRv,
			final Set<IProgramVar> returnPredRv, final UnmodifiableTransFormula localVarAssignment,
			final UnmodifiableTransFormula returnTF, final UnmodifiableTransFormula oldVarAssignment,
			final UnmodifiableTransFormula globalVarAssignment, final String callee, final int posOfCall,
			final int posOfCorrespondingReturn) {
		final Set<IProgramVar> alternativeResult = new HashSet<>(returnPredRv);
		// final ConstraintAnalysis returnTfCa =
		// mNestedConstraintAnalysis.getFormulaFromNonCallPos(posOfCorrespondingReturn);
		// remove all that were reassigned
		// either explicitly by the return or implicitly as modifiable global
		alternativeResult.removeAll(returnTF.getAssignedVars());
		final ConstraintAnalysis globalVarAssignmentCa = mNestedConstraintAnalysis.getGlobalVarAssignment(posOfCall);
		alternativeResult.removeAll(globalVarAssignmentCa.getUnconstraintOut());

		// add all non-modifiable globals from the call successor
		addAllNonModifiableGlobals(callPredRv, callee, alternativeResult);

		// add all arguments of the call
		final ConstraintAnalysis localVarAssignmentCa = mNestedConstraintAnalysis.getLocalVarAssignment(posOfCall);
		alternativeResult.addAll(localVarAssignmentCa.getConstraintIn());

		// add all (non-old) global vars that are used in the procedure
		final ConstraintAnalysis oldVarAssignmentCa = mNestedConstraintAnalysis.getOldVarAssignment(posOfCall);
		alternativeResult.addAll(oldVarAssignmentCa.getConstraintIn());

		final Set<IProgramVar> result = new HashSet<>();
		for (final IProgramVar bv : returnPredRv) {
			if (!returnTF.getAssignedVars().contains(bv) && !globalVarAssignment.getAssignedVars().contains(bv)) {
				result.add(bv);
			}
		}
		result.addAll(localVarAssignment.getInVars().keySet());
		// for (BoogieVar bv : callPredRv) {
		// if (bv.isGlobal()) {
		// result.add(bv);
		// }
		// }
		// new
		addAllNonModifiableGlobals(callPredRv, callee, result);
		result.addAll(oldVarAssignment.getInVars().keySet());
		assert result.equals(alternativeResult) : "inconsistent result of live variables analysis";
		return alternativeResult;
	}

	private Set<IProgramVar> computePredecessorRvCall_Pending(final Set<IProgramVar> callPredRv,
			final UnmodifiableTransFormula localVarAssignment, final UnmodifiableTransFormula oldVarAssignment,
			final UnmodifiableTransFormula globalVarAssignment, final String callee, final int posOfCall) {
		final Set<IProgramVar> alternativeResult = new HashSet<>();

		// add all non-old global vars that are used in the procedure
		// and add non-old globals for all oldvars
		final ConstraintAnalysis oldVarAssignmentCa = mNestedConstraintAnalysis.getOldVarAssignment(posOfCall);
		final ConstraintAnalysis globalVarAssignmentCa = mNestedConstraintAnalysis.getGlobalVarAssignment(posOfCall);
		for (final IProgramVar bv : callPredRv) {
			if (bv instanceof IProgramNonOldVar) {
				if (globalVarAssignmentCa.getUnconstraintOut().contains(bv)) {
					// value not passed, we may omit it
				} else {
					alternativeResult.add(bv);
				}
			} else if (bv instanceof IProgramOldVar) {
				if (oldVarAssignmentCa.getUnconstraintOut().contains(bv)) {
					// value not passed, we may omit it
				} else {
					final IProgramNonOldVar pnov = ((IProgramOldVar) bv).getNonOldVar();
					alternativeResult.add(pnov);
				}
			}
		}

		final ConstraintAnalysis localVarAssignmentCa = mNestedConstraintAnalysis.getLocalVarAssignment(posOfCall);
		alternativeResult.addAll(localVarAssignmentCa.getConstraintIn());

		final Set<IProgramVar> result = new HashSet<>();
		result.addAll(localVarAssignment.getInVars().keySet());
		for (final IProgramVar bv : callPredRv) {
			if (bv instanceof IProgramNonOldVar) {
				if (!isHavoced(globalVarAssignment, oldVarAssignment, bv)) {
					result.add(bv);
				}
			}
		}

		assert result.equals(alternativeResult) : "notEqual";
		return alternativeResult;
	}

	private Set<IProgramVar> computePredecessorRvReturn(final Set<IProgramVar> returnSuccRv,
			final UnmodifiableTransFormula returnTf, final UnmodifiableTransFormula oldVarAssignmentAtCall,
			final UnmodifiableTransFormula localVarAssignmentAtCall, final String callee,
			final int posOfCorrespondingCall, final int posOfReturn) {
		final Set<IProgramVar> alternativeResult = new HashSet<>();
		// initially add all non-old globals
		for (final IProgramVar bv : returnSuccRv) {
			if (bv instanceof IProgramNonOldVar) {
				alternativeResult.add(bv);
			}
		}
		// remove all of these that were assigned on return
		alternativeResult.removeAll(returnTf.getAssignedVars());

		// add all parameters (needed e.g., for summaries)
		final ConstraintAnalysis localVarAssignmentCa =
				mNestedConstraintAnalysis.getLocalVarAssignment(posOfCorrespondingCall);
		alternativeResult.addAll(localVarAssignmentCa.getConstraintOut());

		// add procedure out vars
		final ConstraintAnalysis returnTfCa = mNestedConstraintAnalysis.getFormulaFromNonCallPos(posOfReturn);
		alternativeResult.addAll(returnTfCa.getConstraintIn());

		// add all oldvars
		final ConstraintAnalysis oldVarAssignmentCa =
				mNestedConstraintAnalysis.getOldVarAssignment(posOfCorrespondingCall);
		alternativeResult.addAll(oldVarAssignmentCa.getConstraintOut());

		final Set<IProgramVar> result = new HashSet<>(returnSuccRv.size());
		for (final IProgramVar bv : returnSuccRv) {
			if (bv instanceof IProgramNonOldVar) {
				if (!returnTf.isHavocedIn(bv) && true) {
					result.add(bv);
				}
			} else {
				// do nothing
			}
		}
		for (final IProgramVar bv : returnTf.getInVars().keySet()) {
			if (!returnTf.isHavocedIn(bv) && true) {
				result.add(bv);
			}
		}

		for (final IProgramVar bv : oldVarAssignmentAtCall.getInVars().keySet()) {
			if (!oldVarAssignmentAtCall.isHavocedIn(bv) && true) {
				result.add(bv);
			}
		}

		for (final IProgramVar bv : oldVarAssignmentAtCall.getOutVars().keySet()) {
			if (!oldVarAssignmentAtCall.isHavocedOut(bv) && true) {
				result.add(bv);
			}
		}

		for (final IProgramVar bv : localVarAssignmentAtCall.getOutVars().keySet()) {
			if (!localVarAssignmentAtCall.isHavocedOut(bv) && true) {
				result.add(bv);
			}
		}
		assert result.equals(alternativeResult) : "notEqual";
		return alternativeResult;
	}

	private static boolean isHavoced(final UnmodifiableTransFormula globalVarAssignment,
			final UnmodifiableTransFormula oldVarAssignment, final IProgramVar bv) {
		if (bv instanceof GlobalBoogieVar) {
			boolean result;
			if (bv instanceof IProgramOldVar) {
				result = oldVarAssignment.isHavocedOut(bv);
				// assert globalVarAssignment.isHavocedOut(((BoogieOldVar) bv).getNonOldVar()) == result :
				// "unexpected: unsat core contains only one of both, globalVarAssignment or oldVarAssignment";
			} else {
				assert bv instanceof IProgramNonOldVar;
				result = globalVarAssignment.isHavocedOut(bv);
				// assert oldVarAssignment.isHavocedOut(((BoogieNonOldVar) bv).getOldVar()) == result :
				// "unexpected: unsat core contains only one of both, globalVarAssignment or oldVarAssignment";
			}
			return result;
		}
		return false;
	}

	private static class ConstraintAnalysis {
		private final UnmodifiableTransFormula mTransFormula;
		private final Set<IProgramVar> mConstraintIn = new HashSet<>();
		private final Set<IProgramVar> mUnconstraintIn = new HashSet<>();
		private final Set<IProgramVar> mConstraintOut = new HashSet<>();
		private final Set<IProgramVar> mUnconstraintOut = new HashSet<>();
		private final Set<TermVariable> mFreeVars;

		public ConstraintAnalysis(final UnmodifiableTransFormula transFormula) {
			super();
			mTransFormula = transFormula;
			mFreeVars = new HashSet<>(Arrays.asList(transFormula.getFormula().getFreeVars()));
			analyze();
		}

		public Set<IProgramVar> getConstraintIn() {
			return mConstraintIn;
		}

		public Set<IProgramVar> getUnconstraintIn() {
			return mUnconstraintIn;
		}

		public Set<IProgramVar> getConstraintOut() {
			return mConstraintOut;
		}

		public Set<IProgramVar> getUnconstraintOut() {
			return mUnconstraintOut;
		}

		private void analyze() {
			for (final IProgramVar bv : mTransFormula.getInVars().keySet()) {
				final TermVariable inVar = mTransFormula.getInVars().get(bv);
				final TermVariable outVar = mTransFormula.getOutVars().get(bv);
				if (outVar == null) {
					mUnconstraintOut.add(bv);
				}
				if (mFreeVars.contains(inVar)) {
					mConstraintIn.add(bv);
				} else {
					if (inVar == outVar) {
						// do nothing. special case where inVar==outVar holds.
					} else {
						mUnconstraintIn.add(bv);
					}
				}
			}

			for (final IProgramVar bv : mTransFormula.getOutVars().keySet()) {
				final TermVariable inVar = mTransFormula.getInVars().get(bv);
				final TermVariable outVar = mTransFormula.getOutVars().get(bv);
				if (inVar == null) {
					mUnconstraintIn.add(bv);
				}
				if (mFreeVars.contains(outVar)) {
					mConstraintOut.add(bv);
				} else {
					if (inVar == outVar) {
						// do nothing. special case where inVar==outVar holds.
					} else {
						mUnconstraintOut.add(bv);
					}
				}
			}

		}

		@Override
		public String toString() {
			return "ConstraintAnalysis [mConstraintIn=" + mConstraintIn + ", mUnconstraintIn=" + mUnconstraintIn
					+ ", mConstraintOut=" + mConstraintOut + ", mUnconstraintOut=" + mUnconstraintOut + "]";
		}

	}

	private static class NestedConstraintAnalysis extends ModifiableNestedFormulas<ConstraintAnalysis, IPredicate> {
		public NestedConstraintAnalysis(final NestedWord<? extends IAction> nestedWord,
				final SortedMap<Integer, IPredicate> pendingContexts,
				final NestedFormulas<UnmodifiableTransFormula, IPredicate> traceWithFormulas) {
			super(nestedWord, pendingContexts);
			for (int i = 0; i < nestedWord.length(); i++) {
				if (getTrace().isCallPosition(i)) {
					final UnmodifiableTransFormula globalVarAssignment = traceWithFormulas.getGlobalVarAssignment(i);
					setGlobalVarAssignmentAtPos(i, new ConstraintAnalysis(globalVarAssignment));
					final UnmodifiableTransFormula oldVarAssignment = traceWithFormulas.getOldVarAssignment(i);
					setOldVarAssignmentAtPos(i, new ConstraintAnalysis(oldVarAssignment));
					final UnmodifiableTransFormula localVarAssignment = traceWithFormulas.getLocalVarAssignment(i);
					setLocalVarAssignmentAtPos(i, new ConstraintAnalysis(localVarAssignment));
				} else {
					final UnmodifiableTransFormula tf = traceWithFormulas.getFormulaFromNonCallPos(i);
					setFormulaAtNonCallPos(i, new ConstraintAnalysis(tf));
				}
			}

		}
	}

	//
	// /**
	// * Return true if this TransFormula modifies the BoogieVar bv, but after
	// * executing the TransFormula every value of bv is possible. This is the
	// * case for a variable x and the TransFormula of the statement havoc x.
	// */
	// private boolean isHavoced(BoogieVar bv, TransFormula tf) {
	// TermVariable outVar = tf.getOutVars().get(bv);
	// if (outVar == null) {
	// return false;
	// } else {
	// return !Arrays.asList(tf.getFormula().getFreeVars()).contains(tf.getOutVars().get(bv));
	// }
	// }

}
