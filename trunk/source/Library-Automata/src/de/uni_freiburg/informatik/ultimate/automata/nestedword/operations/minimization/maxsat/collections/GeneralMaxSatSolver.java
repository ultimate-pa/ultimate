/*
 * Copyright (C) 2016 Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * Copyright (C) 2016 Christian Schilling <schillic@informatik.uni-freiburg.de>
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * MAX-SAT solver for propositional logic clauses. The satisfying assignment returned by this solver is a locally
 * optimal solution in the following sense. If you replace one false-assignment to a variable by a true-assignment then
 * the resulting mapping is not a valid assignment anymore. <br>
 * There is no guarantee that this locally optimal solution does not have to be a globally optimal solution (which is a
 * solution in which the number of true-assigned variables is maximal).
 * <p>
 * TODO add resolution to solver
 * <p>
 * TODO ignore temporary data structures before first decision
 * <p>
 * TODO detect clause duplicates
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <V>
 *            variable type
 */
@SuppressWarnings("squid:UselessParenthesesCheck")
public class GeneralMaxSatSolver<V> extends AbstractMaxSatSolver<V> {
	private static final Object[] EMPTY_ARRAY = new Object[0];

	private final SolverStack mStack;

	// TODO temporary improvement, should become more sophisticated
	private int mNumberOfNonHornClauses;

	private int mMaxNonHornClauses;

	/*
	 * used for debugging, can be very expensive for bigger automata!
	 * TODO remove after thoroughly testing
	 */
	private final boolean mShowExpensiveDebugLogs = false;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 */
	public GeneralMaxSatSolver(final AutomataLibraryServices services) {
		super(services);

		mStack = new SolverStack();
		synchronizeStack();
	}

	@SuppressWarnings("unchecked")
	@Override
	public void addHornClause(final V[] negativeAtoms, final V positiveAtom) {
		final V[] positiveAtoms;
		if (positiveAtom == null) {
			positiveAtoms = (V[]) EMPTY_ARRAY;
		} else {
			positiveAtoms = (V[]) new Object[] { positiveAtom };
		}
		addClause(negativeAtoms, positiveAtoms);
	}

	@Override
	public void addClause(final V[] negativeAtoms, final V[] positiveAtoms) {
		if (mDecisions > 0) {
			throw new UnsupportedOperationException("only legal before decisions were made");
		}
		assert mPropagatees.isEmpty();

		final Clause<V> clause = new Clause<V>(this, positiveAtoms, negativeAtoms);
		if (mShowExpensiveDebugLogs && mLogger.isDebugEnabled()) {
			mLogger.debug("creating clause: " + clause);
		}

		if (clause.isEquivalentToTrue()) {
			mClauses++;
			mTrivialClauses++;
			// clause is true and can be ignored if we will never backtrack
		} else {
			mClauses++;
			mCurrentLiveClauses++;
			mMaxLiveClauses = Math.max(mMaxLiveClauses, mCurrentLiveClauses);
			if (clause.isEquivalentToFalse()) {
				mConjunctionEquivalentToFalse = true;
				throw new UnsupportedOperationException("clause set is equivalent to false");
			} else {
				for (final V var : clause.getNegativeAtoms()) {
					mOccursNegative.addPair(var, clause);
				}
				for (final V var : clause.getPositiveAtoms()) {
					mOccursPositive.addPair(var, clause);
				}
				if (clause.isPseudoUnit()) {
					final Pair<V, Boolean> propagatee = clause.getPropagatee();
					mPropagatees.put(propagatee.getFirst(), propagatee.getSecond());
					propagateAll();
				} else if (!clause.isHorn()) {
					incrementNumberOfNonHornClauses();
				}
			}
		}
	}

	@Override
	protected Boolean getPersistentAssignment(final V var) {
		final Boolean result = mVariablesIrrevocablySet.get(var);
		assert (result == null)
				|| (!mStack.getVarTempSet().containsKey(var)) : "Unsynchronized assignment data structures.";
		return result;
	}

	@SuppressWarnings("squid:S2447")
	@Override
	protected VariableStatus getTemporaryAssignment(final V var) {
		final Iterator<Map<V, Boolean>> it = mStack.iterator();
		while (it.hasNext()) {
			final Map<V, Boolean> map = it.next();
			final Boolean result = map.get(var);
			if (result != null) {
				assert (!mVariablesIrrevocablySet.containsKey(var)) : "Unsynchronized assignment data structures.";
				// TODO cache result

				return result ? VariableStatus.TRUE : VariableStatus.FALSE;
			}
		}
		return VariableStatus.UNSET;
	}

	@Override
	protected void decideOne() {
		final V var = getUnsetVariable();

		// new decision level
		pushStack(var);
		mDecisions++;

		setVariable(var, true);
		propagateAll();
		if (mConjunctionEquivalentToFalse) {
			// first backtracking attempt
			backtrack(var);

			if (mConjunctionEquivalentToFalse) {
				// resetting variable did not help, backtrack further
				backtrackFurther(var);
			}
		}
		if (!mConjunctionEquivalentToFalse) {
			makeModificationsPersistentIfAllowed();
		}
	}

	@Override
	protected void setVariable(final V var, final boolean newStatus) {
		if (mShowExpensiveDebugLogs && mLogger.isDebugEnabled()) {
			mLogger.debug("setting variable " + var + " to " + newStatus);
		}
		assert mVariables.contains(var) : "unknown variable";
		assert !mVariablesIrrevocablySet.containsKey(var) : "variable already set";
//		assert checkClausesConsistent() : "clauses inconsistent";
		final Boolean oldStatus = mStack.getVarTempSet().put(var, newStatus);
		if (oldStatus != null) {
			throw new IllegalArgumentException("variable already set " + var);
		}
		mPropagatees.remove(var);
		reEvaluateStatusOfAllClauses(var);
//		assert checkClausesConsistent() : "clauses inconsistent";
	}

	@Override
	protected void makeAssignmentPersistent() {
		mLogger.debug("making current solver state persistent");
		while (true) {
			// make variable assignment persistent
			for (final Entry<V, Boolean> entry : mStack.getVarTempSet().entrySet()) {
				final V var = entry.getKey();

				// make assignment persistent
				mVariablesIrrevocablySet.put(var, entry.getValue());

				// mark variable as set
				mUnsetVariables.remove(var);
			}

			// remove clauses which were evaluated to true
			removeMarkedClauses();

			// pop current level from stack
			final boolean poppedLastFrame = popStack();
			if (poppedLastFrame) {
				break;
			}
		}
//		mLogger.debug("finished making solver state persistent");
	}

	@Override
	protected void backtrack(final V var) {
		mLogger.debug("backtracking");
		mWrongDecisions++;
		final Set<V> variablesIncorrectlySet = mStack.getVarTempSet().keySet();
		popStack();

		mPropagatees = new HashMap<>();
		mConjunctionEquivalentToFalse = false;
		reEvaluateStatusOfAllClauses(variablesIncorrectlySet, var);
		setVariable(var, false);
		propagateAll();
	}

	@Override
	protected void undoAssignment(final V var) {
		super.undoAssignment(var);
		// this solver treats the unset variables more carefully
		mUnsetVariables.add(var);
	}

	@Override
	protected void incrementNumberOfNonHornClauses() {
		mNumberOfNonHornClauses++;
		mLogger.debug("NumberOfNonHornClauses: " + mNumberOfNonHornClauses);
	}

	@Override
	protected void decrementNumberOfNonHornClauses() {
		mNumberOfNonHornClauses--;
		mLogger.debug("NumberOfNonHornClauses: " + mNumberOfNonHornClauses);
		assert mNumberOfNonHornClauses >= 0 : "Number of non-Horn clauses became negative.";
	}

	@Override
	protected void firstDecisionOrStop() {
		mMaxNonHornClauses = mNumberOfNonHornClauses;
	}

	@Override
	protected void log() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Clauses: ").append(mClauses);
		sb.append(" (thereof " + mTrivialClauses + " trivial clauses");
		sb.append(" and " + mMaxNonHornClauses + " Non-Horn clauses)");
		sb.append(" MaxLiveClauses: ").append(mMaxLiveClauses);
		sb.append(" Decisions : ").append(mDecisions);
		sb.append(" (thereof " + mWrongDecisions + " wrong decisions)");
		mLogger.info(sb.toString());
	}

	private void makeModificationsPersistentIfAllowed() {
		// true iff backtracking past this point is never necessary
		final boolean makeReallyPersistent = (mStack.isLowestStackLevel() || hasOnlyHornClauses());
		if (makeReallyPersistent) {
			makeAssignmentPersistent();
		} else {
			// only mark temporarily assigned variables as set
			for (final Entry<V, Boolean> entry : mStack.getVarTempSet().entrySet()) {
				mUnsetVariables.remove(entry.getKey());
			}
		}
	}

	private void backtrackFurther(final V var) {
		assert (mNumberOfNonHornClauses > 0) : "For Horn clauses backtracking should not be necessary for more than "
				+ "one level.";
		assert (var != null);
		V nextVar = var;
		do {
			// unassign the variable
			final boolean wasSet = mUnsetVariables.add(nextVar);
			assert wasSet : "The variable should have been set before backtracking.";

			// resetting variable did not help, backtrack further
			nextVar = mStack.getDecision();
			assert (nextVar != null);
			backtrack(nextVar);
		} while (mConjunctionEquivalentToFalse && (!mStack.isLowestStackLevel()));
	}

	private boolean hasOnlyHornClauses() {
		// TODO implement for optimization
		return mNumberOfNonHornClauses == 0;
	}

	/* --- solver stack (auxiliary data structure) interface methods --- */

	private void synchronizeStack() {
		// synchronize information with superclass
		mClausesMarkedForRemoval = mStack.getMarkedClauses();
	}

	private void pushStack(final V var) {
//		if (mLogger.isDebugEnabled()) {
//			mLogger.debug("+A stack level " + mStack.size() + ": " + mStack.peek());
//		}
		mStack.push(var);

		synchronizeStack();
//		if (mLogger.isDebugEnabled()) {
//			mLogger.debug("+B stack level " + mStack.size() + ": " + mStack.peek());
//		}
	}

	/**
	 * @return true iff lowest level was popped.
	 */
	private boolean popStack() {
//		if (mLogger.isDebugEnabled()) {
//			mLogger.debug("-A stack level " + mStack.size() + ": " + mStack.peek());
//		}
		final boolean poppedLowestLevel = mStack.pop();

		synchronizeStack();
//		if (mLogger.isDebugEnabled()) {
//			mLogger.debug("-B stack level " + mStack.size() + ": " + mStack.peek());
//		}
		return poppedLowestLevel;
	}

	/**
	 * Encapsulates a solver stack.
	 */
	private class SolverStack {
		private final ArrayDeque<StackContent> mStackInner;
		private StackContent mLowestLevel;
		private boolean mIsLowestLevel;

		public SolverStack() {
			this.mStackInner = new ArrayDeque<>();
			mLowestLevel = new StackContent();
			mIsLowestLevel = true;
		}

		/**
		 * Pops the current stack level, empties the stack if at lowermost level.
		 * 
		 * @return true iff stack is empty afterward
		 */
		public boolean pop() {
			if (!mStackInner.isEmpty()) {
				mStackInner.pop();
				mIsLowestLevel = mStackInner.isEmpty();
				return false;
			} else {
				mLowestLevel = new StackContent();
				return true;
			}
		}

		/**
		 * Pushes a new stack level.
		 * 
		 * @param var
		 *            current decision
		 */
		public void push(final V var) {
			mStackInner.push(new StackContent(var));
			mIsLowestLevel = false;
		}

		public boolean isLowestStackLevel() {
			assert (mIsLowestLevel == mStackInner.isEmpty());
			return mIsLowestLevel;
		}

		public Map<V, Boolean> getVarTempSet() {
			return getCurrentLevel().getVariablesTemporarilySet();
		}

		public V getDecision() {
			return getCurrentLevel().getVariableDecision();
		}

		public Set<Clause<V>> getMarkedClauses() {
			return getCurrentLevel().getClausesMarkedForRemoval();
		}

		/**
		 * NOTE: Must be used by alternation of <code>hasNext()</code> and <code>next()</code>. <br>
		 * <p>
		 * NOTE: Do not edit the stack during iteration!
		 * 
		 * @return unsynchronized iterator over all temporary maps
		 */
		public Iterator<Map<V, Boolean>> iterator() {
			return new StackIterator(mStackInner.iterator(), mLowestLevel);
		}

		private StackContent getCurrentLevel() {
			final StackContent sc = mIsLowestLevel ? mLowestLevel : mStackInner.peek();
			return sc;
		}

		/**
		 * Iterator through the stack.
		 * 
		 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
		 */
		private class StackIterator implements Iterator<Map<V, Boolean>> {
			private final Iterator<StackContent> mIt;
			private boolean mIsAtBottom;
			private final StackContent mLowestLevelStack;

			public StackIterator(final Iterator<StackContent> iterator, final StackContent lowestLevel) {
				mIt = iterator;
				mLowestLevelStack = lowestLevel;
			}

			@Override
			public boolean hasNext() {
				final boolean hasStackNext = mIt.hasNext();
				if (hasStackNext) {
					return true;
				} else if (mIsAtBottom) {
					return false;
				}
				mIsAtBottom = true;
				return true;
			}

			@Override
			public Map<V, Boolean> next() {
				final StackContent level = mIsAtBottom ? mLowestLevelStack : mIt.next();
				return level.getVariablesTemporarilySet();
			}
		}

		/**
		 * Contents in one stack level.
		 */
		private class StackContent {
			private final V mVariableDecision;
			private final Map<V, Boolean> mVariablesTemporarilySet;
			private final Set<Clause<V>> mClausesMarkedForRemoval;

			public StackContent() {
				this(null, false);
			}

			public StackContent(final V variable) {
				this(variable, false);
				assert (variable != null) : "Do not set the variable to null!";
			}

			@SuppressWarnings("squid:S1172")
			private StackContent(final V variable, final boolean dummy) {
				this.mVariableDecision = variable;
				this.mVariablesTemporarilySet = new HashMap<>();
				this.mClausesMarkedForRemoval = new LinkedHashSet<Clause<V>>();
			}

			public V getVariableDecision() {
				return mVariableDecision;
			}

			public Map<V, Boolean> getVariablesTemporarilySet() {
				return mVariablesTemporarilySet;
			}

			public Set<Clause<V>> getClausesMarkedForRemoval() {
				return mClausesMarkedForRemoval;
			}

			@Override
			public String toString() {
				final StringBuilder b = new StringBuilder();
				b.append("<");
				if (mVariableDecision == null) {
					b.append("lowest level, ");
				} else {
					b.append(mVariableDecision);
					b.append(" = current decision, ");
				}
				b.append(mVariablesTemporarilySet.size());
				b.append(" variables temporarily assigned, ");
				b.append(this.mClausesMarkedForRemoval.size());
				b.append(" clauses temporarily satisfied>");
				return b.toString();
			}
		}
	}
}
