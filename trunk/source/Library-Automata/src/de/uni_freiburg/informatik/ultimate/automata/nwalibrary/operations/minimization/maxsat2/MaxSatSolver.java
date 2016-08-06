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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat2;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;

/**
 * MAX-SAT solver for propositional logic clauses.
 * The satisfying assignment returned by this solver is a locally optimal 
 * solution in the following sense. If you replace one false-assignment to
 * a variable by a true-assignment then the resulting mapping is not a valid
 * assignment anymore. <br>
 * There is no guarantee that this locally optimal solution does not have to
 * be a globally optimal solution (which is a solution in which the number
 * of true-assigned variables is maximal).
 * 
 * @author Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 * @param <V> variable type
 */
@SuppressWarnings("squid:UselessParenthesesCheck")
public class MaxSatSolver<V> extends AMaxSatSolver<V> {
	private final ArrayDeque<StackContent> mStack;
	
	// TODO temporary improvement, should become more sophisticated
	private int mNumberOfNonHornClauses;
	
	/**
	 * @param services Ultimate services
	 */
	public MaxSatSolver(final AutomataLibraryServices services) {
		super(services);
		
		mStack = new ArrayDeque<>();
		initializeStack();
	}

	@SuppressWarnings("unchecked")
	@Override
	public void addHornClause(final V[] negativeAtoms, final V positiveAtom) {
		final V[] positiveAtoms;
		if (positiveAtom == null) {
			positiveAtoms = (V[]) new Object[0];
		} else {
			positiveAtoms = (V[]) new Object[]{ positiveAtom };
		}
		addClause(negativeAtoms, positiveAtoms);
	}

	@Override
	public void addClause(final V[] negativeAtoms, final V[] positiveAtoms) {
		if (mDecisions > 0) {
			throw new UnsupportedOperationException(
					"only legal before decisions were made");
		}
		
		final Clause<V> clause = new Clause<V>(this, positiveAtoms, negativeAtoms);
//		if (mLogger.isDebugEnabled()) {
//			mLogger.debug("creating clause: " + clause);
//		}
		
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
				throw new UnsupportedOperationException(
						"clause set is equivalent to false");
			} else  {
//				if (mLogger.isDebugEnabled()) {
//					mLogger.debug("adding clause");
//				}
				assert clause.getUnsetAtoms() > 0;
				for (final V var :clause.getNegativeAtoms()) {
//					mLogger.debug("ONC " + mOccursNegative);
					mOccursNegative.addPair(var, clause);
//					mLogger.debug("ONC " + mOccursNegative);
				}
				for (final V var :clause.getPositiveAtoms()) {
					mOccursPositive.addPair(var, clause);
//					mLogger.debug("OPC " + mOccursPositive);
				}
				if (clause.getUnsetAtoms() == 1) {
					mPropagatees.add(clause);
					assert clause.isPropagatee();
					propagateAll();
				} else {
					assert !clause.isPropagatee();
					assert mPropagatees.isEmpty();
					if (! clause.isHorn(this)) {
						mNumberOfNonHornClauses++;
					}
				}
			}
		}
	}

	@Override
	protected Boolean getPersistentAssignment(final V var) {
		final Boolean result = mVariablesIrrevocablySet.get(var);
		assert (result == null) || (! getVarTempSet().containsKey(var)) :
				"Unsynchronized assignment data structures.";
		return result;
	}

	@SuppressWarnings("squid:S2447")
	@Override
	protected Boolean getTemporaryAssignment(final V var) {
		final Iterator<StackContent> it = mStack.iterator();
		while (it.hasNext()) {
			final HashMap<V, Boolean> map = it.next().mVariablesTemporarilySet;
			final Boolean result = map.get(var);
			if (result != null) {
				assert (! mVariablesIrrevocablySet.containsKey(var)) :
					"Unsynchronized assignment data structures.";
				// TODO cache result 
				return result;
			}
		}
		return null;
	}

	@Override
	protected void decideOne() {
		final V var = getUnsetVariable();
		
		// new decision level
		pushStack(var);
		mDecisions++;
		
		setVariable(var, true);
//		mLogger.debug("Propagatees: " + mPropagatees);
		propagateAll();
		if (mConjunctionEquivalentToFalse) {
			// first backtracking attempt
			backtrack(var);
			
			if (mConjunctionEquivalentToFalse) {
				// resetting variable did not help, backtrack further
				backtrackFurther(var);
			}
		}
		if (! mConjunctionEquivalentToFalse) {
			makeModificationsPersistentIfAllowed();
		}	
	}

		@Override
	protected void setVariable(final V var, final boolean newStatus) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("setting variable " + var + " to " + newStatus);
		}
		assert mVariables.contains(var) : "unknown variable";
		assert !mVariablesIrrevocablySet.containsKey(var) : "variable already set";
//		assert checkClausesConsistent() : "clauses inconsistent";
		final Boolean oldStatus = getVarTempSet().put(var, newStatus);
		if (oldStatus != null) {
			throw new IllegalArgumentException("variable already set " + var);
		}
		reEvaluateStatusOfAllClauses(var);
//		assert checkClausesConsistent() : "clauses inconsistent";
	}

	@Override
	protected void makeModificationsPersistent() {
		mLogger.debug("making current solver state persistent");
		while (true) {
			assert (! mStack.isEmpty());
			// make variable assignment persistent
			for (final Entry<V, Boolean> entry : getVarTempSet().entrySet()) {
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
		mWrongDecisions ++;
		final Set<V> variablesIncorrectlySet = getVarTempSet().keySet();
		popStack();
		
		mConjunctionEquivalentToFalse = false;
		reEvaluateStatusOfAllClauses(variablesIncorrectlySet, var);
		setVariable(var, false);
		propagateAll();
	}
	
	@Override
	protected void undoAssignment(final V var) {
		// this solver treats the unset variables more carefully
		mUnsetVariables.add(var);
	}

	@Override
	protected void log() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Clauses: ").append(mClauses);
		sb.append(" (thereof " + mTrivialClauses + " trivial clauses)");
		sb.append(" MaxLiveClauses: ").append(mMaxLiveClauses);
		sb.append(" Decisions : ").append(mDecisions);
		sb.append(" (thereof " + mWrongDecisions + " wrong decisions)");
		mLogger.info(sb.toString());
	}

	private void makeModificationsPersistentIfAllowed() {
		// true iff backtracking past this point is never necessary
		final boolean makeReallyPersistent =
				(isLowestStackLevel() || hasOnlyHornClauses());
		if (makeReallyPersistent) {
			makeModificationsPersistent();
		} else {
			// only mark temporarily assigned variables as unset
			for (final Entry<V, Boolean> entry : getVarTempSet().entrySet()) {
				mUnsetVariables.add(entry.getKey());
			}
		}
	}

	private void backtrackFurther(final V var) {
		assert (mNumberOfNonHornClauses > 0) :
			"For Horn clauses backtracking should not be necessary for more than one level.";
		assert (var != null);
		V nextVar = var;
		do {
			// unassign the variable
			final boolean wasSet = mUnsetVariables.add(nextVar);
			assert wasSet : "The variable should have been set before backtracking.";
			
			// resetting variable did not help, backtrack further
			nextVar = getDecision();
			assert (nextVar != null);
			backtrack(nextVar);
		} while (mConjunctionEquivalentToFalse && (! isLowestStackLevel()));
	}

	private boolean hasOnlyHornClauses() {
		// TODO implement for optimization
		return mNumberOfNonHornClauses == 0;
	}
	
	/* --- decision level stack (auxiliary data structure) --- */
	
	private boolean isLowestStackLevel() {
		return (mStack.size() == 1);
	}
	
	private void initializeStack() {
		// add lowest-level content
		mStack.push(new StackContent());
		
		// synchronize information with superclass
		mClausesMarkedForRemoval = getMarkedClauses();
	}
	
	private void pushStack(final V var) {
//		if (mLogger.isDebugEnabled()) {
//			mLogger.debug("+A stack level " + mStack.size() + ": " + mStack.peek());
//		}
		mStack.push(new StackContent(var));
		
		// synchronize information with superclass
		mClausesMarkedForRemoval = getMarkedClauses();
//		if (mLogger.isDebugEnabled()) {
//			mLogger.debug("+B stack level " + mStack.size() + ": " + mStack.peek());
//		}
	}
	
	private boolean popStack() {
//		if (mLogger.isDebugEnabled()) {
//			mLogger.debug("-A stack level " + mStack.size() + ": " + mStack.peek());
//		}
		mStack.pop();
		
		final boolean result = mStack.isEmpty();
		if (result) {
			// add lowest level again
			initializeStack();
		} else {
			// only synchronize information with superclass
			mClausesMarkedForRemoval = getMarkedClauses();
		}
//		if (mLogger.isDebugEnabled()) {
//			mLogger.debug("-B stack level " + mStack.size() + ": " + mStack.peek());
//		}
		return result;
	}
	
	private HashMap<V, Boolean> getVarTempSet() {
		return mStack.peek().mVariablesTemporarilySet;
	}
	
	private V getDecision() {
		return mStack.peek().mVariableDecision;
	}
	
	private Set<Clause<V>> getMarkedClauses() {
		return mStack.peek().mClausesMarkedForRemoval;
	}
	
	private class StackContent {
		private final V mVariableDecision;
		private final HashMap<V, Boolean> mVariablesTemporarilySet;
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
