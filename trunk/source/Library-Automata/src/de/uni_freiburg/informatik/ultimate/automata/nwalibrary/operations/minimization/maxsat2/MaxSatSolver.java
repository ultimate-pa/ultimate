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
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;

/**
 * MAX-SAT solver for propositional logic clauses.
 * The satisfying assignment returned by this solver is a locally optimal 
 * solution in the following sense. If you replace one false-assignment to
 * a variable by a true-assignment then the resulting mapping is not a valid
 * assignment anymore.
 * There is no guarantee that this locally optimal solution does not have to
 * be a globally optimal solution (which is a solution in which the number
 * of true-assigned variables is maximal).  
 * @author Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 * @param <V> Kind of objects that are used as variables.
 */
public class MaxSatSolver<V> extends AMaxSatSolver<V> {
	// TODO<backtracking> move back to superclass
	private final Map<V, Boolean> mVariablesIrrevocablySet =
			new HashMap<V, Boolean>();
	private final ArrayDeque<HashMap<V, Boolean>> mVariablesTemporarilySetStack;
	private HashMap<V, Boolean> mVariablesTemporarilySet;
	private final ArrayDeque<V> mVariableDecisionStack = new ArrayDeque<>();
	
	/**
	 * @param services Ultimate services
	 */
	public MaxSatSolver(final AutomataLibraryServices services) {
		super(services);
		
		mVariablesTemporarilySetStack = new ArrayDeque<HashMap<V, Boolean>>();
		mVariablesTemporarilySet = new HashMap<>();
		mVariablesTemporarilySetStack.push(mVariablesTemporarilySet);
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
			throw new UnsupportedOperationException("only legal before decisions were made");
		}
		
		final Clause<V> clause = new Clause<V>(this, positiveAtoms, negativeAtoms);
		
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
			} else  {
				assert clause.getUnsetAtoms() > 0;
				for (final V var :clause.getNegativeAtoms()) {
					mOccursNegative.addPair(var, clause);
				}
				for (final V var :clause.getPositiveAtoms()) {
					mOccursPositive.addPair(var, clause);
				}
				if (clause.getUnsetAtoms() == 1) {
					mPropagatees.add(clause);
					assert clause.isPropagatee();
					propagateAll();
				} else {
					assert !clause.isPropagatee();
					assert mPropagatees.isEmpty();
				}
			}
		}
	}

	@Override
	public Map<V, Boolean> getValues() {
		// TODO<backtracking>
		return Collections.unmodifiableMap(mVariablesIrrevocablySet);
	}
	
	@Override
	protected Boolean getPersistentAssignment(final V var) {
		// TODO<backtracking>
		final Boolean result = mVariablesIrrevocablySet.get(var);
		assert (result == null) || (! mVariablesTemporarilySet.containsKey(var)) :
				"Unsynchronized assignment data structures.";
		return result;
	}

	@Override
	protected Boolean getTemporaryAssignment(final V var) {
		// TODO<backtracking>
		final Boolean result = mVariablesTemporarilySet.get(var);
		assert (result == null) || (! mVariablesIrrevocablySet.containsKey(var)) :
			"Unsynchronized assignment data structures.";
		return result;
	}

	@Override
	protected void decideOne() {
		mDecisions++;
		if (! mVariableDecisionStack.isEmpty()) {
			mVariablesTemporarilySet = new HashMap<>();
			mVariablesTemporarilySetStack.push(mVariablesTemporarilySet);
		}
		final V var = getUnsetVariable();
		mVariableDecisionStack.push(var);
		setVariable(var, true);
		propagateAll();
		if (mConjunctionEquivalentToFalse) {
			backtrack(var);
			
			while (mConjunctionEquivalentToFalse &&
					! mVariableDecisionStack.isEmpty()) {
				// resetting variable did not help, backtrack further
				backtrackPrevious(); // TODO<backtracking> correct?
			}
		} else {
			makeModificationsPersistent();
		}
	}

	@Override
	protected void setVariable(final V var, final boolean newStatus) {
		// TODO<backtracking>
		assert mVariables.contains(var) : "unknown variable";
		assert !mVariablesIrrevocablySet.containsKey(var) : "variable already set";
//		assert checkClausesConsistent() : "clauses inconsistent";
		final Boolean oldStatus = mVariablesTemporarilySet.put(var, newStatus);
		if (oldStatus != null) {
			throw new IllegalArgumentException("variable already set " + var);
		}
		reEvaluateStatusOfAllClauses(var);
//		assert checkClausesConsistent() : "clauses inconsistent";
	}

	@Override
	protected void makeModificationsPersistent() {
		// TODO<backtracking>
		// true iff backtracking past this point is never necessary
		final boolean unbacktrackable = mVariableDecisionStack.isEmpty();
		
		if (unbacktrackable) {
			removeClauses(mClausesMarkedForRemoval);
			mClausesMarkedForRemoval = new LinkedHashSet<>();
			for (final HashMap<V, Boolean> map : mVariablesTemporarilySetStack) {
				for (final Entry<V, Boolean> entry : map.entrySet()) {
					mVariablesIrrevocablySet.put(entry.getKey(), entry.getValue());
					final boolean wasUnset = mUnsetVariables.remove(entry.getKey());
					assert wasUnset;
				}
			}
			mVariablesTemporarilySetStack.clear();
		}
		
		mVariablesTemporarilySet = new HashMap<>();
		mVariablesTemporarilySetStack.push(mVariablesTemporarilySet);
	}

	@Override
	protected void backtrack(final V var) {
		mWrongDecisions ++;
		final V var2 = mVariableDecisionStack.pop();
		assert (var.equals(var2)) : "illegal first-level backtracking";
		mClausesMarkedForRemoval = new LinkedHashSet<>();
		final HashMap<V, Boolean> variablesIncorrectlySet =
				mVariablesTemporarilySetStack.pop();
		mVariablesTemporarilySet = mVariablesTemporarilySetStack.peek();
		if (mVariablesTemporarilySet == null) {
			mVariablesTemporarilySet = new HashMap<>();
			mVariablesTemporarilySetStack.push(mVariablesTemporarilySet);
		}
		mConjunctionEquivalentToFalse = false;
		for (final V tmpVar : variablesIncorrectlySet.keySet()) {
			/*
			 * TODO some clauses are reevaluated several times
			 *      (if they contain several reset variables)
			 */
			reEvaluateStatusOfAllClauses(tmpVar);
		}
		setVariable(var, false);
	}

	private void backtrackPrevious() {
		assert (! mVariableDecisionStack.isEmpty());
		final V var = mVariableDecisionStack.peek();
		backtrack(var);
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
}
