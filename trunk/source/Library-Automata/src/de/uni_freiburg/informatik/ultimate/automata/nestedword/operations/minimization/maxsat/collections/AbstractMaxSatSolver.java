/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Abstract MAX-SAT solver for propositional logic clauses.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <V>
 *            Kind of objects that are used as variables.
 */
public abstract class AbstractMaxSatSolver<V> {
	protected final AutomataLibraryServices mServices;
	protected final ILogger mLogger;

	// TODO remove this data structure which is only used for assertions in the long term
	protected final Set<V> mVariables = new HashSet<>();

	protected final Map<V, Boolean> mVariablesIrrevocablySet = new HashMap<>();

	/*
	 * NOTE: The semantics of this variable differ for different solvers.
	 *       In the old solver, this variable is not always synchronized, which
	 *       only happens after a successful assignment.
	 *       In the new solver, this variable is synchronized more often, namely
	 *       also during backtracking.
	 */
	protected final Set<V> mUnsetVariables = new HashSet<>();
	/**
	 * A clause is pseudo-unit if it has exactly one unset literal and is not equivalent to true at the moment. We call
	 * the pair (variable, assignment) a propagatee.
	 */
	protected Map<V, Boolean> mPropagatees = new LinkedHashMap<>();
	protected boolean mConjunctionEquivalentToFalse;
	protected Set<Clause<V>> mClausesMarkedForRemoval = new LinkedHashSet<>();

	/*
	 * NOTE: There is no need to separate the occurrence as positive or negative
	 *       literal at the moment. Still, having only one relation is slower in
	 *       practice.
	 */
	protected final HashRelation<V, Clause<V>> mOccursPositive = new HashRelation<>();
	protected final HashRelation<V, Clause<V>> mOccursNegative = new HashRelation<>();

	protected int mDecisions;
	protected int mWrongDecisions;
	protected int mClauses;
	/**
	 * A clause is trivial if we were able to evaluate it to true when it was added.
	 */
	protected int mTrivialClauses;
	protected int mCurrentLiveClauses;
	protected int mMaxLiveClauses;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 */
	public AbstractMaxSatSolver(final AutomataLibraryServices services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		Clause.trues = 0;
		Clause.falses = 0;
		Clause.neithers = 0;
	}

	/**
	 * @return The number of variables.
	 */
	public int getNumberOfVariables() {
		return mVariables.size();
	}

	/**
	 * @return The number of clauses.
	 */
	public int getNumberOfClauses() {
		return mClauses;
	}

	/**
	 * Add a new variable. Variables have to be added before they can be used in clauses.
	 * 
	 * @param var
	 *            variable
	 */
	public void addVariable(final V var) {
		final boolean modified = mVariables.add(var);
		if (!modified) {
			throw new IllegalArgumentException("variable already added " + var);
		}
		mUnsetVariables.add(var);
	}

	/**
	 * Add a new Horn clause. We call the variables on the left-hand side negativeAtoms and the variable on the
	 * right-hand side the positive atom.
	 * 
	 * @param negativeAtoms
	 *            array of non-null variables
	 * @param positiveAtom
	 *            variable that may be null. If the variable is null it considered as true. If you want to assert only a
	 *            negative atom, you have to use null as positive Atom
	 * @deprecated This method is only present for legacy reasons and just converts the Horn clause to a general clause
	 *             in the general solver. The caller should instead directly call the general <code>addClause()</code>
	 *             method. For the old solver, this method is still needed.
	 */
	@Deprecated
	public abstract void addHornClause(final V[] negativeAtoms, final V positiveAtom);

	/**
	 * Add a new clause. We call the variables on the left-hand side negativeAtoms and the variables on the right-hand
	 * side the positive atoms.
	 * 
	 * @param negativeAtoms
	 *            array of non-null variables considered negative
	 * @param positiveAtoms
	 *            array of non-null variables considered positive. If you want to assert only a negative atom, you have
	 *            to use an empty array as positive atoms.
	 */
	public abstract void addClause(final V[] negativeAtoms, final V[] positiveAtoms);

	/**
	 * Solve the given MAX-SAT problem for the given set of Horn clauses.
	 * 
	 * @return true iff the given set of Horn clauses is satisfiable.
	 */
	public boolean solve() throws AutomataOperationCanceledException {
		mLogger.info("starting solver");
		propagateAll();
		makeAssignmentPersistent();
		mLogger.debug("trues before first decision: " + Clause.trues);
		mLogger.debug("falses before first decision: " + Clause.falses);
		mLogger.debug("neithers before first decision: " + Clause.neithers);
		firstDecisionOrStop();
		while (!mUnsetVariables.isEmpty()) {
			decideOne();
			if (mConjunctionEquivalentToFalse) {
				return false;
			}
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(getRunningTaskInfo());
			}
		}
		makeAssignmentPersistent();
		mLogger.info("finished solver");
		log();
		mLogger.debug("trues total: " + Clause.trues);
		mLogger.debug("falses total: " + Clause.falses);
		mLogger.debug("neithers total: " + Clause.neithers);
		return true;
	}

	/**
	 * Called after all clauses have been added and pseudo-unit clauses have been propagated.
	 * <p>
	 * In other words, this method is called before the first decision in case there is at least one unassigned variable
	 * left.
	 * <p>
	 * The intention is that implementing solvers are informed about the beginning of the decision phase.
	 */
	protected void firstDecisionOrStop() {
		// do nothing in the general case
	}

	/**
	 * Prints the log message.
	 */
	protected abstract void log();

	/**
	 * @return The locally optimal satisfying assignment.
	 */
	public Map<V, Boolean> getValues() {
		return Collections.unmodifiableMap(mVariablesIrrevocablySet);
	}

	/**
	 * @param var
	 *            variable
	 * @return The locally optimal satisfying assignment.
	 */
	public VariableStatus getValue(final V var) {
		final Boolean value = getPersistentAssignment(var);
		if (value == null) {
			return VariableStatus.UNSET;
		} else if (value) {
			return VariableStatus.TRUE;
		} else {
			return VariableStatus.FALSE;
		}
	}

	/**
	 * Assignment to the variable which is guaranteed to not be backtracked.
	 * 
	 * @param var
	 *            variable
	 * @return <code>true</code>/<code>false</code> if assigned, <code>null</code> otherwise
	 */
	protected abstract Boolean getPersistentAssignment(V var);

	/**
	 * Assignment to the variable which is not guaranteed to not be backtracked.
	 * 
	 * @param var
	 *            variable
	 * @return assignment status
	 */
	protected abstract VariableStatus getTemporaryAssignment(V var);

	protected VariableStatus getCurrentVariableStatus(final V var) {
		assert mVariables.contains(var);
		final Boolean irr = getPersistentAssignment(var);
		if (irr != null) {
			if (irr) {
				return VariableStatus.TRUE;
			} else {
				return VariableStatus.FALSE;
			}
		}
		return getTemporaryAssignment(var);
	}

	/**
	 * Backtracking mechanism.
	 * 
	 * @param var
	 *            last set variable which lead to inconsistency
	 */
	protected abstract void backtrack(final V var);

	/**
	 * Make current assignment persistent.
	 */
	protected abstract void makeAssignmentPersistent();

	/**
	 * Propagate and assign all pseudo-unit clauses (under current assignment).
	 */
	protected void propagateAll() {
		while (!mPropagatees.isEmpty() && !mConjunctionEquivalentToFalse) {
			propagateOne();
		}
	}

	/**
	 * Assign pseudo-unit clause (under current assignment).
	 */
	private void propagateOne() {
		final Entry<V, Boolean> unsetAtom = getPropagatee();
		setVariable(unsetAtom.getKey(), unsetAtom.getValue());
	}

	/**
	 * current policy: just return the next propagatee from the set
	 * <p>
	 * TODO other policies The only goal for optimization here is to find contradictions faster. If no contradiction is
	 * found, all policies should take the same time.
	 * <p>
	 * One policy could be to prefer clauses with positive/negative variable, but it is not clear whether this makes
	 * sense.
	 * <p>
	 * Another possibility could be to prefer variables which also occur in a non-Horn clause to remove the number of
	 * such clauses.
	 * 
	 * @return pair of unset variable and assignment value
	 */
	private Entry<V, Boolean> getPropagatee() {
		final Iterator<Entry<V, Boolean>> it = mPropagatees.entrySet().iterator();
		final Entry<V, Boolean> propagatee = it.next();
		// Do not remove, we remove while updating clause, this will ease debugging.
		return propagatee;
	}

	/**
	 * Sets a status to a variable.
	 * 
	 * @param var
	 *            variable
	 * @param newStatus
	 *            new status
	 */
	protected abstract void setVariable(final V var, final boolean newStatus);

	/**
	 * Reevaluate all clauses whose variables have been incorrectly set.
	 * <p>
	 * NOTE: must be called from backtracking, as we modify the set
	 * 
	 * @param variablesIncorrectlySet
	 *            variables to be unset (modified here)
	 * @param varToBeSetFalse
	 *            variable which is going to be set to false soon
	 */
	protected void reEvaluateStatusOfAllClauses(final Set<V> variablesIncorrectlySet, final V varToBeSetFalse) {
		// exclude the one variable which is going to be set to false soon
		final boolean wasInSet = variablesIncorrectlySet.remove(varToBeSetFalse);
		assert wasInSet;
		for (final V var : variablesIncorrectlySet) {
			undoAssignment(var);
			/*
			 * TODO some clauses are reevaluated several times
			 *      (if they contain several reset variables)
			 */
			reEvaluateStatusOfAllClauses(var);
		}
	}

	protected void reEvaluateStatusOfAllClauses(final V var) {
		for (final Clause<V> clause : mOccursPositive.getImage(var)) {
			reEvaluateClauseStatus(clause);
			if (mConjunctionEquivalentToFalse) {
				return;
			}
		}
		for (final Clause<V> clause : mOccursNegative.getImage(var)) {
			reEvaluateClauseStatus(clause);
			if (mConjunctionEquivalentToFalse) {
				return;
			}
		}
	}

	private void reEvaluateClauseStatus(final Clause<V> clause) {
		final boolean wasHorn = clause.isHorn();
		clause.updateClauseCondition(this);
		if (clause.isEquivalentToFalse()) {
			mConjunctionEquivalentToFalse = true;
		} else if (clause.isEquivalentToTrue()) {
			mClausesMarkedForRemoval.add(clause);
		} else if (clause.isPseudoUnit()) {
			final Pair<V, Boolean> propagatee = clause.getPropagatee();
			final Boolean oldVal = mPropagatees.put(propagatee.getFirst(), propagatee.getSecond());
			if ((oldVal != null) && (!oldVal.equals(propagatee.getSecond()))) {
				// The propagatee already existed with a different value.
				mConjunctionEquivalentToFalse = true;
			}
		} else if (wasHorn != clause.isHorn()) {
			if (wasHorn && !clause.isHorn()) {
				incrementNumberOfNonHornClauses();
			} else {
				decrementNumberOfNonHornClauses();
			}
		}
	}

	protected void incrementNumberOfNonHornClauses() {
		// do nothing in the general case
	}

	protected void decrementNumberOfNonHornClauses() {
		// do nothing in the general case
	}

	protected void undoAssignment(final V var) {
		// do nothing in the general case
	}

	protected abstract void decideOne();

	/**
	 * current policy: just return the next variable from the set.
	 * <p>
	 * TODO other policies, e.g., prefer non-Horn clauses
	 * 
	 * @return unset variable
	 */
	protected V getUnsetVariable() {
		final Iterator<V> it = mUnsetVariables.iterator();
		final V var = it.next();
		it.remove();
		return var;
	}

	protected void removeMarkedClauses() {
		for (final Clause<V> clause : mClausesMarkedForRemoval) {
			removeClause(clause);
		}
		mCurrentLiveClauses = mCurrentLiveClauses - mClausesMarkedForRemoval.size();
		mClausesMarkedForRemoval = new LinkedHashSet<>();
	}

	private void removeClause(final Clause<V> clause) {
		for (final V var : clause.mPositiveAtoms) {
			mOccursPositive.removePair(var, clause);
		}
		for (final V var : clause.mNegativeAtoms) {
			mOccursNegative.removePair(var, clause);
		}
	}

	protected boolean checkClausesConsistent() {
		boolean consistent = true;
		final Set<Clause<V>> allClauses = new HashSet<>();
		for (final Entry<V, Clause<V>> entry : mOccursPositive.entrySet()) {
			final Clause<V> clause = entry.getValue();
			allClauses.add(clause);
			final IClauseCondition condition = clause.computeClauseCondition(this);
			if (condition.getClauseStatus().equals(clause.getClauseStatus())) {
				consistent = false;
				assert consistent;
			}
		}
		for (final Entry<V, Clause<V>> entry : mOccursNegative.entrySet()) {
			final Clause<V> clause = entry.getValue();
			allClauses.add(clause);
			final IClauseCondition condition = clause.computeClauseCondition(this);
			if (condition.getClauseStatus().equals(clause.getClauseStatus())) {
				consistent = false;
				assert consistent;
			}

		}
		for (final Clause<V> clause : allClauses) {
			if (clause.isPseudoUnit()) {
				if (!mPropagatees.get(clause.getUnsetAtom(this))) {
					consistent = false;
					assert consistent;
				}
			}
			if (clause.getClauseStatus() == ClauseStatus.TRUE && (!mClausesMarkedForRemoval.contains(clause))) {
				consistent = false;
				assert consistent;
			}

		}
		for (final Clause<V> clause : mClausesMarkedForRemoval) {
			if (clause.getClauseStatus() != ClauseStatus.TRUE) {
				consistent = false;
				assert consistent;
			}
			if (!allClauses.contains(clause)) {
				consistent = false;
				assert consistent;
			}
		}
		if (allClauses.size() != mCurrentLiveClauses) {
			consistent = false;
			assert consistent;
		}
		return consistent;
	}

	private RunningTaskInfo getRunningTaskInfo() {
		return new RunningTaskInfo(this.getClass(), "Solving system of " + mClauses + " clauses.");
	}
}
