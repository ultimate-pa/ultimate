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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Abstract MAX-SAT solver for propositional logic clauses.
 * 
 * @author Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 * @param <V> Kind of objects that are used as variables.
 */
public abstract class AMaxSatSolver<V> {
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
	 * A clause is a propagatee if it has exactly one unset literal and is not
	 * equivalent to true at the moment.
	 * 
	 * TODO Instead of storing the clauses, store the variables and respective value:
	 *      this is exactly what happens next in the implementation, might save
	 *      a lot of memory, and might detect inconsistencies earlier (if one
	 *      variable gets positive and negative value at the moment of storing).
	 */
	protected final Set<Clause<V>> mPropagatees = new HashSet<>();
	protected boolean mConjunctionEquivalentToFalse = false;
	protected Set<Clause<V>> mClausesMarkedForRemoval = new LinkedHashSet<>();
	
	protected final HashRelation<V, Clause<V>> mOccursPositive = new HashRelation<>();
	protected final HashRelation<V, Clause<V>> mOccursNegative = new HashRelation<>();
	
	protected int mDecisions = 0;
	protected int mWrongDecisions = 0;
	protected int mClauses = 0;
	/**
	 * A clause is trivial if we were able to evaluate it to true when it was
	 * added.
	 */
	protected int mTrivialClauses = 0;
	protected int mCurrentLiveClauses = 0;
	protected int mMaxLiveClauses = 0;
	
	
	/**
	 * @param services Ultimate services
	 */
	public AMaxSatSolver(final AutomataLibraryServices services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
	}
	
	/**
	 * Add a new variable. Variables have to be added before they can be
	 * used in clauses.
	 * 
	 * @param var variable
	 */
	public void addVariable(final V var) {
		final boolean modified = mVariables.add(var);
		if (!modified) {
			throw new IllegalArgumentException("variable already added " + var);
		}
		mUnsetVariables.add(var);
	}
	
	/**
	 * Add a new Horn clause. We call the variables on the left-hand side
	 * negativeAtoms and the variable on the right-hand side the positive
	 * atom. 
	 * @param negativeAtoms array of non-null variables
	 * @param positiveAtom variable that may be null. If the variable is null
	 *  it considered as true. If you want to assert only a negative atom, you
	 *  have to use null as positive Atom
	 * @deprecated This method is only present for legacy reasons and just
	 *  converts the Horn clause to a general clause in the general solver.
	 *  The caller should instead directly call the general
	 *  <code>addClause()</code> method.
	 *  For the old solver, this method is still needed.
	 */
	@Deprecated
	public abstract void addHornClause(final V[] negativeAtoms, final V positiveAtom);
	
	/**
	 * Add a new clause. We call the variables on the left-hand side
	 * negativeAtoms and the variables on the right-hand side the positive
	 * atoms. 
	 * @param negativeAtoms array of non-null variables considered negative
	 * @param positiveAtoms array of non-null variables considered positive.
	 *  If you want to assert only a negative atom, you have to use an empty
	 *  array as positive atoms.
	 */
	public abstract void addClause(final V[] negativeAtoms, final V[] positiveAtoms);
	
	/**
	 * Solve the given MAX-SAT problem for the given set of Horn clauses.
	 * @return true iff the given set of Horn clauses is satisfiable.
	 */
	public boolean solve() throws AutomataOperationCanceledException {
		mLogger.info("starting solver");
		propagateAll();
		makeModificationsPersistent();
		while(!mUnsetVariables.isEmpty()) {
			decideOne();
			if (mConjunctionEquivalentToFalse) {
				return false;
			}
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		makeModificationsPersistent();
		mLogger.info("finished solver");
		log();
		return true;
	}

	/**
	 * prints the log message
	 */
	protected abstract void log();
	
	/**
	 * @return The locally optimal satisfying assignment.
	 */
	public Map<V, Boolean> getValues() {
		return Collections.unmodifiableMap(mVariablesIrrevocablySet);
	}

	/**
	 * @param var variable
	 * @return The locally optimal satisfying assignment.
	 */
	public EVariableStatus getValue(final V var) {
		final Boolean value = getPersistentAssignment(var);
		if (value == null) {
			return EVariableStatus.UNSET;
		} else if (value) {
			return EVariableStatus.TRUE;
		} else {
			return EVariableStatus.FALSE;
		}
	}

	/**
	 * assignment to the variable which is guaranteed to not be backtracked
	 * 
	 * @param var variable
	 * @return <code>true</code>/<code>false</code> if assigned,
	 *         <code>null</code> otherwise
	 */
	protected abstract Boolean getPersistentAssignment(V var);

	/**
	 * assignment to the variable which is not guaranteed to not be backtracked
	 * 
	 * @param var variable
	 * @return <code>true</code>/<code>false</code> if assigned,
	 *         <code>null</code> otherwise
	 */
	protected abstract Boolean getTemporaryAssignment(V var);

	/**
	 * backtracking mechanism
	 * 
	 * @param var last set variable which lead to inconsistency
	 */
	protected abstract void backtrack(final V var);
	
	/**
	 * 
	 */
	protected abstract void makeModificationsPersistent();

	protected void propagateAll() {
		while (!mPropagatees.isEmpty() && !mConjunctionEquivalentToFalse) {
			propagateOne();
		}
	}
	
	private void propagateOne() {
		final Clause<V> clause = getPropagatee();
		final Pair<V, Boolean> unsetAtom = clause.getUnsetAtom(this);
		setVariable(unsetAtom.getFirst(), unsetAtom.getSecond());
	}

	/**
	 * current policy: just return the next clause from the set
	 * 
	 * TODO other policies
	 *      The only goal for optimization here is to find contradictions faster.
	 *      If no contradiction is found, all policies should take the same time.
	 *      One policy could be to prefer clauses with positive/negative
	 *      variable, but it is not clear whether this makes sense.
	 * 
	 * @return clause with only one unset variable
	 */
	private Clause<V> getPropagatee() {
		final Iterator<Clause<V>> it = mPropagatees.iterator();
		final Clause<V> clause = it.next();
//		Do not remove, we remove while updating clause, this will ease debugging
//		it.remove();
		return clause;
	}
	
	/**
	 * sets a status to a variable
	 * 
	 * @param var variable
	 * @param newStatus new status
	 */
	protected abstract void setVariable(final V var, final boolean newStatus);
	
	/**
	 * NOTE: must be called from backtracking, as we modify the set
	 * 
	 * @param variablesIncorrectlySet variables to be unset (modified here)
	 * @param varToBeSetFalse variable which is going to be set to false soon
	 */
	protected void reEvaluateStatusOfAllClauses(
			final Set<V> variablesIncorrectlySet,
			final V varToBeSetFalse) {
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
		// TODO improvement: interrupt if clause equivalent to false was found
		for (final Clause<V> clause : mOccursPositive.getImage(var)) {
			reEvaluateClauseStatus(clause);
		}
		for (final Clause<V> clause : mOccursNegative.getImage(var)) {
			reEvaluateClauseStatus(clause);
		}
	}

	private void reEvaluateClauseStatus(final Clause<V> clause) {
		final boolean wasPropagatee = clause.isPropagatee();
		clause.updateClauseCondition(this);
		if (clause.isEquivalentToFalse()) {
			mConjunctionEquivalentToFalse = true;
		} else if (clause.isEquivalentToTrue()) {
			mClausesMarkedForRemoval.add(clause);
		} else {
			if (clause.getUnsetAtoms() == 1) {
				assert clause.isPropagatee();
				mPropagatees.add(clause);
			} else {
				assert !clause.isPropagatee();
				assert clause.getUnsetAtoms() > 1;
			}
		}
		if (wasPropagatee && !clause.isPropagatee()) {
			final boolean removed = mPropagatees.remove(clause);
			assert removed : "clause was not there";
		} else {
			assert clause.getUnsetAtoms() == 1 ||
					!mPropagatees.contains(clause) : " clause illegal";
		}
	}

	protected void undoAssignment(final V var) {
		// do nothing in the general case
	}
	
	protected abstract void decideOne();

	/**
	 * current policy: just return the next variable from the set
	 * 
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
		mCurrentLiveClauses =
				mCurrentLiveClauses - mClausesMarkedForRemoval.size();
		mClausesMarkedForRemoval = new LinkedHashSet<>();
	}

	private void removeClause(final Clause<V> clause) {
		mPropagatees.remove(clause);
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
			final ClauseCondition condition = clause.computeClauseCondition(this);
			if (condition.getClauseStatus().equals(clause.getClauseCondition().getClauseStatus())) {
				consistent = false;
				assert consistent;
			}
		}
		for (final Entry<V, Clause<V>> entry : mOccursNegative.entrySet()) {
			final Clause<V> clause = entry.getValue();
			allClauses.add(clause);
			final ClauseCondition condition = clause.computeClauseCondition(this);
			if (condition.getClauseStatus().equals(clause.getClauseCondition().getClauseStatus())) {
				consistent = false;
				assert consistent;
			}
			
		}
		for (final Clause<V> clause : allClauses) {
			if (clause.isPropagatee() && !mPropagatees.contains(clause)) {
				consistent = false;
				assert consistent;
			}
			if (clause.getClauseCondition().getClauseStatus() == EClauseStatus.TRUE && 
					!mClausesMarkedForRemoval.contains(clause)) {
				consistent = false;
				assert consistent;
			}

		}
		for (final Clause<V> clause : mClausesMarkedForRemoval) {
			if (clause.getClauseCondition().getClauseStatus() != EClauseStatus.TRUE) {
				consistent = false;
				assert consistent;
			}
			if (!allClauses.contains(clause)) {
				consistent = false;
				assert consistent;
			}
		}
		for (final Clause<V> clause : mPropagatees) {
			if (!clause.isPropagatee()) {
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
}
