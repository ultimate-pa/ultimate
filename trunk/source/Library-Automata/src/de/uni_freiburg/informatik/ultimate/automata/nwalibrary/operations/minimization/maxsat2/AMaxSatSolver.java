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

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

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
	
	protected final Set<V> mVariables = new HashSet<V>();
	protected final Map<V, Boolean> mVariablesIrrevocablySet = new HashMap<V, Boolean>();
	protected Map<V, Boolean> mVariablesTemporarilySet = new HashMap<V, Boolean>();
	protected final Set<V> mUnsetVariables = new LinkedHashSet<V>();
	/**
	 * A clause is a propagatee if it has exactly one unset literal and is not
	 * equivalent to true at the moment.
	 */
	protected final LinkedHashSet<Clause<V>> mPropagatees = new LinkedHashSet<>();
	protected boolean mConjunctionEquivalentToFalse = false;
	protected LinkedHashSet<Clause<V>> mClausesMarkedForRemoval = new LinkedHashSet<>();
	
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
	 * used in Horn clauses.
	 * 
	 * @param var variable
	 */
	public abstract void addVariable(final V var);
	
	/**
	 * Add a new Horn clause. We call the variables on the left-hand side
	 * negativeAtoms and the variable on the right-hand side the positive
	 * atom. 
	 * @param negativeAtoms array of non-null variables
	 * @param positiveAtom variable that may be null. If the variable is null
	 * it considered as true. If you want to assert only a negative atom, you
	 * have to use null as positive Atom
	 * @deprecated This method is only present for legacy reasons and just
	 *  converts the Horn clause to a general clause. The caller should instead
	 *  directly call the general <code>addClause()</code> method.
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
	public abstract boolean solve() throws AutomataOperationCanceledException;
	
	/**
	 * @return The locally optimal satisfying assignment.
	 */
	public abstract Map<V, Boolean> getValues();

	/**
	 * @param var variable
	 * @return The locally optimal satisfying assignment.
	 */
	public EVariableStatus getValue(final V var) {
		final Boolean value = mVariablesIrrevocablySet.get(var);
		if (value == null) {
			return EVariableStatus.UNSET;
		} else if (value) {
			return EVariableStatus.TRUE;
		} else {
			return EVariableStatus.FALSE;
		}
	}

	protected boolean checkClausesConsistent() {
		boolean consistent = true;
		final Set<Clause<V>> allClauses = new HashSet<>();
		for (final Entry<V, Clause<V>> entry : mOccursPositive.entrySet()) {
			final Clause<V> clause = entry.getValue();
			allClauses.add(clause);
			final ClauseCondition condition = clause.computeClauseCondition(this);
			if (condition.getClauseStatus().equals(clause.getClauseCondition())) {
				consistent = false;
				assert consistent;
			}
		}
		for (final Entry<V, Clause<V>> entry : mOccursNegative.entrySet()) {
			final Clause<V> clause = entry.getValue();
			allClauses.add(clause);
			final ClauseCondition condition = clause.computeClauseCondition(this);
			if (condition.getClauseStatus().equals(clause.getClauseCondition())) {
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
