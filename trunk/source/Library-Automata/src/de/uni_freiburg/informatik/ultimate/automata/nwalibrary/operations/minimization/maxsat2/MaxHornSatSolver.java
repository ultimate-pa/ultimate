/*
 * Copyright (C) 2016 Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * MAX-SAT solver for Horn clauses.
 * The satisfying assignment returned by this solver is a locally optimal 
 * solution in the following sense. If you replace one false-assignment to
 * a variable by a true-assignment then the resulting mapping is not a valid
 * assignment any more.
 * There is no guarantee that this locally optimal solution does not have to
 * be a globally optimal solution (which is a solution in which the number
 * of true-assigned variables is maximal).  
 * @author Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * @param <V> Kind of objects that are used as variables.
 */
public class MaxHornSatSolver<V> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	
	private final Map<V,VariableStatus> mVariables = new HashMap<V,VariableStatus>();
	private final Set<V> mUnsetVariables = new LinkedHashSet<V>();
	private final LinkedHashSet<Clause> mClausesWithOneUnsetVariable = new LinkedHashSet<>();
	private boolean mConjunctionEquivalentToFalse = false;
	private List<Clause> mClausesMarkedForRemoval = new ArrayList<>();
	
	private final HashRelation<V, Clause> mOccursPositive = new HashRelation<>();
	private final HashRelation<V, Clause> mOccursNegative = new HashRelation<>();
	private int mDecisions = 0;
	
	private int mWrongDecisions = 0;
	private int mClauses = 0;
	/**
	 * A clause is trivial if we were able to evaluate it to true when it 
	 * was added.
	 */
	private int mTrivialClauses = 0;
	private int mCurrentLiveClauses = 0;
	private int mMaxLiveClauses = 0;
	
	
	
	public MaxHornSatSolver(AutomataLibraryServices services) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
	}

	/**
	 * Add a new variable. Variables have to be added before they can be
	 * used in Horn clauses.
	 */
	public void addVariable(V var) {
		final VariableStatus oldValue = mVariables.put(var, VariableStatus.UNSET);
		if (oldValue != null) {
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
	 * it considered as true. If you want to assert only a negative atom, you
	 * have to use null as positive Atom
	 */
	public void addHornClause(V[] negativeAtoms, V positiveAtom) {
		final V[] positiveAtoms;
		if (positiveAtom == null) {
			positiveAtoms = (V[]) new Object[0];
		} else {
			positiveAtoms = (V[]) new Object[]{ positiveAtom };
		}
		final Clause clause = new Clause(positiveAtoms, negativeAtoms);
				
		if (mDecisions > 0) {
			throw new UnsupportedOperationException("only legal before decisions were made");
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
			} else  {
				assert clause.getUnsetAtoms() > 0;
				for (final V var :clause.getNegativeAtoms()) {
					mOccursNegative.addPair(var, clause);
				}
				for (final V var :clause.getPositiveAtoms()) {
					mOccursPositive.addPair(var, clause);
				}
				if (clause.getUnsetAtoms() == 1) {
					mClausesWithOneUnsetVariable.add(clause);
				}
			}
			propagateAll();
		}
	}
	
	/**
	 * Solve the given MAX-SAT problem for the given set of Horn clauses.
	 * @return true iff the given set of Horn clauses is satisfiable.
	 */
	public boolean solve() throws AutomataOperationCanceledException {
		propagateAll();
		makeClauseRemovalPersistent();
		while(!mUnsetVariables.isEmpty()) {
			decideOne();
			if (mConjunctionEquivalentToFalse == true) {
				return false;
			}
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("Clauses: ").append(mClauses);
		sb.append(" (thereof " + mTrivialClauses + " trivial clauses)");
		sb.append(" MaxLiveClauses: ").append(mMaxLiveClauses);
		sb.append(" Decisions : ").append(mDecisions);
		sb.append(" (thereof " + mWrongDecisions + " wrong decisions)");
		mLogger.info(sb.toString());
		return true;
	}
	
	
	/**
	 * @return The locally optimal satisfying assignment.
	 */
	public Map<V, VariableStatus> getValues() {
		return Collections.unmodifiableMap(mVariables);
	}

	private void decideOne() {
		mDecisions++;
		final Iterator<V> it = mUnsetVariables.iterator();
		final V var = it.next();
		it.remove();
		setVariable(var, true, false);
		if (mConjunctionEquivalentToFalse) {
			backtrack(var);
			mVariables.put(var, VariableStatus.FALSE);
		} else {
			propagateAll();
			if (mConjunctionEquivalentToFalse) {
				backtrack(var);
				mVariables.put(var, VariableStatus.FALSE);
			} else {
				makeClauseRemovalPersistent();
			}

		}
	}
	
	private void makeClauseRemovalPersistent() {
		removeClauses(mClausesMarkedForRemoval);
		mClausesMarkedForRemoval = new ArrayList<>();
	}

	private void backtrack(V var) {
		mWrongDecisions ++;
		mClausesMarkedForRemoval = new ArrayList<>();
		mConjunctionEquivalentToFalse = false;
		setVariable(var, false, true);
		assert (mConjunctionEquivalentToFalse == false) : "resetting variable did not help";
	}

	private void propagateAll() {
		while (!mClausesWithOneUnsetVariable.isEmpty() && !mConjunctionEquivalentToFalse) {
			propagateOne();
		}
	}
	
	private void propagateOne() {
		final Iterator<MaxHornSatSolver<V>.Clause> it = mClausesWithOneUnsetVariable.iterator();
		final Clause clause = it.next();
		it.remove();
		final Pair<V, Boolean> unsetAtom = clause.getUnsetAtom();
		setVariable(unsetAtom.getFirst(), unsetAtom.getSecond(), false);
	}
	
	private void setVariable(V var, boolean b, boolean isReset) {
		final VariableStatus newStatus;
		if (b) {
			newStatus = VariableStatus.TRUE;
		} else {
			newStatus = VariableStatus.FALSE;
		}
		final VariableStatus oldStatus = mVariables.put(var, newStatus);
		if (oldStatus == null) {
			throw new IllegalArgumentException("unknown variable " + var);
		} else if (oldStatus != VariableStatus.UNSET) {
			if (oldStatus == VariableStatus.TRUE && isReset && !b) {
				// do not throw exception - resetting is legal
			} else {
				throw new IllegalArgumentException("variable already set " + var);
			}
		}
		mUnsetVariables.remove(var);
		for (final Clause clause : mOccursPositive.getImage(var)) {
			clause.updateClauseStatus();
			if (clause.isEquivalentToFalse()) {
				mConjunctionEquivalentToFalse = true;
			} else if (clause.isEquivalentToTrue()) {
				mClausesMarkedForRemoval.add(clause);
				mClausesWithOneUnsetVariable.remove(clause);
			} else {
				if (clause.getUnsetAtoms() == 1) {
					mClausesWithOneUnsetVariable.add(clause);
				} else {
					assert clause.getUnsetAtoms() > 1;
				}
			}
		}
		for (final Clause clause : mOccursNegative.getImage(var)) {
			clause.updateClauseStatus();
			if (clause.isEquivalentToFalse()) {
				mConjunctionEquivalentToFalse = true;
			} else if (clause.isEquivalentToTrue()) {
				mClausesMarkedForRemoval.add(clause);
				mClausesWithOneUnsetVariable.remove(clause);
			} else {
				if (clause.getUnsetAtoms() == 1) {
					mClausesWithOneUnsetVariable.add(clause);
				} else {
					assert clause.getUnsetAtoms() > 1;
				}
			}
		}
	}
	
	public void removeClauses(Collection<Clause> clauses) {
		for (final Clause clause : clauses) {
			removeClause(clause);
		}
		mCurrentLiveClauses = mCurrentLiveClauses - clauses.size();
	}
	

	public void removeClause(Clause clause) {
		mClausesWithOneUnsetVariable.remove(clause);
		for (final V var : clause.mPositiveAtoms) {
			mOccursPositive.removePair(var, clause);
		}
		for (final V var : clause.mNegativeAtoms) {
			mOccursNegative.removePair(var, clause);
		}

	}
	
	public enum VariableStatus { UNSET, TRUE, FALSE }
	
	enum ClauseStatus { TRUE, FALSE, NEITHER }
	
	/**
	 * Clause used by the MAX-SAT solver. Although there is only one
	 * positive atom in Horn clauses, this class allows one to use
	 * several positive atoms.
	 */
	private class Clause {
		private final V[] mPositiveAtoms;
		private final V[] mNegativeAtoms;
		private ClauseStatus mClauseStatus;
		private int mUnsetAtoms;
		
		public Clause(V[] positiveAtoms, V[] negativeAtoms) {
			super();
			mPositiveAtoms = positiveAtoms;
			mNegativeAtoms = negativeAtoms;
			updateClauseStatus();
		}
		
		/**
		 * TODO: do update only for newly changed variable
		 */
		public void updateClauseStatus() {
			mClauseStatus = ClauseStatus.NEITHER;
			mUnsetAtoms = 0;
			for (final V var : mPositiveAtoms) {
				final VariableStatus status = mVariables.get(var);
				switch (status) {
				case FALSE:
					// do nothing
					break;
				case TRUE:
					mClauseStatus = ClauseStatus.TRUE;
					break;
				case UNSET:
					mUnsetAtoms++;
					break;
				default:
					throw new AssertionError();
				}
			}
			for (final V var : mNegativeAtoms) {
				final VariableStatus status = mVariables.get(var);
				switch (status) {
				case FALSE:
					mClauseStatus = ClauseStatus.TRUE;
					break;
				case TRUE:
					// do nothing
					break;
				case UNSET:
					mUnsetAtoms++;
					break;
				default:
					throw new AssertionError();
				}
			}
			assert mUnsetAtoms >= 0 && mUnsetAtoms <= mPositiveAtoms.length + mNegativeAtoms.length;
			if (mUnsetAtoms == 0 && mClauseStatus != ClauseStatus.TRUE) {
				mClauseStatus = ClauseStatus.FALSE;
			}
		}
		
		public boolean isEquivalentToFalse() {
			return mClauseStatus == ClauseStatus.FALSE;
		}
		
		public boolean isEquivalentToTrue() {
			return mClauseStatus == ClauseStatus.TRUE;
		}
		
		public int getUnsetAtoms() {
			return mUnsetAtoms;
		}

		public V[] getPositiveAtoms() {
			return mPositiveAtoms;
		}

		public V[] getNegativeAtoms() {
			return mNegativeAtoms;
		}
		
		public Pair<V,Boolean> getUnsetAtom() {
			if (mUnsetAtoms != 1) {
				throw new IllegalArgumentException("not only one unset Atom");
			} else {
				for (final V var : mPositiveAtoms) {
					final VariableStatus status = mVariables.get(var);
					switch (status) {
					case TRUE:
					case FALSE:
						// do nothing
						break;
					case UNSET:
						return new Pair<V, Boolean>(var, true);
					default:
						throw new AssertionError();
					}
				}
				for (final V var : mNegativeAtoms) {
					final VariableStatus status = mVariables.get(var);
					switch (status) {
					case TRUE:
					case FALSE:
						// do nothing
						break;
					case UNSET:
						return new Pair<V, Boolean>(var, false);
					default:
						throw new AssertionError();
					}
				}
				throw new AssertionError("did not find unset atom");
			}
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			final Iterator<V> it = Arrays.asList(mNegativeAtoms).iterator();
			while(it.hasNext()) {
				sb.append(it.next());
				if (it.hasNext()) {
					sb.append(" /\\ ");
				}
			}
			if (mNegativeAtoms.length > 0 && mPositiveAtoms.length > 0) {
				sb.append(" --> ");
			}
			if (mPositiveAtoms.length == 0) {
				// do nothing
			} else if (mPositiveAtoms.length == 1) {
				sb.append(mPositiveAtoms[0]);
			} else {
				throw new UnsupportedOperationException(
						"more than one positive literal is not supported at the moment");
			}
			return sb.toString();
		}
		
		

	}
	
}
