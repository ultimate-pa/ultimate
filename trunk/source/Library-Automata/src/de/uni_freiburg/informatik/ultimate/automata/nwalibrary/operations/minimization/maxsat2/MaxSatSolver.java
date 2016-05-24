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

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.relation.HashRelation;

public class MaxSatSolver<V> {
	
	private final Map<V,VariableStatus> mVariables = new HashMap<V,VariableStatus>();
	private final Set<V> mUnsetVariables = new LinkedHashSet<V>();
	private final LinkedHashSet<Clause> mClausesWithOneUnsetVariable = new LinkedHashSet<>();
	
	private final HashRelation<V, Clause> mOccursPositive = new HashRelation<>();
	private final HashRelation<V, Clause> mOccursNegative = new HashRelation<>();
	private int mDecisions = 0;
	private boolean mConjunctionEquivalentToFalse = false;
	private List<Clause> mClausesMarkedForRemoval = new ArrayList<>();
	private int mWrongDecisions = 0;
	
	public void addVariable(V var) {
		VariableStatus oldValue = mVariables.put(var, VariableStatus.UNSET);
		if (oldValue != null) {
			throw new IllegalArgumentException("variable already added " + var);
		}
		mUnsetVariables.add(var);
	}
	
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
			// clause is true and can be ignored if we will never backtrack
		} else {
			if (clause.isEquivalentToFalse()) {
				mConjunctionEquivalentToFalse = true;
				throw new UnsupportedOperationException("clause set is equivalent to false");
			} else  {
				assert clause.getUnsetAtoms() > 0;
				for (V var :clause.getNegativeAtoms()) {
					mOccursNegative.addPair(var, clause);
				}
				for (V var :clause.getPositiveAtoms()) {
					mOccursPositive.addPair(var, clause);
				}
				if (clause.getUnsetAtoms() == 1) {
					mClausesWithOneUnsetVariable.add(clause);
				}
			}
		}
	}
	
	public void solve() {
		propagateAll();
		makeClauseRemovalPersistent();
		while(!mUnsetVariables.isEmpty()) {
			decideOne();
			if (mConjunctionEquivalentToFalse == true) {
				throw new AssertionError("unsolvable");
			}
		}
	}
	
	
	
	public Map<V, VariableStatus> getValues() {
		return Collections.unmodifiableMap(mVariables);
	}

	public void decideOne() {
		mDecisions++;
		Iterator<V> it = mUnsetVariables.iterator();
		V var = it.next();
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

	public void propagateAll() {
		while (!mClausesWithOneUnsetVariable.isEmpty() && !mConjunctionEquivalentToFalse) {
			propagateOne();
		}
	}
	
	public void propagateOne() {
		final Iterator<MaxSatSolver<V>.Clause> it = mClausesWithOneUnsetVariable.iterator();
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
		for (Clause clause : mOccursPositive.getImage(var)) {
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
		for (Clause clause : mOccursNegative.getImage(var)) {
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
		for (Clause clause : clauses) {
			removeClause(clause);
		}
	}
	

	public void removeClause(Clause clause) {
		mClausesWithOneUnsetVariable.remove(clause);
		for (V var : clause.mPositiveAtoms) {
			mOccursPositive.removePair(var, clause);
		}
		for (V var : clause.mNegativeAtoms) {
			mOccursNegative.removePair(var, clause);
		}

	}
	
	public enum VariableStatus { UNSET, TRUE, FALSE }
	
	enum ClauseStatus { TRUE, FALSE, NEITHER }
	
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
			for (V var : mPositiveAtoms) {
				VariableStatus status = mVariables.get(var);
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
			for (V var : mNegativeAtoms) {
				VariableStatus status = mVariables.get(var);
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
				for (V var : mPositiveAtoms) {
					VariableStatus status = mVariables.get(var);
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
				for (V var : mNegativeAtoms) {
					VariableStatus status = mVariables.get(var);
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
			Iterator<V> it = Arrays.asList(mNegativeAtoms).iterator();
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
