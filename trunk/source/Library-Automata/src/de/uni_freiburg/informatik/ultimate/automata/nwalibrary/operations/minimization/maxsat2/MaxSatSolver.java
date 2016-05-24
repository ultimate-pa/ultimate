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
	
	private final Map<V,VariableStatus> m_Variables = new HashMap<V,VariableStatus>();
	private final Set<V> m_UnsetVariables = new LinkedHashSet<V>();
	private final LinkedHashSet<Clause> m_ClausesWithOneUnsetVariable = new LinkedHashSet<>();
	
	private final HashRelation<V, Clause> m_OccursPositive = new HashRelation<>();
	private final HashRelation<V, Clause> m_OccursNegative = new HashRelation<>();
	private int m_Decisions = 0;
	private boolean m_ConjunctionEquivalentToFalse = false;
	private List<Clause> m_ClausesMarkedForRemoval = new ArrayList<>();
	private int m_WrongDecisions = 0;
	
	public void addVariable(V var) {
		VariableStatus oldValue = m_Variables.put(var, VariableStatus.UNSET);
		if (oldValue != null) {
			throw new IllegalArgumentException("variable already added " + var);
		}
		m_UnsetVariables.add(var);
	}
	
	public void addHornClause(V[] negativeAtoms, V positiveAtom) {
		final V[] positiveAtoms;
		if (positiveAtom == null) {
			positiveAtoms = (V[]) new Object[0];
		} else {
			positiveAtoms = (V[]) new Object[]{ positiveAtom };
		}
		final Clause clause = new Clause(positiveAtoms, negativeAtoms);
				
		if (m_Decisions > 0) {
			throw new UnsupportedOperationException("only legal before decisions were made");
		}
		if (clause.isEquivalentToTrue()) {
			// clause is true and can be ignored if we will never backtrack
		} else {
			if (clause.isEquivalentToFalse()) {
				m_ConjunctionEquivalentToFalse = true;
				throw new UnsupportedOperationException("clause set is equivalent to false");
			} else  {
				assert clause.getUnsetAtoms() > 0;
				for (V var :clause.getNegativeAtoms()) {
					m_OccursNegative.addPair(var, clause);
				}
				for (V var :clause.getPositiveAtoms()) {
					m_OccursPositive.addPair(var, clause);
				}
				if (clause.getUnsetAtoms() == 1) {
					m_ClausesWithOneUnsetVariable.add(clause);
				}
			}
		}
	}
	
	public void solve() {
		propagateAll();
		makeClauseRemovalPersistent();
		while(!m_UnsetVariables.isEmpty()) {
			decideOne();
			if (m_ConjunctionEquivalentToFalse == true) {
				throw new AssertionError("unsolvable");
			}
		}
	}
	
	
	
	public Map<V, VariableStatus> getValues() {
		return Collections.unmodifiableMap(m_Variables);
	}

	public void decideOne() {
		m_Decisions++;
		Iterator<V> it = m_UnsetVariables.iterator();
		V var = it.next();
		it.remove();
		setVariable(var, true, false);
		if (m_ConjunctionEquivalentToFalse) {
			backtrack(var);
			m_Variables.put(var, VariableStatus.FALSE);
		} else {
			propagateAll();
			if (m_ConjunctionEquivalentToFalse) {
				backtrack(var);
				m_Variables.put(var, VariableStatus.FALSE);
			} else {
				makeClauseRemovalPersistent();
			}

		}
	}
	
	private void makeClauseRemovalPersistent() {
		removeClauses(m_ClausesMarkedForRemoval);
		m_ClausesMarkedForRemoval = new ArrayList<>();
	}

	private void backtrack(V var) {
		m_WrongDecisions ++;
		m_ClausesMarkedForRemoval = new ArrayList<>();
		m_ConjunctionEquivalentToFalse = false;
		setVariable(var, false, true);
		assert (m_ConjunctionEquivalentToFalse == false) : "resetting variable did not help";
	}

	public void propagateAll() {
		while (!m_ClausesWithOneUnsetVariable.isEmpty() && !m_ConjunctionEquivalentToFalse) {
			propagateOne();
		}
	}
	
	public void propagateOne() {
		final Iterator<MaxSatSolver<V>.Clause> it = m_ClausesWithOneUnsetVariable.iterator();
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
		final VariableStatus oldStatus = m_Variables.put(var, newStatus);
		if (oldStatus == null) {
			throw new IllegalArgumentException("unknown variable " + var);
		} else if (oldStatus != VariableStatus.UNSET) {
			if (oldStatus == VariableStatus.TRUE && isReset && !b) {
				// do not throw exception - resetting is legal
			} else {
				throw new IllegalArgumentException("variable already set " + var);
			}
		}
		m_UnsetVariables.remove(var);
		for (Clause clause : m_OccursPositive.getImage(var)) {
			clause.updateClauseStatus();
			if (clause.isEquivalentToFalse()) {
				m_ConjunctionEquivalentToFalse = true;
			} else if (clause.isEquivalentToTrue()) {
				m_ClausesMarkedForRemoval.add(clause);
				m_ClausesWithOneUnsetVariable.remove(clause);
			} else {
				if (clause.getUnsetAtoms() == 1) {
					m_ClausesWithOneUnsetVariable.add(clause);
				} else {
					assert clause.getUnsetAtoms() > 1;
				}
			}
		}
		for (Clause clause : m_OccursNegative.getImage(var)) {
			clause.updateClauseStatus();
			if (clause.isEquivalentToFalse()) {
				m_ConjunctionEquivalentToFalse = true;
			} else if (clause.isEquivalentToTrue()) {
				m_ClausesMarkedForRemoval.add(clause);
				m_ClausesWithOneUnsetVariable.remove(clause);
			} else {
				if (clause.getUnsetAtoms() == 1) {
					m_ClausesWithOneUnsetVariable.add(clause);
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
		m_ClausesWithOneUnsetVariable.remove(clause);
		for (V var : clause.m_PositiveAtoms) {
			m_OccursPositive.removePair(var, clause);
		}
		for (V var : clause.m_NegativeAtoms) {
			m_OccursNegative.removePair(var, clause);
		}

	}
	
	public enum VariableStatus { UNSET, TRUE, FALSE }
	
	enum ClauseStatus { TRUE, FALSE, NEITHER }
	
	private class Clause {
		private final V[] m_PositiveAtoms;
		private final V[] m_NegativeAtoms;
		private ClauseStatus m_ClauseStatus;
		private int m_UnsetAtoms;
		
		public Clause(V[] positiveAtoms, V[] negativeAtoms) {
			super();
			m_PositiveAtoms = positiveAtoms;
			m_NegativeAtoms = negativeAtoms;
			updateClauseStatus();
		}
		
		/**
		 * TODO: do update only for newly changed variable
		 */
		public void updateClauseStatus() {
			m_ClauseStatus = ClauseStatus.NEITHER;
			m_UnsetAtoms = 0;
			for (V var : m_PositiveAtoms) {
				VariableStatus status = m_Variables.get(var);
				switch (status) {
				case FALSE:
					// do nothing
					break;
				case TRUE:
					m_ClauseStatus = ClauseStatus.TRUE;
					break;
				case UNSET:
					m_UnsetAtoms++;
					break;
				default:
					throw new AssertionError();
				}
			}
			for (V var : m_NegativeAtoms) {
				VariableStatus status = m_Variables.get(var);
				switch (status) {
				case FALSE:
					m_ClauseStatus = ClauseStatus.TRUE;
					break;
				case TRUE:
					// do nothing
					break;
				case UNSET:
					m_UnsetAtoms++;
					break;
				default:
					throw new AssertionError();
				}
			}
			assert m_UnsetAtoms >= 0 && m_UnsetAtoms <= m_PositiveAtoms.length + m_NegativeAtoms.length;
			if (m_UnsetAtoms == 0 && m_ClauseStatus != ClauseStatus.TRUE) {
				m_ClauseStatus = ClauseStatus.FALSE;
			}
		}
		
		public boolean isEquivalentToFalse() {
			return m_ClauseStatus == ClauseStatus.FALSE;
		}
		
		public boolean isEquivalentToTrue() {
			return m_ClauseStatus == ClauseStatus.TRUE;
		}
		
		public int getUnsetAtoms() {
			return m_UnsetAtoms;
		}

		public V[] getPositiveAtoms() {
			return m_PositiveAtoms;
		}

		public V[] getNegativeAtoms() {
			return m_NegativeAtoms;
		}
		
		public Pair<V,Boolean> getUnsetAtom() {
			if (m_UnsetAtoms != 1) {
				throw new IllegalArgumentException("not only one unset Atom");
			} else {
				for (V var : m_PositiveAtoms) {
					VariableStatus status = m_Variables.get(var);
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
				for (V var : m_NegativeAtoms) {
					VariableStatus status = m_Variables.get(var);
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
			Iterator<V> it = Arrays.asList(m_NegativeAtoms).iterator();
			while(it.hasNext()) {
				sb.append(it.next());
				if (it.hasNext()) {
					sb.append(" /\\ ");
				}
			}
			if (m_NegativeAtoms.length > 0 && m_PositiveAtoms.length > 0) {
				sb.append(" --> ");
			}
			if (m_PositiveAtoms.length == 0) {
				// do nothing
			} else if (m_PositiveAtoms.length == 1) {
				sb.append(m_PositiveAtoms[0]);
			} else {
				throw new UnsupportedOperationException(
						"more than one positive literal is not supported at the moment");
			}
			return sb.toString();
		}
		
		

	}
	
}
