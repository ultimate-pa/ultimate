/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * This class represents a clause.  It basically consists of an array
 * of literals.  There is also some additional informations like activity,
 * literal watchers, proof information and stacklevel for push/pop mechanism.
 * 
 * @author Jochen Hoenicke
 * 
 */
public class Clause extends SimpleListable<Clause> {
	Literal[] m_literals;
	
	/**
	 * The next watched clause on the watcher list.
	 * Each clause has two watchers.  The first watching lit 0, the next lit1.
	 * Their watchers form a linked list.  For memory efficiency reasons there 
	 * is no real data structure for watchers, but a clause and a bit is used
	 * to represent a watcher.
	 */
	Clause  nextFirstWatch, nextSecondWatch;
	/**
	 * A bitset telling if the next watcher for nextFirstWatch/nextSecondWatch
	 * is the first or second watcher in that clause.  Bit0 is 1, iff  the
	 * next watcher on the first list, which watches nextFirstWatch, is the
	 * second watcher of that clause.  Likewise Bit1 is 1, iff the next watcher
	 * on the second list is the second watcher of the clause nextSecondWatch.
	 */
	int     nextIsSecond;
	/**
	 * A WatchList is a list of watchers.
	 * Each clause has two watchers.  The first watching lit 0, the next lit1.
	 * Their watchers form a linked list.  For memory efficiency reasons there 
	 * is no real data structure for watchers, but a clause and a bit is used
	 * to represent a watcher.
	 */
	final static class WatchList {
		Clause m_Head;
		int    m_HeadIndex;
		Clause m_Tail;
		int    m_TailIndex;
		int    m_Size;
		
		public WatchList() {
			m_Head = m_Tail = null;
		}
		
		public boolean isEmpty() {
			return m_Head == null;
		}
		
		public int size() {
			return m_Size;
		}

		public void prepend(Clause c, int index) {
			if (m_Head == null) {
				m_Tail = c;
				m_TailIndex = index;
			} else {
				if (index == 0) {
					assert c.nextFirstWatch == null;
					c.nextFirstWatch = m_Head;
					c.nextIsSecond |= m_HeadIndex;
				} else {
					assert c.nextSecondWatch == null;
					c.nextSecondWatch = m_Head;
					c.nextIsSecond |= m_HeadIndex<<1;
				}
			}
			m_Head = c;
			m_HeadIndex = index;
			m_Size++;
		}

		public void append(Clause c, int index) {
			if (m_Head == null) {
				m_Head = c;
				m_HeadIndex = index;
			} else {
				Clause t = m_Tail;
				if (m_TailIndex == 0) {
					assert t.nextFirstWatch == null;
					t.nextFirstWatch = c;
					t.nextIsSecond |= index;
				} else {
					assert t.nextSecondWatch == null;
					t.nextSecondWatch = c;
					t.nextIsSecond |= index<<1;
				}
			}
			m_Tail = c;
			m_TailIndex = index;
			m_Size++;
		}

		public int getIndex() {
			return m_HeadIndex;
		}

		public Clause removeFirst() {
			Clause c = m_Head;
			if (m_HeadIndex == 0) {
				m_Head = c.nextFirstWatch;
				m_HeadIndex = c.nextIsSecond & 1;
				c.nextFirstWatch = null;
				c.nextIsSecond &= 2;
			} else {
				m_Head = c.nextSecondWatch;
				m_HeadIndex = (c.nextIsSecond & 2) >>1;
				c.nextSecondWatch = null;
				c.nextIsSecond &= 1;
			}
			if (m_Head == null) {
				m_Tail = null;
				m_TailIndex = 0;
			}
			m_Size--;
			return c;
		}

		public void moveAll(WatchList src) {
			if (src.m_Head == null)
				return;

			append(src.m_Head, src.m_HeadIndex);
			m_Size += src.m_Size-1;
			m_Tail = src.m_Tail;
			m_TailIndex = src.m_TailIndex;
			src.m_Head = null;
			src.m_HeadIndex = 0;
			src.m_Tail = null;
			src.m_TailIndex = 0;
			src.m_Size = 0;
		}
	}

	/**
	 * The activity of a clause. Infinity for clauses that are not inferred. If
	 * the activity drops below some point the clause is removed.
	 */
	double activity;
	int usedTimes;
	/**
	 * The stacklevel this clause was introduced.
	 */
	final int stacklevel;

	/**
	 * Proof annotation
	 */
	ProofNode proof;

	ClauseDeletionHook cleanupHook;
	
	private int hash = 0;

	public int getSize() {
		return m_literals.length;
	}

	public Literal getLiteral(int i) {
		return m_literals[i];
	}

	public Clause(Literal[] literals) {
		this.m_literals = literals;
		stacklevel = computeStackLevel();
	}

	public Clause(Literal[] literals, ProofNode proof) {
		this.m_literals = literals;
		this.proof = proof;
		stacklevel = computeStackLevel();
	}

	public Clause(Literal[] literals, int stacklevel) {
		this.m_literals = literals;
		this.stacklevel = Math.max(stacklevel, computeStackLevel());
	}

	public Clause(Literal[] literals, ResolutionNode proof, int stacklevel) {
		this.m_literals = literals;
		this.proof = proof;
		this.stacklevel = Math.max(stacklevel, computeStackLevel());
	}

	private final int computeStackLevel() {
		int sl = 0;
		for (Literal lit : m_literals)
			if (lit.getAtom().assertionstacklevel > sl)
				sl = lit.getAtom().assertionstacklevel;
		return sl;
	}

	public String toString() {
		return Arrays.toString(m_literals);
	}
	
	public String toSMTLIB(Theory smtTheory) {
		if (m_literals.length == 0)
			return "false";
		if (m_literals.length == 1)
			return m_literals[0].getSMTFormula(smtTheory, true).toString();
		StringBuilder sb = new StringBuilder("(or");
		for (Literal l : m_literals)
			sb.append(' ').append(l.getSMTFormula(smtTheory, true));
		sb.append(')');
		return sb.toString();
	}

	public void setActivityInfinite() {
		activity = Double.POSITIVE_INFINITY;
	}

	public boolean equals(Object o) {
		if (o instanceof Clause)
			return Arrays.equals(m_literals, ((Clause) o).m_literals);
		return false;
	}

	public void setProof(ProofNode proof) {
		this.proof = proof;
	}

	public ProofNode getProof() {
		return proof;
	}

	public void setDeletionHook(ClauseDeletionHook hook) {
		cleanupHook = hook;
	}

	public boolean doCleanup(DPLLEngine engine) {
		return cleanupHook != null ?
				cleanupHook.clauseDeleted(this, engine) : true;
	}

	/**
	 * Returns true, if the clause contains the literal with the same polarity.
	 * @param lit the literal it should contain.
	 * @return true, if the clause contains the literal with the same polarity.
	 */
	public boolean contains(Literal lit) {
		for (Literal l : m_literals) {
			if (l == lit)
				return true;
		}
		return false;
	}
	
	public int hashCode() {
		if (hash == 0) {
			hash = HashUtils.hashJenkins(0, (Object[]) m_literals);
			if (hash == 0)
				hash = 0xbadc0ded;
		}
		return hash;
	}
	
	public Term toTerm(Theory theory) {
		if (m_literals.length == 0)
			return theory.FALSE;
		if (m_literals.length == 1)
			return m_literals[0].getSMTFormula(theory, true);
		Term[] args = new Term[m_literals.length];
		for (int i = 0; i < m_literals.length; ++i) 
			args[i] = m_literals[i].getSMTFormula(theory, true);
		return theory.term("or", args);
	}
	
}