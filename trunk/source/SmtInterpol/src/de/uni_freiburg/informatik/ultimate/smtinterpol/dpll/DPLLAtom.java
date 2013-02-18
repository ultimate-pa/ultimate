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

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;


public abstract class DPLLAtom extends Literal {
	
	public static class TrueAtom extends DPLLAtom {

		public TrueAtom() {
			super(0, 0);
			decideStatus = this;
			decideLevel = 0;
		}

		@Override
		public Term getSMTFormula(Theory smtTheory, boolean quoted) {
			return smtTheory.TRUE;
		}
		
	}
	
	public static class NegLiteral extends Literal {
		public NegLiteral(DPLLAtom atom) {
			super(~atom.hashCode());//TODO is bit-flipping a good hash??? 
			this.atom = atom;
			this.negated = atom;
		}
		public int getSign() {
			return -1;
		}
		public String toString() {
			return atom.toStringNegated();
		}
		public Term getSMTFormula(Theory smtTheory, boolean quoted) {
			return atom.getNegatedSMTFormula(smtTheory, quoted);
		}
	}
	

	int decideLevel = -1;
	int stackPosition = -1;
	Literal decideStatus;
	Literal lastStatus;
	double  activity;
	public Object  explanation;
	Clause.WatchList backtrackWatchers = new Clause.WatchList();
	int m_atomQueueIndex = -1;
	final int assertionstacklevel;
	
	public DPLLAtom(int hash, int assertionstacklevel) {
		super(hash);
		this.atom = this;
		this.negated = new NegLiteral(this);
		this.assertionstacklevel = assertionstacklevel;
		lastStatus = negated;
	}
	
	/**
	 * Compares two atoms with respect to their activity. Do not override!
	 */
	public final int compareActivityTo(DPLLAtom other) {
		return activity < other.activity ? 1
				: activity == other.activity ? 0 : -1;
	}

	/**
	 * Returns 1, since an atom is always positive.
	 */
	public int getSign() {
		return 1;
	}
	
	public final int getDecideLevel() { 
		return decideLevel;
	}

	public final int getStackPosition() { 
		return stackPosition;
	}

	/**
	 * Returns a string representation of the negated atoms.
	 * Subclasses may overwrite this for pretty output.
	 */
	public String toStringNegated() {
		return "!("+toString()+")";
	}
	
	/**
	 * Returns a SMT formula representing the negated atoms.
	 * Subclasses may overwrite this for pretty output.
	 */
	public final Term getNegatedSMTFormula(Theory smtTheory, boolean useAuxVars) {
		return smtTheory.not(getSMTFormula(smtTheory, useAuxVars));
	}

	/**
	 * Returns the status of an atom:
	 * null if atom is undecided,
	 * atom if atom should be true,
	 * atom.negate() if atom should be false.
	 */
	public Literal getDecideStatus() {
		return decideStatus;
	}

	public int getAssertionStackLevel() {
		return assertionstacklevel;
	}

	public void setPreferredStatus(Literal status) {
		lastStatus = status;
//		activity += 1.0;
	}
	
	public Literal getPreferredStatus() {
		return lastStatus;
	}
}
