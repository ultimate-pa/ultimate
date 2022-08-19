/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory.InstanceOrigin;

/**
 * An instance of a quantified clause that is not added to the DPLL engine so far. It is basically a list of literals.
 *
 * It contains information about the number of yet undefined literals. It also contains information to build proofs
 * later, i.e., the quantified clause and the substitution this instance comes from.
 *
 * @author Tanja Schindler
 *
 */
class InstClause {
	protected final QuantClause mQuantClause;
	protected final List<Term> mSubs;
	protected final List<Literal> mLits;
	protected int mNumUndefLits;
	protected InstanceOrigin mOrigin;
	private Term mInstClauseTerm;

	InstClause(final QuantClause qClause, final List<Term> subs, final List<Literal> lits,
			final int numUndefLits, final InstanceOrigin origin, final Term instClauseTerm) {
		mQuantClause = qClause;
		mSubs = subs;
		mLits = lits;
		mNumUndefLits = numUndefLits;
		mOrigin = origin;
		mInstClauseTerm = instClauseTerm;
	}

	@Override
	public int hashCode() {
		return mLits.hashCode();
	}

	@Override
	public boolean equals(final Object other) {
		if (other instanceof InstClause) {
			return mLits.equals(((InstClause) other).mLits);
		}
		return false;
	}

	@Override
	public String toString() {
		return mLits.toString();
	}

	boolean isConflict() {
		return mNumUndefLits == 0;
	}

	boolean isUnit() {
		return mNumUndefLits == 1;
	}

	/**
	 * Count the number of undef literals. If a true literal is contained, return -1.
	 */
	int countAndSetUndefLits() {
		int numUndef = 0;
		for (final Literal lit : mLits) {
			if (lit.getAtom().getDecideStatus() == lit) {
				mNumUndefLits = -1;
				return -1;
			}
			if (lit.getAtom().getDecideStatus() == null) {
				numUndef++;
			}
		}
		mNumUndefLits = numUndef;
		return numUndef;
	}

	/**
	 * Build a (DPLL) Clause from this InstClause. If proofs are enabled, this also sets the proof node.
	 *
	 * @param produceProofs
	 *            flag to determine if proofs have to be produced.
	 * @return a Clause consisting of the literals of this InstClause, including the proof if enabled.
	 */
	Clause toClause(final boolean produceProofs) {
		final Clause clause = new Clause(mLits.toArray(new Literal[mLits.size()]),
				mQuantClause.getQuantTheory().getEngine().getAssertionStackLevel());
		if (produceProofs) {
			clause.setProof(new LeafNode(LeafNode.QUANT_INST,
					new QuantAnnotation(mQuantClause, mSubs, mInstClauseTerm, mOrigin)));
		}
		return clause;
	}
}