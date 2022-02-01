/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseDpllLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Stores the information for ground propagations, i.e., the clause and the dawg for which the clause propagated the
 * DPLL literal.
 *
 * @author Jochen Hoenicke
 *
 */
public class GroundPropagationInfo {

	/**
	 * The clause literal whose clause, together with the prefix of the decide stack is responsible
	 * for the setting of this literal
	 */
	private final ClauseDpllLiteral mReasonUnitClauseLiteral;
	/**
	 * Instantiation for of the clause. The entries corresponding to variables used in the propagated literal must be
	 * set to null. The entries for other variables may be set to null, if the clause can be instantiated for all
	 * "uninteresting" terms, i.e., the corresponding letter in the Dawg is a complemented letter.
	 */
	private final DawgState<ApplicationTerm, Boolean> mReasonClauseDawg;

	private int mStackDepth;

	public GroundPropagationInfo(final ClauseDpllLiteral unitClauseLiteral,
			final DawgState<ApplicationTerm, Boolean> clauseDawg) {
		super();
		mReasonUnitClauseLiteral = unitClauseLiteral;
		mReasonClauseDawg = clauseDawg;
	}

	/**
	 * Returns the dawg that contains those groundings of the clause that was the reason for propagation of this literal, which
	 * correspond to the point where this dsl sets its predicate.
	 *  -- i.e. the dawg that was the preimage of the renameProjectAndSelect operation that yielded this dsl's dawg.
	 */
	public DawgState<ApplicationTerm, Boolean> getClauseDawg() {
		return mReasonClauseDawg;
	}

	/**
	 * Returns the unit clause that was the reason for setting this propagated decide stack literal.
	 * @return unit clause
	 */
	public ClauseDpllLiteral getReasonClauseLit() {
		return mReasonUnitClauseLiteral;
	}

	public int getStackDepth() {
		return mStackDepth;
	}

	public void setStackDepth(int stackDepth) {
		this.mStackDepth = stackDepth;
	}

	@Override
	public String toString() {
		return String.format("(DSPropDPLL: %s)", mReasonUnitClauseLiteral.getLiteral());
	}
}
