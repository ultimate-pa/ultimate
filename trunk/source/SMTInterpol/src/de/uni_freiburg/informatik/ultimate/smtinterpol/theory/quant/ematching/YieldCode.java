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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral;

/**
 * Code to add a new interesting substitution for a given literal, including the corresponding CCTerms.
 * 
 * @author Tanja Schindler
 */
public class YieldCode implements ICode {

	private final EMatching mEMatching;
	private final QuantLiteral mQuantLiteral;
	private final TermVariable[] mVarOrder;
	private final Map<TermVariable, Integer> mVarPos;
	private final Map<Term, Integer> mEquivCCTermPos;

	/**
	 * Generate a new Yield Code.
	 * 
	 * @param eMatching
	 *            the E-Matching engine.
	 * @param qLit
	 *            the quantified literal.
	 * @param varOrder
	 *            the order of the variables; the resulting substitution will be returned in this order.
	 * @param varPos
	 *            the position of the variable substitutions in the register.
	 * @param equivCCTermPos
	 *            the position of the equivalent CCTerms in the register.
	 */
	public YieldCode(final EMatching eMatching, final QuantLiteral qLit, final TermVariable[] varOrder,
			final Map<TermVariable, Integer> varPos, final Map<Term, Integer> equivCCTermPos) {
		mEMatching = eMatching;
		mQuantLiteral = qLit;
		mVarOrder = varOrder;
		mVarPos = varPos;
		mEquivCCTermPos = equivCCTermPos;
	}

	@Override
	public void execute(CCTerm[] register, final int decisionLevel) {
		final List<CCTerm> varSubs = new ArrayList<CCTerm>(mVarOrder.length);
		for (int i = 0; i < mVarOrder.length; i++) {
			if (mVarPos.containsKey(mVarOrder[i])) {
				varSubs.add(register[mVarPos.get(mVarOrder[i])]);
			} else {
				varSubs.add(null);
			}
		}
		final Map<Term, CCTerm> equivalentCCTerms = new HashMap<>();
		for (final Entry<Term, Integer> pos : mEquivCCTermPos.entrySet()) {
			equivalentCCTerms.put(pos.getKey(), register[pos.getValue()]);
		}
		mEMatching.addInterestingSubstitution(mQuantLiteral, varSubs, equivalentCCTerms, decisionLevel);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("yield(" + mQuantLiteral);
		for (final TermVariable var : mVarPos.keySet()) {
			sb.append(", " + var);
		}
		sb.append(")");
		return sb.toString();
	}

}
