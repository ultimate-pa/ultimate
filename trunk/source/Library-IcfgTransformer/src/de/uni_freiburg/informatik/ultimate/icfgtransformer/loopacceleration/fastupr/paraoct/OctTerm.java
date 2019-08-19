/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public abstract class OctTerm {

	protected final TermVariable mFirstVar;
	protected final TermVariable mSecondVar;
	protected final boolean mFirstNegative;
	protected final boolean mSecondNegative;
	protected final Object mValue;

	public OctTerm(final Object value, final TermVariable firstVar, final boolean firstNegative, final TermVariable secondVar,
			final boolean secondNegative) {
		mValue = value;
		mFirstVar = firstVar;
		mFirstNegative = firstNegative;
		mSecondVar = secondVar;
		mSecondNegative = secondNegative;
	}

	public OctTerm(final Object value, final TermVariable firstVar, final boolean firstNegative) {
		mValue = value;
		mFirstVar = firstVar;
		mFirstNegative = firstNegative;
		mSecondVar = firstVar;
		mSecondNegative = firstNegative;
	}

	/**
	 * Converts the OctTerm to a Term
	 *
	 * @param script
	 *            Script to build Terms
	 * @return Fresh Term representing the OctTerm
	 */
	public Term toTerm(final Script script) {
		final Term leftTerm = leftTerm(script);
		final Term rightTerm = rightTerm(script);
		return script.term("<=", leftTerm, rightTerm);
	}

	protected Term leftTerm(final Script script) {
		if (isOneVar()) {
			return script.term("*", isFirstNegative() ? SmtUtils.constructIntValue(script, BigInteger.valueOf(-2))
					: SmtUtils.constructIntValue(script, BigInteger.valueOf(2)), mFirstVar);

		} else {
			return script.term("+", isFirstNegative() ? script.term("*", script.decimal("-1"), mFirstVar) : mFirstVar,
					isSecondNegative() ? script.term("*", script.decimal("-1"), mSecondVar) : mSecondVar);
		}
	}

	protected abstract Term rightTerm(Script script);

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (isOneVar()) {
			sb.append((isFirstNegative() ? "-" : "") + "2*" + mFirstVar.toString());
		} else {
			sb.append((isFirstNegative() ? "-" : "") + mFirstVar.toString() + " + " + (isSecondNegative() ? "-" : "")
					+ mSecondVar.toString());
		}
		sb.append(" <= ");
		sb.append(rightString());
		return sb.toString();
	}

	protected abstract String rightString();

	public abstract Object getValue();

	public boolean isOneVar() {
		return mFirstNegative == mSecondNegative && mFirstVar == mSecondVar;
	}

	public TermVariable getFirstVar() {
		return mFirstVar;
	}

	public TermVariable getSecondVar() {
		return mSecondVar;
	}

	public boolean isFirstNegative() {
		return mFirstNegative;
	}

	public boolean isSecondNegative() {
		return mSecondNegative;
	}
}
