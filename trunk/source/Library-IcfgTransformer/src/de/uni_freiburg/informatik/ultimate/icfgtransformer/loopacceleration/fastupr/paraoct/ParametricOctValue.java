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

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class ParametricOctValue {

	private final BigDecimal mCoefficient;
	private final BigDecimal mSummand;
	private final TermVariable mVar;
	private final BigDecimal mIncrement;

	ParametricOctValue() {
		mCoefficient = new BigDecimal("0");
		mSummand = new BigDecimal("0");
		mVar = null;
		mIncrement = null;
	}

	ParametricOctValue(BigDecimal coefficient, BigDecimal summand, TermVariable parametricVar) {
		this(coefficient, summand, parametricVar, BigDecimal.ZERO);
	}

	ParametricOctValue(BigDecimal coefficient, BigDecimal summand, TermVariable parametricVar, BigDecimal increment) {
		mCoefficient = coefficient;
		mSummand = summand;
		mVar = parametricVar;
		mIncrement = increment;
	}

	BigDecimal getCoefficient() {
		return mCoefficient;
	}

	BigDecimal getSummand() {
		return mSummand;
	}

	TermVariable getVariable() {
		return mVar;
	}

	BigDecimal getIncrement() {
		return mIncrement;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder(mCoefficient.toString() + " * ");
		if (mIncrement.equals(BigDecimal.ZERO)) {
			sb.append(mVar.toString());
		} else {
			sb.append("(" + mVar.toString() + "+" + mIncrement.toString() + ")");
		}
		sb.append(" + " + mSummand.toString());
		return sb.toString();
	}

	public ParametricOctValue add(ParametricOctValue value) {
		return new ParametricOctValue(mCoefficient.add(value.getCoefficient()), mSummand.add(value.getSummand()), mVar,
				mIncrement);
	}

	public ParametricOctValue add(BigDecimal value) {
		return new ParametricOctValue(mCoefficient, mSummand.add(value), mVar, mIncrement);
	}

	public ParametricOctValue multipy(BigDecimal value) {
		return new ParametricOctValue(mCoefficient.multiply(value), mSummand.multiply(value), mVar, mIncrement);
	}

	public Object add(Object value) {
		if (value instanceof ParametricOctValue) {
			return add((ParametricOctValue) value);
		} else {
			return add((BigDecimal) value);
		}
	}

	public Term getTerm(Script script) {
		final Term inner = mIncrement.equals(BigDecimal.ZERO) ? mVar
				: script.term("+", mVar, script.decimal(mIncrement));
		final Term coeff = mCoefficient.equals(BigDecimal.ZERO) ? script.numeral(BigInteger.ZERO)
				: script.term("*", script.decimal(mCoefficient), inner);
		return mSummand.equals(BigDecimal.ZERO) ? coeff : script.term("+", coeff, script.decimal(mSummand));
	}
}
