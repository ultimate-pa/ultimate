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

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;

/**
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public abstract class ParametricOctagonTerm extends OctagonTerm {

	protected final TermVariable mParametricVar;
	protected final BigDecimal mSummand;
	protected final BigDecimal mIncrement;

	public ParametricOctagonTerm(final BigDecimal constant, final TermVariable parametricVar, final BigDecimal summant) {
		this(constant, parametricVar, summant, BigDecimal.ZERO);
	}

	public ParametricOctagonTerm(final BigDecimal constant, final TermVariable parametricVar, final BigDecimal summant, final BigDecimal inc) {
		super(constant);
		mParametricVar = parametricVar;
		mSummand = summant;
		mIncrement = inc;
	}

	@Override
	protected Term rightTerm(final Script script) {
		final Sort intSort = SmtSortUtils.getIntSort(script);
		final Term constTerm = (Rational.valueOf(mConstant.toBigInteger(), BigInteger.ONE)).toTerm(intSort);
		Term varTerm = mParametricVar;
		if (!mIncrement.equals(BigDecimal.ZERO)) {
			varTerm = script.term("+", mParametricVar,
					Rational.valueOf(mIncrement.toBigInteger(), BigInteger.ONE).toTerm(intSort));
		}
		final Term summandTerm = (Rational.valueOf(mSummand.toBigInteger(), BigInteger.ONE)).toTerm(intSort);
		return script.term("+", script.term("*", constTerm, varTerm), summandTerm);
	}

	@Override
	public String toString() {
		return " <= " + mConstant + " * " + (mIncrement.equals(BigDecimal.ZERO) ? mParametricVar.toString()
				: "(" + mParametricVar + " + " + mIncrement.toString() + ")") + " + " + mSummand.toString();
	}

}
