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

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class OneVarParaOctTerm extends ParametricOctagonTerm {

	private final TermVariable mFirstVar;
	private final boolean mFirstNegative;

	public OneVarParaOctTerm(BigDecimal constant, TermVariable var, boolean negative, TermVariable parametricVar,
			BigDecimal summant) {
		super(constant, parametricVar, summant);
		mFirstVar = var;
		mFirstNegative = negative;
	}

	public OneVarParaOctTerm(BigDecimal constant, TermVariable var, boolean negative, TermVariable parametricVar,
			BigDecimal summant, BigDecimal inc) {
		super(constant, parametricVar, summant, inc);
		mFirstVar = var;
		mFirstNegative = negative;
	}

	@Override
	public String toString() {
		return ((mFirstNegative ? "- " : "") + "2 * " + mFirstVar.toString() + super.toString());
	}

	@Override
	public TermVariable getFirstVar() {
		return mFirstVar;
	}

	@Override
	public TermVariable getSecondVar() {
		return mFirstVar;
	}

	@Override
	protected Term leftTerm(Script script) {
		return (mFirstNegative ? script.term("-", mFirstVar) : mFirstVar);
	}

	@Override
	public boolean isFirstNegative() {
		return mFirstNegative;
	}

	@Override
	public boolean isSecondNegative() {
		return mFirstNegative;
	}
}
