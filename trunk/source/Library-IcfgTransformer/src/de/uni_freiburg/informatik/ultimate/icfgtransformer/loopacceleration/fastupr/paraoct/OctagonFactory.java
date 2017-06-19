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
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Factory Class for creating OctagonConjunctions and OctagonTerms
 *
 * @author Jill Enke
 *
 */
public final class OctagonFactory {

	private OctagonFactory() {
	}

	public static OctTerm createOctTerm(Object value, TermVariable firstVar, boolean firstNegative,
			TermVariable secondVar, boolean secondNegative) {
		if (firstVar.equals(secondVar)) {
			if (firstNegative != secondNegative) {
				throw new IllegalArgumentException("Can't create a term of the form x - x <= c");
			}
			return createOneVarOctTerm(value, firstVar, firstNegative);
		}
		return createTwoVarOctTerm(value, firstVar, firstNegative, secondVar, secondNegative);
	}

	public static OctTerm createOneVarOctTerm(Object value, TermVariable firstVar, boolean firstNegative) {
		if (value instanceof ParametricOctValue) {
			return new ParametricOctTerm((ParametricOctValue) value, firstVar, firstNegative);
		} else if (value instanceof BigDecimal) {
			return new StandardOctTerm((BigDecimal) value, firstVar, firstNegative);
		}
		return null;
	}

	public static OctTerm createTwoVarOctTerm(Object value, TermVariable firstVar, boolean firstNegative,
			TermVariable secondVar, boolean secondNegative) {
		if (value instanceof ParametricOctValue) {
			return new ParametricOctTerm((ParametricOctValue) value, firstVar, firstNegative, secondVar,
					secondNegative);
		} else if (value instanceof BigDecimal) {
			return new StandardOctTerm((BigDecimal) value, firstVar, firstNegative, secondVar, secondNegative);
		}
		return null;
	}

	public static OctConjunction createConjunction(Collection<OctTerm> terms) {
		final OctConjunction result = new OctConjunction();
		return result;

	}

}
