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

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ParametricOctTerm extends OctTerm {

	public ParametricOctTerm(ParametricOctValue value, TermVariable firstVar, boolean firstNegative) {
		super(value, firstVar, firstNegative);
	}

	public ParametricOctTerm(ParametricOctValue value, TermVariable firstVar, boolean firstNegative,
			TermVariable secondVar, boolean secondNegative) {
		super(value, firstVar, firstNegative, secondVar, secondNegative);
	}

	@Override
	protected Term rightTerm(Script script) {
		return getValue().getTerm(script);
	}

	@Override
	public ParametricOctValue getValue() {
		return (ParametricOctValue) mValue;
	}

	@Override
	protected String rightString() {
		return getValue().toString();
	}

}
