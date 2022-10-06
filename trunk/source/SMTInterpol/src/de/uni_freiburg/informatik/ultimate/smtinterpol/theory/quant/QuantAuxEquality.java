/*
 * Copyright (C) 2019-2021 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * An auxiliary equality atom of the form "({@pre @}AUXi ...) = true".
 *
 * @author Jochen Hoenicke
 */
public class QuantAuxEquality extends QuantEquality {

	private final Term mDefinition;

	public QuantAuxEquality(final Term lhs, final Term rhs, final Term definition) {
		super(lhs, rhs);
		mDefinition = definition;
	}

	/**
	 * Get the definition for this aux equality.
	 *
	 * @return the definition.
	 */
	public Term getDefinition() {
		return mDefinition;
	}
}
