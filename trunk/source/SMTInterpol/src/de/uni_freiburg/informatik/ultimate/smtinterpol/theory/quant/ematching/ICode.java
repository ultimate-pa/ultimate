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

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;

/**
 * This represents a piece of code for E-matching which can be executed for a register containing candidate terms and a
 * decision level depending on those candidate terms.
 * 
 * @author Tanja Schindler
 */
public interface ICode {

	/**
	 * Execute this piece of code with the given register.
	 * 
	 * @param register
	 *            the relevant CCTerms for this execution.
	 * @param decisionLevel
	 *            the relevant decisionLevel for this execution.
	 */
	public void execute(final CCTerm[] register, final int decisionLevel);
}
