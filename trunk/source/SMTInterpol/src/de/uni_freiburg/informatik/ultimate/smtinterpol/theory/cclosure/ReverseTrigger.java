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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;

/**
 * @author Tanja Schindler, Jochen Hoenicke
 */
public abstract class ReverseTrigger extends SimpleListable<ReverseTrigger> {
	/**
	 * Get the argument on which the reverse trigger is installed.
	 * 
	 * @return the argument term.
	 */
	public abstract CCTerm getArgument();

	/**
	 * Get the position in the function application where the argument should be.
	 * 
	 * @return the position (0 for first argument).
	 */
	public abstract int getArgPosition();

	public abstract FunctionSymbol getFunctionSymbol();

	public abstract void activate(final CCAppTerm appTerm);
}
