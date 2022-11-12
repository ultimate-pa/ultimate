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
 * A reverse trigger listens on the E-graph for a function application on a
 * CCTerm as n-th argument. It gets activated if a function application is
 * detected whose n-th argument equals the CCTerm. This can happen either,
 * because the function application was just created (by quantifiers or other
 * means), or because the n-th argument of the function application was merged
 * with the equivalence class of the CCTerm that this trigger is expecting.
 *
 * The trigger gets installed on the argument CC term and the congruence closure
 * calls this trigger. A trigger can be either called from createCCTerm or from
 * merge. In both cases the trigger shouldn't do much (e.g. it should never
 * create new terms), but just enqueue work for later.
 *
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

	/**
	 * Called by CClosure when a function is found whose argument is equal to the
	 * argument term.
	 *
	 * @param appTerm the found function application
	 * @param isFresh true, if the function was just created, false, if we were
	 *                activated due to an equality between trigger's argument term
	 *                and function argument.
	 */
	public abstract void activate(final CCAppTerm appTerm, final boolean isFresh);
}
