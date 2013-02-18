/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * An executable term is a term that can be used by a model to evaluate a
 * formula.
 * @author Juergen Christ
 */
public interface ExecTerm {
	/**
	 * Evaluate the application of some arguments to the function represented by
	 * this executable term.
	 * @param args Arguments to apply to the function represented by this term.
	 * @return Result of the evaluation or <code>null</code> if the default
	 *         value should be used.
	 */
	Term evaluate(Term... args);
	/**
	 * Transform this executable term into SMTLIB format.  For function symbols,
	 * variables {@code @0} to {@code @n-1} are introduced (where {@code n} is
	 * arity of the function).
	 * @param t    Theory to use to create formulas.
	 * @param vars Positional variables of the term.
	 * @return SMTLIB representation of this term.
	 */
	Term toSMTLIB(Theory t, TermVariable[] vars);
}
