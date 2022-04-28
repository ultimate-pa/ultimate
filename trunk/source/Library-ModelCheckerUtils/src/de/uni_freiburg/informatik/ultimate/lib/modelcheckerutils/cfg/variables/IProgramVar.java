/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Variable of an {@link ICFG}. We follow the ideas of Boogie
 * {@link https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml178.pdf}
 * in an ICFG. There are mainly two scopes: global and local. For global
 * variables, we can use the "old" keyword to refer to the value of the variable
 * at the beginning of the procedure. In several settings we use copies of
 * global variables that represent the variable at the beginning of the
 * procedure. If the {@link IProgramVar#getProcedure()} method returns null the
 * variable is global. Only global variables can be "old variables".
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IProgramVar extends IProgramVarOrConst {

	/**
	 * Returns the procedure in which this variable was declared. If this a global
	 * variable, then null is returned.
	 */
	String getProcedure();

	boolean isOldvar();

	/**
	 *
	 * @return The {@link TermVariable} that represents this {@link IProgramVar} in
	 *         SMT terms
	 */
	TermVariable getTermVariable();

	/**
	 * @return The constant (0-ary ApplicationTerm) that represents this
	 *         {@link IProgramVar} in closed SMT terms.
	 */
	ApplicationTerm getDefaultConstant();

	/**
	 * Constant (0-ary ApplicationTerm) which represents this {@link IProgramVar} if
	 * it occurs as next state variable in closed SMT which describe a transition.
	 */
	ApplicationTerm getPrimedConstant();
}
