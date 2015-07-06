/*
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Model Checker Utils Library.
 *
 * The ULTIMATE Model Checker Utils Library is free software: you can 
 * redistribute it and/or modify it under the terms of the GNU Lesser General 
 * Public License as published by the Free Software Foundation, either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Model Checker Utils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty 
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Model Checker Utils Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Model Checker Utils Library, or any covered work, 
 * by linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE Model Checker Utils Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Interface for the construction of "fresh" TermVariables.
 * In mathematical logics a variable is called "fresh" if the variable has not
 * occurred in the same context.
 * TermVariables constructed by objects that implement this interface are 
 * guaranteed to have a name which is different form all other TermVariables 
 * constructed by this object. There is no guarantee that a similar variable
 * was not constructed with the same Script.
 * @author Matthias Heizmann
 *
 */
public interface IFreshTermVariableConstructor {

	/**
	 * @param name String that will occur as substring of the resulting 
	 * TermVariable.
	 * @param sort Sort of the resulting TermVariable.
	 * @return TermVariable whose name is different from the names
	 * of all other TermVariable that have been constructed by this object.
	 */
	public abstract TermVariable constructFreshTermVariable(String name,
			Sort sort);

}