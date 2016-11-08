/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.core.model.translation;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;

/**
 * Valuation for the counter example result class.
 *
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 02.01.2012
 */
public interface IValuation {
	/**
	 * This method returns the Variable Values for current position on the failure path. How this is done is in the
	 * responsibility of each ModelChecker, that have to implement this interface. <br />
	 * <br />
	 * The method returns a map which maps from the variable name to the values. The values are modeled as
	 * <code>Entry&lt;IBoogieType, List&lt;String&gt;&gt;</code>, where {@link IBoogieType} signals the type of the
	 * Variable (so <code>Integer</code>, <code>Double</code> or <code>Array&lt;Integer&gt;</code>) and the List
	 * represent the values of the single variable or the array. See also: {@link VariableValuesMap}.
	 *
	 * @param index
	 *            the current position on the failure path.
	 * @return the values as Strings for the variables.
	 */
	VariableValuesMap getValuesForFailurePathIndex(final int index);
}
