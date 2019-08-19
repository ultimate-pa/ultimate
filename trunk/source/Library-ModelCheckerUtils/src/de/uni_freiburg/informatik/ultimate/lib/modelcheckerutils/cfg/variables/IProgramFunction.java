/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;


/**
 * Represents an function in the program.
 * Note that we use the notion of Boogie here, where a function is not a
 * procedure but a side-effect free deterministic mapping, i.e., the function
 * always returns the same values for the same input.
 * However, the function does not have to be completely specified, i.e. if we
 * apply a function f to a domain value d the resulting value will always be
 * the same value r but the function definition does not have to specify
 * which concrete value r actually is. 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IProgramFunction extends IProgramSymbol {

	@Override
	default String getGloballyUniqueId() {
		return getFunctionSymbol().getName();
	}
	
	/**
	 * @return the SMT function symbol which represents this function.
	 */
	FunctionSymbol getFunctionSymbol();
}
