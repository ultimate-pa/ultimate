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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;


/**
 * Represents a set of program states.
 * Generic version that does not rely on Terms
 * TOOD: Find good name, This about parameterization with constraint
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public interface IAbstractPredicate {

	String[] getProcedures();

	/**
	 * Returns a superset of the all {@link IProgramVar} that are constraint
	 * by this predicate (informally: whose corresponding TermVariable "occurs" 
	 * in this IPredicate)
	 * It is sound to return the set of variables but a better approximation
	 * increases the speed of some operations and increases the precision
	 * of data flow-based analysis
	 */
	Set<IProgramVar> getVars();
	
	/**
	 * Similar that {@link this#getVars()} but for constants. 
	 */
	default Set<IProgramConst> getConstants() {
		throw new UnsupportedOperationException("not yet implemented");
	}
	
	/**
	 * Similar that {@link this#getVars()} but for constants. 
	 */
	default Set<IProgramFunction> getFunctions() {
		throw new UnsupportedOperationException("not yet implemented");
	}

}