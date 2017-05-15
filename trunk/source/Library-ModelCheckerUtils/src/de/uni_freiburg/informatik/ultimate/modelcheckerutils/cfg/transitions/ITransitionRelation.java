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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Generalized version of {@link TransFormula} where the constraint is
 * not necessarily given as a Term.
 * TODO: documentation
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface ITransitionRelation {

	Set<IProgramVar> getAssignedVars();

	Map<IProgramVar, TermVariable> getInVars();

	Map<IProgramVar, TermVariable> getOutVars();

	Set<IProgramConst> getNonTheoryConsts();
	
	default Set<IProgramFunction> getNonTheoryFunctions() {
		throw new UnsupportedOperationException("not yet implemented");
	}

	/**
	 * If this method returns true, the outVar of bv may have any value even if the value of the inVar is restricted. If
	 * the methods returns false there are constraints on the outVar or syntactic check was not able to find out that
	 * there are no constraints.
	 */
	boolean isHavocedOut(IProgramVar bv);

	boolean isHavocedIn(IProgramVar bv);
	
	Set<TermVariable> getAuxVars();

}