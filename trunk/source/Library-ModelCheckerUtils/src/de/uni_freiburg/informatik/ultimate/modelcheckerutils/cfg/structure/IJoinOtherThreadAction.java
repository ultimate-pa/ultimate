/*
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
 * Copyright (C) 2018 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Classes that implement this interface represent an {@link IAction} which labels a join edge 
 * from another thread in an interprocedural control flow graph.
 *
 * @author Lars Nitzke (lars.nitzke@outlook.com)
 *
 */
public interface IJoinOtherThreadAction extends IAction {
	/**
	 * @return {@link TransFormula} which defines how the variables that are explicitly mentioned in the fork are
	 *         updated on the join (this does not include information about modifiable global variables that are
	 *         implicitly modified).
	 */
	UnmodifiableTransFormula getAssignmentOfJoin();

	/**
	 * @return {@link TransFormula} which defines how the local variables of the forked procedure are modified while
	 *         executing the corresponding fork action.
	 */
	UnmodifiableTransFormula getLocalVarsAssignmentOfFork();

	@Override
	default UnmodifiableTransFormula getTransformula() {
		return getAssignmentOfJoin();
	}
}
