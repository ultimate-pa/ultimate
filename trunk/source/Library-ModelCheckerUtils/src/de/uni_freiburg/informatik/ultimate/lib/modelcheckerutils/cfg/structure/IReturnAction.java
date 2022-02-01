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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Classes that implement this interface represent an {@link IAction} that defines the effect that a return has to the
 * (non-control-flow) variables of the system. A return is the transition that brings the system from the called
 * procedure back to the called procedure. This means that the effect of the of a return is that
 * <ul>
 * <li>local variables of the calling context get the values that they had before the call
 * <li>variables that are assigned by the call get the values that are returned by the procedure
 * <li>all local variables that occur only in the context of the called procedure are havoced.
 * <ul />
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IReturnAction extends IAction {

	/**
	 * @return {@link TransFormula} which defines how the variables that are explicitly mentioned in the call are
	 *         updated on the return (this does not include information about modifiable global variables that are
	 *         implicitly modified).
	 */
	@Visualizable
	UnmodifiableTransFormula getAssignmentOfReturn();

	/**
	 * @return {@link TransFormula} which defines how the local variables of the called procedure are modified while
	 *         executing the corresponding call action.
	 */
	@Visualizable
	UnmodifiableTransFormula getLocalVarsAssignmentOfCall();

	@Override
	default UnmodifiableTransFormula getTransformula() {
		return getAssignmentOfReturn();
	}
}
