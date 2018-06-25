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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Classes that implement this interface define the effect that a transition has
 * on (non-control-flow) variables of the system. Note that there are no
 * explicit control-flow variables (like a program counter or a call stack) in
 * our ICFG. <br />
 * In contrast to {@link IIcfgTransition}s the {@link IAction}s do not have to
 * provide predecessor and successor locations.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IAction {
	/**
	 * @return Identifier of the procedure in which the system/program is before
	 *         this action is executed.
	 */
	@Visualizable
	String getPrecedingProcedure();

	/**
	 * @return Identifier of the procedure in which the system/program is after this
	 *         action is executed.
	 */
	@Visualizable
	String getSucceedingProcedure();

	/**
	 * @return {@link TransFormula} which defines
	 *         <ul>
	 *         <li>how the system/program's variables are modified while executing
	 *         this action
	 *         <li>in which states this action can be executed (e.g., x'=x+1 /\ x
	 *         >=23 can only be executed in states where the value of the variable x
	 *         is greater than or equal to 23.
	 *         </ul>
	 */
	@Visualizable
	UnmodifiableTransFormula getTransformula();
}
