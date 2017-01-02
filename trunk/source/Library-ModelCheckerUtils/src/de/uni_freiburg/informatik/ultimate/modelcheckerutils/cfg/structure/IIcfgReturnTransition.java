/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;

/**
 * An {@link IIcfgTransition} that represents a Return.
 * 
 * An {@link IIcfgReturnTransition} in a {@link IIcfg} represents the return from a called procedure. This represents
 * the execution starting from the position directly before the return statement (resp. the last position of a procedure
 * if there is no return statement) to the position after the corresponding call statement. The update of the variables
 * of the calling procedure is defined by the {@link TransFormula} provided by
 * {@link IIcfgReturnTransition#getAssignmentOfReturn()}.
 * 
 * Note that each {@link IIcfgReturnTransition} has to have a corresponding call (provided by
 * {@link IIcfgReturnTransition#getCorrespondingCall()}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IIcfgReturnTransition<LOC extends IcfgLocation, T extends IIcfgCallTransition<LOC>>
		extends IIcfgTransition<LOC>, IReturnAction {

	/**
	 * @return the {@link IIcfgCallTransition} that has to be taken before this {@link IIcfgReturnTransition} can be
	 *         taken.
	 */
	T getCorrespondingCall();

	/**
	 * @return the location that represents the call site.
	 */
	default LOC getCallerProgramPoint() {
		return getCorrespondingCall().getSource();
	}

}
