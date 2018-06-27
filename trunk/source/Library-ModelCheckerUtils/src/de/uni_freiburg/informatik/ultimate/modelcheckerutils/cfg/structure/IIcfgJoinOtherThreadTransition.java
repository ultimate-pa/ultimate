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

/** 
 * An {@link IIcfgTransition} that represents a Join from another thread. Edges of this type connect 
 * the location directly after the join with the exit location of the forked procedure.
 *  
 * An {@link IIcfgJoinOtherThreadTransition} in a {@link IIcfg} represents the join with a forked procedure. This represents
 * the execution starting from the last position of a forked procedure to the position of the corresponding join statement. 
 * The update of the variables of the forking procedure is defined by the {@link TransFormula} provided by
 * {@link IIcfgJoinOtherThreadTransition#getAssignmentOfJoin()}.
 * 
 * Note that each {@link IIcfgJoinOtherThreadTransition} has to have a corresponding fork (provided by
 * {@link IIcfgJoinOtherThreadTransition#getCorrespondingFork()}.
 * 
 * @author Lars Nitzke
 *
 */
public interface IIcfgJoinOtherThreadTransition<LOC extends IcfgLocation, T 
		extends IIcfgForkOtherThreadTransition<LOC>> extends IIcfgTransition<LOC>, IJoinOtherThreadAction {
	
	/**
	 * @return the {@link IIcfgForkOtherThreadTransition} that has to be taken before this 
	 * {@link IIcfgJoinOtherThreadTransition} can be taken.
	 */
	T getCorrespondingFork();

	/**
	 * @return the location that represents the call site.
	 */
	default LOC getForkerProgramPoint() {
		return getCorrespondingFork().getSource();
	}
}
