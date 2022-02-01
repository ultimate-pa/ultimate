/*
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure;

/**
 * An {@link IIcfgTransition} that represents a Fork. Edges of this type connect
 * the location of the fork with the entry location of the forked procedure.
 * Conceptually, there is only one transition that represents the fork and this
 * transition has one source and two targets. The data structures of our
 * {@link IIcfg} however do not support edges with two targets and as a
 * workaround we implement the fork by the two edges
 * {@link IIcfgForkTransitionThreadCurrent} and
 * {@link IIcfgForkTransitionThreadOther}.If our "petrification" produces
 * several thread instances for a thread template the resulting {@link IICFG}
 * has only one {@link IIcfgForkTransitionThreadCurrent} and several
 * {@link IIcfgForkTransitionThreadOther}.
 *
 * @author Lars Nitzke
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IIcfgForkTransitionThreadOther<LOC extends IcfgLocation>
		extends IIcfgTransition<LOC>, IForkActionThreadOther {

	IIcfgForkTransitionThreadCurrent<LOC> getCorrespondingIIcfgForkTransitionCurrentThread();

}
