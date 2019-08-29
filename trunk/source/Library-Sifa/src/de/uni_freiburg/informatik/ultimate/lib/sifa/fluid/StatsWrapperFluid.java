/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.fluid;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

/**
 * Updates all statistics so that the wrapped fluid doesn't have to.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class StatsWrapperFluid implements IFluid {

	private final IFluid mFluid;
	private final SifaStats mStats;

	public StatsWrapperFluid(final SifaStats stats, final IFluid fluid) {
		mStats = stats;
		mFluid = fluid;
	}

	@Override
	public boolean shallBeAbstracted(final IPredicate predicate) {
		mStats.increment(SifaStats.Key.FLUID_QUERIES);
		mStats.start(SifaStats.Key.FLUID_QUERY_TIME);
		final boolean result = mFluid.shallBeAbstracted(predicate);
		mStats.stop(SifaStats.Key.FLUID_QUERY_TIME);
		if (result) {
			mStats.increment(SifaStats.Key.FLUID_YES_ANSWERS);
		}
		return result;
	}
}
