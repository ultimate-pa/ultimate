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
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

/**
 * Updates all statistics so that the wrapped domain doesn't have to.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class StatsWrapperDomain implements IDomain {

	private final SifaStats mStats;
	private final IDomain mInternDomain;

	public StatsWrapperDomain(final SifaStats stats, final IDomain internDomain) {
		mStats = stats;
		mInternDomain = internDomain;
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		mStats.start(SifaStats.Key.DOMAIN_JOIN_TIME);
		mStats.increment(SifaStats.Key.DOMAIN_JOIN_APPLICATIONS);
		final IPredicate result = mInternDomain.join(lhs, rhs);
		mStats.stop(SifaStats.Key.DOMAIN_JOIN_TIME);
		return result;
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		mStats.start(SifaStats.Key.DOMAIN_WIDEN_TIME);
		mStats.increment(SifaStats.Key.DOMAIN_WIDEN_APPLICATIONS);
		final IPredicate result = mInternDomain.widen(old, widenWith);
		mStats.stop(SifaStats.Key.DOMAIN_WIDEN_TIME);
		return result;
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		mStats.start(SifaStats.Key.DOMAIN_ISBOTTOM_TIME);
		mStats.increment(SifaStats.Key.DOMAIN_ISBOTTOM_APPLICATIONS);
		final ResultForAlteredInputs result = mInternDomain.isEqBottom(pred);
		mStats.stop(SifaStats.Key.DOMAIN_ISBOTTOM_TIME);
		return result;
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		mStats.start(SifaStats.Key.DOMAIN_ISSUBSETEQ_TIME);
		mStats.increment(SifaStats.Key.DOMAIN_ISSUBSETEQ_APPLICATIONS);
		final ResultForAlteredInputs result = mInternDomain.isSubsetEq(subset, superset);
		mStats.stop(SifaStats.Key.DOMAIN_ISSUBSETEQ_TIME);
		return result;
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		mStats.start(SifaStats.Key.DOMAIN_ALPHA_TIME);
		mStats.increment(SifaStats.Key.DOMAIN_ALPHA_APPLICATIONS);
		final IPredicate result = mInternDomain.alpha(pred);
		mStats.stop(SifaStats.Key.DOMAIN_ALPHA_TIME);
		return result;
	}

}
