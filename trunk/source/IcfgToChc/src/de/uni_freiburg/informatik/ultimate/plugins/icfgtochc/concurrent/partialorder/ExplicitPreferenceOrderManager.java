/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder;

import java.util.Comparator;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.HornClauseBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ThreadInstance;

class ExplicitPreferenceOrderManager implements IPreferenceOrderManager {
	private final IThreadModularPreferenceOrder mPreferenceOrder;
	private final Script mScript;
	private final Map<IcfgLocation, Integer> mLocationMap;

	public ExplicitPreferenceOrderManager(final IThreadModularPreferenceOrder preferenceOrder, final Script script,
			final Map<IcfgLocation, Integer> locationMap) {
		mPreferenceOrder = preferenceOrder;
		mScript = script;
		mLocationMap = locationMap;
	}

	@Override
	public Term getOrderConstraint(final HornClauseBuilder clause, final Comparator<ThreadInstance> comp,
			final ThreadInstance thread1, final IcfgLocation loc1, final Term locTerm1, final ThreadInstance thread2,
			final IcfgLocation loc2, final Term locTerm2) {
		// (loc1, loc2) in R
		final var locConstraint1 = mPreferenceOrder.getOrderConstraint(loc1, locTerm1, loc2, locTerm2, mLocationMap);

		final int ordering = comp.compare(thread1, thread2);
		if (ordering < 0) {
			// implication "(loc2, loc1) in R ==> thread1 < thread2" trivially true
			return locConstraint1;
		}

		// (loc2, loc1) in R
		final var locConstraint2 = mPreferenceOrder.getOrderConstraint(loc2, locTerm2, loc1, locTerm1, mLocationMap);

		// (loc1, loc2) in R /\ (loc2, loc1) not in R
		return SmtUtils.and(mScript, locConstraint1, SmtUtils.not(mScript, locConstraint2));
	}

	@Override
	public void ensureUniqueThreadIDs(final HornClauseBuilder clause, final List<ThreadInstance> instances) {
		// nothing to do
	}
}