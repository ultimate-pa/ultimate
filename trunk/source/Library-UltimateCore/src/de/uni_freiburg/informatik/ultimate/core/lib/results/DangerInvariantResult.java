/*
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Report a danger invariant.
 *
 * @author Dennis Wölfing
 *
 * @param <LOC>
 *            The type of the locations.
 * @param <TERM>
 *            The type of the terms.
 */
public class DangerInvariantResult<LOC, TERM> extends AbstractResult {
	private final Map<LOC, TERM> mInvariants;
	private final Set<LOC> mErrorLocations;
	private final IBacktranslationService mBacktranslator;

	/**
	 * Creates a DangerInvariantResult.
	 *
	 * @param plugin
	 *            The plugin name.
	 * @param invariants
	 *            A map from locations to invariants.
	 * @param errorLocations
	 *            A set of error locations.
	 * @param backtranslator
	 *            A backtranslation service.
	 */
	public DangerInvariantResult(final String plugin, final Map<LOC, TERM> invariants, final Set<LOC> errorLocations,
			final IBacktranslationService backtranslator) {
		super(plugin);
		mInvariants = invariants;
		mErrorLocations = errorLocations;
		mBacktranslator = backtranslator;
	}

	@Override
	public String getShortDescription() {
		return "Danger Invariant";
	}

	@SuppressWarnings("unchecked")
	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Derived danger invariant for the following error locations: ");
		sb.append(mErrorLocations);
		for (final Map.Entry<LOC, TERM> entry : mInvariants.entrySet()) {
			sb.append(CoreUtil.getPlatformLineSeparator());
			sb.append(entry.getKey());
			sb.append(": ");
			sb.append(mBacktranslator.translateExpressionToString(entry.getValue(),
					(Class<TERM>) entry.getValue().getClass()));
		}
		return sb.toString();
	}
}
