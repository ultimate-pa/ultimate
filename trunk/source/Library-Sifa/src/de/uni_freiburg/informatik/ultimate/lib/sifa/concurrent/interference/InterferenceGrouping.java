/*
 * Copyright (C) 2026 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;

public final class InterferenceGrouping {

	public record AbstractLocationPair(int sourceAbstractLocation, int targetAbstractLocation) {
	}

	private InterferenceGrouping() {
	}

	public static AbstractLocationPair keyFor(final TransFormulaToInterferencePredicate translator,
			final IcfgLocation source, final IcfgLocation target) {
		return new AbstractLocationPair(checkAbstractLocationId(translator, source),
				checkAbstractLocationId(translator, target));
	}

	private static int checkAbstractLocationId(final TransFormulaToInterferencePredicate translator,
			final IcfgLocation location) {
		final Integer abstractLocationId = translator.getAbstractLocationIdOrNull(location);
		if (abstractLocationId == null) {
			throw new IllegalStateException("Missing abstract location ID for " + location);
		}
		return abstractLocationId;
	}
}
