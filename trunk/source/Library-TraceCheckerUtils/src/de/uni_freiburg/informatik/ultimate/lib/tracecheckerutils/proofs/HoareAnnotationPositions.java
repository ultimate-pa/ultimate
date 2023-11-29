/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.proofs;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;

/**
 * Hoare annotation position.
 */
public enum HoareAnnotationPositions {
	All, LoopHeads, LoopsAndPotentialCycles;

	public <LOC extends IcfgLocation> Set<LOC> getLocationsForWhichHoareAnnotationIsComputed(final IIcfg<LOC> root) {
		final Set<LOC> hoareAnnotationLocs = new HashSet<>();
		switch (this) {
		case All:
			for (final Map<DebugIdentifier, LOC> value : root.getProgramPoints().values()) {
				hoareAnnotationLocs.addAll(value.values());
			}
			break;
		case LoopsAndPotentialCycles:
			hoareAnnotationLocs.addAll(root.getLoopLocations());
			hoareAnnotationLocs.addAll(IcfgUtils.getCallerAndCalleePoints(root));
			hoareAnnotationLocs.addAll(IcfgUtils.getPotentialCycleProgramPoints(root));
			break;
		case LoopHeads:
			hoareAnnotationLocs.addAll(root.getLoopLocations());
			hoareAnnotationLocs.addAll(IcfgUtils.getCallerAndCalleePoints(root));
			break;
		default:
			throw new AssertionError("unknown value " + this);
		}
		return hoareAnnotationLocs;
	}
}