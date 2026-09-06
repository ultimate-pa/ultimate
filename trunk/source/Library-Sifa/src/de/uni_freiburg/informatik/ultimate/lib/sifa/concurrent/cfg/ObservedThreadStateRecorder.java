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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.LocationMarkerTransition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public final class ObservedThreadStateRecorder {

	private final IDomain mDomain;
	private final GhostVariableManager mGhostVariables;
	private final Map<IcfgLocation, IPredicate> mObservedLocationStates = new LinkedHashMap<>();

	public ObservedThreadStateRecorder(final IDomain domain, final GhostVariableManager ghostVariables) {
		mDomain = domain;
		mGhostVariables = ghostVariables;
	}

	public Map<IcfgLocation, IPredicate> snapshotObservedStates() {
		return Collections.unmodifiableMap(new LinkedHashMap<>(mObservedLocationStates));
	}

	public void recordTransitionInputState(final IIcfgTransition<IcfgLocation> transition,
			final IPredicate inputState) {
		if (!shouldCaptureTransitionInputForInterference(transition)) {
			return;
		}
		final IcfgLocation source = transition.getSource();
		if (source != null) {
			recordObservedState(source, inputState);
		}
	}

	public void recordObservedState(final IcfgLocation location, final IPredicate state) {
		mObservedLocationStates.merge(location, state, mDomain::join);
	}

	private boolean shouldCaptureTransitionInputForInterference(final IIcfgTransition<IcfgLocation> transition) {
		if (transition instanceof LocationMarkerTransition || !(transition instanceof final IcfgEdge edge)) {
			return false;
		}
		if (InterferenceUtils.hasRelevantInterferenceEffect(edge)) {
			return true;
		}
		if (mGhostVariables == null) {
			return true;
		}
		final IcfgLocation source = transition.getSource();
		final IcfgLocation target = transition.getTarget();
		return source != null && target != null && !mGhostVariables.hasSameAbstractLocation(source, target);
	}
}
