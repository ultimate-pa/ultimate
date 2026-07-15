package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.LocationMarkerTransition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
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
