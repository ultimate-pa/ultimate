package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.LocationMarkerTransition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public final class ObservedThreadStateRecorder {

	private final IDomain mInterferenceDomain;
	private final GhostVariableManager mGhostVariables;
	private final Map<IcfgLocation, IPredicate> mObservedLocationStates = new HashMap<>();

	public ObservedThreadStateRecorder(final IDomain interferenceDomain, final GhostVariableManager ghostVariables) {
		mInterferenceDomain = interferenceDomain;
		mGhostVariables = ghostVariables;
	}

	public Map<IcfgLocation, IPredicate> snapshotObservedStates() {
		return Map.copyOf(mObservedLocationStates);
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
		mObservedLocationStates.merge(location, state, mInterferenceDomain::join);
	}

	private boolean shouldCaptureTransitionInputForInterference(final IIcfgTransition<IcfgLocation> transition) {
		if (transition instanceof LocationMarkerTransition) {
			return false;
		}
		if (transition instanceof IIcfgForkTransitionThreadCurrent<?>) {
			return true;
		}
		final var transformula = transition.getTransformula();
		if (transformula == null) {
			return false;
		}
		if (transformula.getAssignedVars().stream().anyMatch(var -> var.isGlobal())) {
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
