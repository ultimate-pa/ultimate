package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

/** Small helpers shared by interference extraction and proof checking. */
public final class InterferenceEdgeSemantics {

	private InterferenceEdgeSemantics() {
	}

	public static boolean modifiesGlobals(final TransFormula tf) {
		return tf.getAssignedVars().stream().anyMatch(IProgramVar::isGlobal);
	}

	public static String getForkedThreadOrNull(final IcfgEdge edge) {
		if (edge instanceof final IIcfgForkTransitionThreadCurrent<?> forkEdge) {
			return forkEdge.getNameOfForkedProcedure();
		}
		return null;
	}

	public static boolean isJoinAssigningGlobal(final IcfgEdge edge) {
		if (edge instanceof final IIcfgJoinTransitionThreadCurrent<?> joinCurrent) {
			return joinCurrent.getJoinSmtArguments().getAssignmentLhs().stream().anyMatch(IProgramVar::isGlobal);
		}
		if (edge instanceof final IIcfgJoinTransitionThreadOther<?> joinOther) {
			return modifiesGlobals(joinOther.getAssignmentOfJoin());
		}
		return false;
	}

	public static Set<IProgramVar> getJoinAssignedGlobals(final IcfgEdge edge) {
		if (!(edge instanceof final IIcfgJoinTransitionThreadCurrent<?> joinCurrent)) {
			return Set.of();
		}
		final List<IProgramVar> globals =
				joinCurrent.getJoinSmtArguments().getAssignmentLhs().stream().filter(IProgramVar::isGlobal).toList();
		return globals.isEmpty() ? Set.of() : Set.copyOf(globals);
	}
}
