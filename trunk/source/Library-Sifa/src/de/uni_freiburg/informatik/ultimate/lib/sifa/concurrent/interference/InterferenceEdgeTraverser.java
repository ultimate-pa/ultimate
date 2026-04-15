package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class InterferenceEdgeTraverser {

	private final Map<IcfgLocation, List<PreparedInterferenceEdge>> mPreparedEdgesBySource;

	public InterferenceEdgeTraverser(final IIcfg<IcfgLocation> icfg,
			final TransFormulaToInterferencePredicate translator) {
		mPreparedEdgesBySource = prepareEdges(icfg, translator);
	}

	public List<InterferenceEdge> collect(final Map<IcfgLocation, IPredicate> locationStates) {
		final List<InterferenceEdge> edges = new ArrayList<>();
		for (final var entry : locationStates.entrySet()) {
			final IcfgLocation source = entry.getKey();
			final IPredicate sourceState = entry.getValue();
			if (sourceState == null) {
				continue;
			}
			final List<PreparedInterferenceEdge> preparedEdges = mPreparedEdgesBySource.get(source);
			if (preparedEdges == null) {
				continue;
			}
			for (final PreparedInterferenceEdge preparedEdge : preparedEdges) {
				edges.add(new InterferenceEdge(preparedEdge, sourceState));
			}
		}
		edges.sort((left, right) -> InterferenceUtils.PREPARED_EDGE_ORDER.compare(left.prepared(), right.prepared()));
		return List.copyOf(edges);
	}

	private static Map<IcfgLocation, List<PreparedInterferenceEdge>> prepareEdges(final IIcfg<IcfgLocation> icfg,
			final TransFormulaToInterferencePredicate translator) {
		final Map<IcfgLocation, List<PreparedInterferenceEdge>> preparedEdgesBySource = new LinkedHashMap<>();
		IcfgUtils.getAllLocations(icfg).forEach(source -> {
			final List<PreparedInterferenceEdge> preparedEdges = new ArrayList<>();
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final PreparedInterferenceEdge prepared = prepareEdge(source, edge, translator);
				if (prepared != null) {
					preparedEdges.add(prepared);
				}
			}
			if (!preparedEdges.isEmpty()) {
				preparedEdges.sort(InterferenceUtils.PREPARED_EDGE_ORDER);
				preparedEdgesBySource.put(source, List.copyOf(preparedEdges));
			}
		});
		return Map.copyOf(preparedEdgesBySource);
	}

	private static PreparedInterferenceEdge prepareEdge(final IcfgLocation source, final IcfgEdge edge,
			final TransFormulaToInterferencePredicate translator) {
		final IcfgLocation target = edge.getTarget();
		if (target == null || edge.getTransformula() == null) {
			return null;
		}
		final String forkedThreadId = InterferenceUtils.getForkedThreadOrNull(edge);
		final boolean interferenceRelevant = InterferenceUtils.hasRelevantInterferenceEffect(edge);
		final boolean locationStutter = source.equals(target) && forkedThreadId == null;
		if (!interferenceRelevant && locationStutter) {
			return null;
		}
		final Set<de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar> additionallyChangedGlobals =
				InterferenceUtils.getAdditionalChangedGlobals(edge);
		final IPredicate transitionPredicate = forkedThreadId == null
				? translator.translateForInterference(edge.getTransformula(), source.getProcedure(), source, target,
						additionallyChangedGlobals)
				: translator.translateForInterferenceWithFork(edge.getTransformula(), source.getProcedure(), source, target,
						forkedThreadId, translator.getEntryLocation(forkedThreadId), additionallyChangedGlobals);
		return new PreparedInterferenceEdge(source, target, InterferenceGrouping.keyFor(translator, source, target),
				transitionPredicate,
				computeModifiedGlobals(source, target, forkedThreadId, edge, translator, additionallyChangedGlobals));
	}

	private static Set<TermVariable> computeModifiedGlobals(final IcfgLocation source, final IcfgLocation target,
			final String forkedThreadId, final IcfgEdge edge, final TransFormulaToInterferencePredicate translator,
			final Set<de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar> additionallyChangedGlobals) {
		final Set<TermVariable> modified =
				new java.util.HashSet<>(InterferenceUtils.getChangedGlobalTermVars(edge.getTransformula(), additionallyChangedGlobals));
		final TermVariable interferingLoc = translator.getLocationTermVarOrNull(source.getProcedure());
		final boolean locationChanges = forkedThreadId != null || !translator.isLocationStutterStep(source, target);
		if (interferingLoc != null && locationChanges) {
			modified.add(interferingLoc);
		}
		if (forkedThreadId != null) {
			final TermVariable forkedLoc = translator.getLocationTermVarOrNull(forkedThreadId);
			if (forkedLoc != null) {
				modified.add(forkedLoc);
			}
		}
		return modified.isEmpty() ? Set.of() : Set.copyOf(modified);
	}
}
