package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;

public final class InterferenceEdgeTraverser {

	private final Map<IcfgLocation, List<TranslatedInterferenceOfEdge>> mInterferenceBySourceLocation;

	public InterferenceEdgeTraverser(final IIcfg<IcfgLocation> icfg,
			final TransFormulaToInterferencePredicate translator) {
		mInterferenceBySourceLocation = prepareEdges(icfg, translator);
	}

	public List<TranslatedInterferenceOfEdge> collect(final Map<IcfgLocation, IPredicate> locationStates) {
		return locationStates.keySet().stream()
				.map(mInterferenceBySourceLocation::get)
				.filter(Objects::nonNull)
				.flatMap(List::stream)
				.toList();
	}

	private static Map<IcfgLocation, List<TranslatedInterferenceOfEdge>> prepareEdges(final IIcfg<IcfgLocation> icfg,
			final TransFormulaToInterferencePredicate translator) {
		final Map<IcfgLocation, List<TranslatedInterferenceOfEdge>> preparedEdgesBySource = new LinkedHashMap<>();
		IcfgUtils.getAllLocations(icfg).forEach(source -> {
			final List<TranslatedInterferenceOfEdge> preparedEdges = new ArrayList<>();
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final TranslatedInterferenceOfEdge prepared = prepareEdge(source, edge, translator);
				if (prepared != null) {
					preparedEdges.add(prepared);
				}
			}
			if (!preparedEdges.isEmpty()) {
				preparedEdges.sort(InterferenceUtils.INTERFERENCE_EDGE_ORDER);
				preparedEdgesBySource.put(source, List.copyOf(preparedEdges));
			}
		});
		return Map.copyOf(preparedEdgesBySource);
	}

	private static TranslatedInterferenceOfEdge prepareEdge(final IcfgLocation source, final IcfgEdge edge,
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
		final Set<IProgramVar> additionallyChangedGlobals = InterferenceUtils.getAdditionalChangedGlobals(edge);
		final IPredicate transitionPredicate = forkedThreadId == null
				? translator.translateForInterference(edge.getTransformula(), source.getProcedure(), source, target,
						additionallyChangedGlobals)
				: translator.translateForInterferenceWithFork(edge.getTransformula(), source.getProcedure(), source, target,
						forkedThreadId, translator.getEntryLocation(forkedThreadId), additionallyChangedGlobals);
		return new TranslatedInterferenceOfEdge(source, target, InterferenceGrouping.keyFor(translator, source, target),
				transitionPredicate, InterferenceUtils.getChangedGlobals(edge.getTransformula(), additionallyChangedGlobals));
	}
}
