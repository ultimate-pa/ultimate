package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class GuardedUpdateEdgeTraverser {

	private static final Comparator<GuardedUpdateEdge> PREPARED_EDGE_ORDER =
			Comparator.comparing((GuardedUpdateEdge edge) -> edge.source().toString())
					.thenComparing(edge -> edge.target().toString())
					.thenComparing(edge -> edge.transitionPredicate().getFormula().toString());

	private final Map<IcfgLocation, List<GuardedUpdateEdge>> mPreparedEdgesBySource;

	public GuardedUpdateEdgeTraverser(final IIcfg<IcfgLocation> icfg,
			final TransFormulaToInterferencePredicate translator) {
		mPreparedEdgesBySource = prepareEdges(icfg, translator);
	}

	public List<GuardedUpdateEdge> collect(final Map<IcfgLocation, IPredicate> locationStates) {
		return locationStates.keySet().stream()
				.map(mPreparedEdgesBySource::get)
				.filter(java.util.Objects::nonNull)
				.flatMap(List::stream)
				.toList();
	}

	private static Map<IcfgLocation, List<GuardedUpdateEdge>> prepareEdges(final IIcfg<IcfgLocation> icfg,
			final TransFormulaToInterferencePredicate translator) {
		final Map<IcfgLocation, List<GuardedUpdateEdge>> preparedEdgesBySource = new LinkedHashMap<>();
		IcfgUtils.getAllLocations(icfg).forEach(source -> {
			final List<GuardedUpdateEdge> preparedEdges = new ArrayList<>();
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final GuardedUpdateEdge prepared = prepareEdge(source, edge, translator);
				if (prepared != null) {
					preparedEdges.add(prepared);
				}
			}
			if (!preparedEdges.isEmpty()) {
				preparedEdges.sort(PREPARED_EDGE_ORDER);
				preparedEdgesBySource.put(source, List.copyOf(preparedEdges));
			}
		});
		return Map.copyOf(preparedEdgesBySource);
	}

	private static GuardedUpdateEdge prepareEdge(final IcfgLocation source, final IcfgEdge edge,
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
		return new GuardedUpdateEdge(source, target, InterferenceGrouping.keyFor(translator, source, target),
				transitionPredicate,
				computeModifiedGlobals(source, target, forkedThreadId, edge, translator, additionallyChangedGlobals));
	}

	private static Set<TermVariable> computeModifiedGlobals(final IcfgLocation source, final IcfgLocation target,
			final String forkedThreadId, final IcfgEdge edge, final TransFormulaToInterferencePredicate translator,
			final Set<IProgramVar> additionallyChangedGlobals) {
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

	public record GuardedUpdateEdge(IcfgLocation source, IcfgLocation target, AbstractLocationPair abstractLocationPair,
			IPredicate transitionPredicate, Set<TermVariable> modifiedGlobals) {
	}
}
