package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DataRaceAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ControlPartitioningHeuristics {
	private final ManagedScript mManagedScript;
	private final IIcfg<IcfgLocation> mIcfg;
	private final Set<IProgramNonOldVar> mGlobals;
	private final Map<TermVariable, IProgramVar> mTermToGlobalMap;
	private final IUltimateServiceProvider mServices;

	public ControlPartitioningHeuristics(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg) {
		mManagedScript = icfg.getCfgSmtToolkit().getManagedScript();
		mIcfg = icfg;
		mGlobals = mIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals();
		mTermToGlobalMap = mGlobals.stream().collect(Collectors.toMap(IProgramVar::getTermVariable, v -> v));
		mServices = services;
	}

	public Map<IcfgLocation, Integer> guardSplitting() {
		return threePhaseMutexSplitting();
	}

	public Map<IcfgLocation, Integer> allVarOccurrencesSplit() {
		return allVarOccurrencesSplit(Set.of());
	}

	public Map<IcfgLocation, Integer> allVarOccurrencesSplit(final Set<IProgramVar> excludedVars) {
		return splitAtGuardsAndWrites(computeFoundationalBaseMapping(excludedVars), excludedVars);
	}

	private Map<IcfgLocation, Set<IProgramVar>> computeMutexVars(final boolean fullyPrecise) {
		final Map<IcfgLocation, Set<IProgramVar>> mutexGuardToVarsMap = new HashMap<>();
		for (final IcfgLocation loc : collectReachableFromEntries()) {
			final List<IcfgEdge> outgoing = loc.getOutgoingEdges();
			if (!shouldDifferentiate(outgoing, fullyPrecise)) {
				continue;
			}
			final Set<IProgramVar> guardVars = getGuardVars(outgoing, fullyPrecise);
			if (!guardVars.isEmpty()) {
				mutexGuardToVarsMap.put(loc, guardVars);
			}
		}
		return mutexGuardToVarsMap;
	}

	private Map<IcfgLocation, Integer> computeFoundationalBaseMapping(final Set<IProgramVar> excludedVars) {
		final Set<IcfgLocation> reachableFromEntries = collectReachableFromEntries();
		final Map<IcfgLocation, IcfgLocation> parent = new HashMap<>();
		for (final IcfgLocation loc : reachableFromEntries) {
			parent.put(loc, loc);
		}

		for (final IcfgLocation source : reachableFromEntries) {
			final String procedure = source.getProcedure();
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (target == null || !procedure.equals(target.getProcedure()) || !parent.containsKey(target)) {
					continue;
				}
				if (!isFoundationalSplitEdge(edge, excludedVars)) {
					union(parent, source, target);
				}
			}
		}

		final Map<String, Set<IcfgLocation>> locationsByProcedure = groupByProcedure(reachableFromEntries);
		final Map<IcfgLocation, Integer> result = new HashMap<>();
		for (final String procedure : sortedKeys(locationsByProcedure)) {
			assignProcedureComponentIds(procedure, locationsByProcedure.get(procedure), parent, result);
		}
		return result;
	}

	private void assignProcedureComponentIds(final String procedure, final Set<IcfgLocation> procedureLocations,
			final Map<IcfgLocation, IcfgLocation> parent, final Map<IcfgLocation, Integer> result) {
		if (procedureLocations == null || procedureLocations.isEmpty()) {
			return;
		}

		final IcfgLocation entry = mIcfg.getProcedureEntryNodes().get(procedure);
		final IcfgLocation entryRep = entry != null && parent.containsKey(entry) ? find(parent, entry) : null;
		final Map<IcfgLocation, Integer> compToId = new HashMap<>();
		int nextId = 2;
		for (final IcfgLocation loc : orderedLocations(procedureLocations)) {
			final IcfgLocation rep = find(parent, loc);
			final int id;
			if (entryRep != null && rep.equals(entryRep)) {
				id = 1;
			} else {
				final Integer existing = compToId.get(rep);
				if (existing != null) {
					id = existing;
				} else {
					id = nextId;
					nextId++;
					compToId.put(rep, id);
				}
			}
			result.put(loc, id);
		}
		if (entry != null && parent.containsKey(entry)) {
			result.put(entry, 1);
		}
	}

	private Map<IcfgLocation, Integer> splitAtGuardsAndWrites(final Map<IcfgLocation, Integer> foundationalMap,
			final Set<IProgramVar> excludedVars) {
		final Map<IcfgLocation, Integer> abstractLocationMapping = new HashMap<>(foundationalMap);
		final Map<IcfgLocation, Set<IProgramVar>> mutexGuardToVarsMap = computeMutexVars(false);
		if (!excludedVars.isEmpty()) {
			mutexGuardToVarsMap.values().forEach(vars -> vars.removeAll(excludedVars));
			mutexGuardToVarsMap.values().removeIf(Set::isEmpty);
		}
		if (mutexGuardToVarsMap.isEmpty()) {
			return abstractLocationMapping;
		}
		final Set<IProgramVar> relevantGuardVars = mutexGuardToVarsMap.values().stream().flatMap(Set::stream)
				.collect(Collectors.toSet());
		final Map<String, Set<IcfgLocation>> locationsByProcedure = groupByProcedure(foundationalMap.keySet());
		for (final String procedure : sortedKeys(locationsByProcedure)) {
			final Set<IcfgLocation> procedureLocations = locationsByProcedure.get(procedure);
			if (procedureLocations == null || procedureLocations.isEmpty()) {
				continue;
			}
			int nextFreshId = nextFreshIdForProcedure(procedureLocations, abstractLocationMapping);
			for (final IcfgLocation loc : orderedLocationsInProcedureFlow(procedure, procedureLocations)) {
				if (!mutexGuardToVarsMap.containsKey(loc) && !writesAnyOf(loc, relevantGuardVars)) {
					continue;
				}
				abstractLocationMapping.put(loc, nextFreshId);
				nextFreshId++;
			}
		}
		return abstractLocationMapping;
	}

	private Map<IcfgLocation, Integer> threePhaseMutexSplitting() {
		final Map<IcfgLocation, Integer> result = singletonPerProcedureMapping();
		final Map<IcfgLocation, Set<IProgramVar>> mutexGuardToVarsMap = computeMutexVars(true);
		if (mutexGuardToVarsMap.isEmpty()) {
			return result;
		}

		final Map<String, Set<IcfgLocation>> locationsByProcedure = groupByProcedure(result.keySet());
		for (final String procedure : sortedKeys(locationsByProcedure)) {
			final Set<IcfgLocation> procedureLocations = locationsByProcedure.get(procedure);
			if (procedureLocations == null || procedureLocations.isEmpty()) {
				continue;
			}
			final List<IcfgLocation> ordered = orderedLocationsInProcedureFlow(procedure, procedureLocations);
			if (ordered.isEmpty()) {
				continue;
			}
			final Set<IProgramVar> guardVars = procedureLocations.stream().filter(mutexGuardToVarsMap::containsKey)
					.flatMap(loc -> mutexGuardToVarsMap.get(loc).stream()).collect(Collectors.toSet());
			if (guardVars.isEmpty()) {
				continue;
			}

			final int firstMutexInteraction = firstMutexInteractionIndex(ordered, mutexGuardToVarsMap, guardVars);
			if (firstMutexInteraction < 0) {
				continue;
			}
			final int insideStart = Math.min(firstMutexInteraction + 1, ordered.size() - 1);
			final int lastGuardVarWrite = lastGuardVarWriteIndex(ordered, guardVars);
			if (lastGuardVarWrite < insideStart) {
				for (int i = insideStart; i < ordered.size(); i++) {
					result.put(ordered.get(i), 2);
				}
				continue;
			}

			for (int i = insideStart; i <= lastGuardVarWrite; i++) {
				result.put(ordered.get(i), 2);
			}
			if (lastGuardVarWrite + 1 < ordered.size()) {
				for (int i = lastGuardVarWrite + 1; i < ordered.size(); i++) {
					result.put(ordered.get(i), 3);
				}
			}
		}
		return result;
	}

	private int firstMutexInteractionIndex(final List<IcfgLocation> ordered,
			final Map<IcfgLocation, Set<IProgramVar>> mutexGuardToVarsMap, final Set<IProgramVar> guardVars) {
		int firstGuard = -1;
		int firstWrite = -1;
		for (int i = 0; i < ordered.size(); i++) {
			final IcfgLocation loc = ordered.get(i);
			if (firstGuard < 0 && mutexGuardToVarsMap.containsKey(loc)) {
				firstGuard = i;
			}
			if (firstWrite < 0 && writesAnyOf(loc, guardVars)) {
				firstWrite = i;
			}
			if (firstGuard >= 0 && firstWrite >= 0) {
				break;
			}
		}
		return firstGuard >= 0 ? firstGuard : firstWrite;
	}

	private int lastGuardVarWriteIndex(final List<IcfgLocation> ordered, final Set<IProgramVar> guardVars) {
		int lastWrite = -1;
		for (int i = 0; i < ordered.size(); i++) {
			if (writesAnyOf(ordered.get(i), guardVars)) {
				lastWrite = i;
			}
		}
		return lastWrite;
	}

	private boolean writesAnyOf(final IcfgLocation loc, final Set<IProgramVar> vars) {
		if (vars.isEmpty()) {
			return false;
		}
		for (final IcfgEdge edge : loc.getOutgoingEdges()) {
			if (InterferenceUtils.writesAnyOf(edge.getTransformula(), vars)) {
				return true;
			}
		}
		return false;
	}

	private Map<IcfgLocation, Integer> singletonPerProcedureMapping() {
		final Map<IcfgLocation, Integer> result = new HashMap<>();
		for (final IcfgLocation loc : collectReachableFromEntries()) {
			result.put(loc, 1);
		}
		return result;
	}

	private int nextFreshIdForProcedure(final Set<IcfgLocation> procedureLocations,
			final Map<IcfgLocation, Integer> mapping) {
		return procedureLocations.stream().map(mapping::get).filter(id -> id != null).max(Integer::compareTo).orElse(0)
				+ 1;
	}

	private Map<String, Set<IcfgLocation>> groupByProcedure(final Set<IcfgLocation> locations) {
		final Map<String, Set<IcfgLocation>> locationsByProcedure = new HashMap<>();
		for (final IcfgLocation loc : locations) {
			locationsByProcedure.computeIfAbsent(loc.getProcedure(), ignored -> new LinkedHashSet<>()).add(loc);
		}
		return locationsByProcedure;
	}

	private List<IcfgLocation> orderedLocationsInProcedureFlow(final String procedure,
			final Set<IcfgLocation> procedureLocations) {
		final IcfgLocation entry = mIcfg.getProcedureEntryNodes().get(procedure);
		if (entry == null) {
			return orderedLocations(procedureLocations);
		}
		final LinkedHashSet<IcfgLocation> ordered = new LinkedHashSet<>();
		final IcfgLocationIterator<IcfgLocation> iter = new IcfgLocationIterator<>(entry);
		while (iter.hasNext()) {
			final IcfgLocation loc = iter.next();
			if (procedure.equals(loc.getProcedure()) && procedureLocations.contains(loc)) {
				ordered.add(loc);
			}
		}
		ordered.addAll(orderedLocations(procedureLocations));
		return new ArrayList<>(ordered);
	}

	private List<IcfgLocation> orderedLocations(final Set<IcfgLocation> locations) {
		final List<IcfgLocation> ordered = new ArrayList<>(locations);
		ordered.sort(
				Comparator.comparing((final IcfgLocation loc) -> loc.getProcedure()).thenComparing(Object::toString));
		return ordered;
	}

	private List<String> sortedKeys(final Map<String, ?> map) {
		return map.keySet().stream().sorted().toList();
	}

	private Set<IcfgLocation> collectReachableFromEntries() {
		final Set<IcfgLocation> reachableFromEntries = new LinkedHashSet<>();
		new IcfgLocationIterator<>(mIcfg.getProcedureEntryNodes().values()).asStream()
				.forEach(reachableFromEntries::add);
		return reachableFromEntries;
	}

	private boolean isFoundationalSplitEdge(final IcfgEdge edge, final Set<IProgramVar> excludedVars) {
		if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
			return true;
		}
		if (isDataRaceSelfCheckAssertNeedingInterference(edge)) {
			return true;
		}
		if (excludedVars.isEmpty()) {
			return InterferenceUtils.modifiesGlobals(edge.getTransformula());
		}
		return !excludedVars.containsAll(InterferenceUtils.getChangedGlobals(edge.getTransformula()));
	}

	private boolean isDataRaceSelfCheckAssertNeedingInterference(final IcfgEdge edge) {
		return DataRaceAnnotation.getAnnotation(edge) != null;
	}

	private IcfgLocation find(final Map<IcfgLocation, IcfgLocation> parent, final IcfgLocation location) {
		final IcfgLocation currentParent = parent.get(location);
		if (currentParent == null || currentParent.equals(location)) {
			return location;
		}
		final IcfgLocation root = find(parent, currentParent);
		parent.put(location, root);
		return root;
	}

	private void union(final Map<IcfgLocation, IcfgLocation> parent, final IcfgLocation left,
			final IcfgLocation right) {
		final IcfgLocation leftRoot = find(parent, left);
		final IcfgLocation rightRoot = find(parent, right);
		if (!leftRoot.equals(rightRoot)) {
			parent.put(rightRoot, leftRoot);
		}
	}

	private Set<IProgramVar> getGuardVars(final List<IcfgEdge> outgoing, final boolean fullyPrecise) {
		if (fullyPrecise) {
			return getGuardVarsStrict(outgoing);
		}
		final List<Term> guards = collectGuardTerms(outgoing);
		final Set<IProgramVar> allVars = new HashSet<>();
		for (final Term term : guards) {
			final Set<IProgramVar> freeVars = Arrays.stream(term.getFreeVars()).filter(mTermToGlobalMap::containsKey)
					.map(mTermToGlobalMap::get).collect(Collectors.toSet());
			allVars.addAll(freeVars);
		}
		return allVars;
	}

	private Set<IProgramVar> getGuardVarsStrict(final List<IcfgEdge> outgoing) {
		final List<Term> guards = collectGuardTerms(outgoing);
		if (guards.isEmpty()) {
			return Set.of();
		}
		final Set<IProgramVar> freeVars = new HashSet<>();
		for (final Term guard : guards) {
			final Term simplified = SmtUtils.simplify(mManagedScript, guard, mServices,
					SimplificationTechnique.POLY_PAC);
			if (SmtUtils.isTrueLiteral(simplified) || SmtUtils.isFalseLiteral(simplified)) {
				continue;
			}
			Arrays.stream(simplified.getFreeVars()).filter(mTermToGlobalMap::containsKey).map(mTermToGlobalMap::get)
					.forEach(freeVars::add);
		}
		return freeVars;
	}

	private boolean shouldDifferentiate(final List<IcfgEdge> outgoing, final boolean fullyPrecise) {
		if (fullyPrecise) {
			return shouldDifferentiateStrict(outgoing);
		}
		final List<Term> guards = collectGuardTerms(outgoing);
		for (final Term term : guards) {
			if (Arrays.stream(term.getFreeVars()).anyMatch(mTermToGlobalMap::containsKey)) {
				return true;
			}
		}
		return false;
	}

	private boolean shouldDifferentiateStrict(final List<IcfgEdge> outgoing) {
		return !getGuardVarsStrict(outgoing).isEmpty();
	}

	private List<Term> collectGuardTerms(final List<IcfgEdge> outgoing) {
		return outgoing.stream().map(IcfgEdge::getTransformula).filter(tf -> tf != null)
				.map(tf -> TransFormulaUtils.computeGuardTerm(mServices, mManagedScript, tf, false)).toList();
	}
}
