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

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class HeuristicLocationAbstraction<LOC extends IcfgLocation> {
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final IIcfg<LOC> mIcfg;
	private final Set<IProgramNonOldVar> mGlobals;
	private final Map<TermVariable, IProgramVar> mTermToGlobalMap;
	private final IUltimateServiceProvider mServices;
	private final Map<LOC, Integer> mMutexVarSplitMapWithExitMarked;
	private final Map<LOC, Integer> mMutexVarSplitMapWithAllVarLinesMarked;

	@SuppressWarnings("unchecked")
	public HeuristicLocationAbstraction(final IUltimateServiceProvider services, final IIcfg<? extends LOC> icfg) {
		mManagedScript = icfg.getCfgSmtToolkit().getManagedScript();
		mScript = mManagedScript.getScript();
		mIcfg = (IIcfg<LOC>) icfg;
		mGlobals = mIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals();
		mTermToGlobalMap = mGlobals.stream().collect(Collectors.toMap(IProgramVar::getTermVariable, v -> v));
		mServices = services;
		mMutexVarSplitMapWithExitMarked = threePhaseMutexSplitting();
		mMutexVarSplitMapWithAllVarLinesMarked = splitAtGuardsAndWrites(computeFoundationalBaseMapping());
	}

	public StaticAbstractLocationMap<LOC> entryExitSplitting() {
		return new StaticAbstractLocationMap<>(this::entryExitMarked, mIcfg);
	}

	public StaticAbstractLocationMap<LOC> allVarOccurrencesSplit() {
		return new StaticAbstractLocationMap<>(this::allVarOccurrencesMarked, mIcfg);
	}

	private int entryExitMarked(final LOC loc) {
		return mMutexVarSplitMapWithExitMarked.get(loc);
	}

	private int allVarOccurrencesMarked(final LOC loc) {
		return mMutexVarSplitMapWithAllVarLinesMarked.get(loc);
	}

	private Map<LOC, Set<IProgramVar>> computeMutexVars(final boolean fullyPrecise) {
		final Map<LOC, Set<IProgramVar>> mutexGuardToVarsMap = new HashMap<>();
		for (final LOC loc : collectReachableFromEntries()) {
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

	private Map<LOC, Integer> computeFoundationalBaseMapping() {
		final Set<LOC> reachableFromEntries = collectReachableFromEntries();
		final Map<LOC, LOC> parent = new HashMap<>();
		for (final LOC loc : reachableFromEntries) {
			parent.put(loc, loc);
		}

		for (final LOC source : reachableFromEntries) {
			final String procedure = source.getProcedure();
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (target == null || !procedure.equals(target.getProcedure()) || !parent.containsKey(target)) {
					continue;
				}
				if (!isFoundationalSplitEdge(edge)) {
					union(parent, source, castLocation(target));
				}
			}
		}

		final Map<String, Set<LOC>> locationsByProcedure = groupByProcedure(reachableFromEntries);
		final Map<LOC, Integer> result = new HashMap<>();
		for (final String procedure : sortedKeys(locationsByProcedure)) {
			assignProcedureComponentIds(procedure, locationsByProcedure.get(procedure), parent, result);
		}
		return result;
	}

	private void assignProcedureComponentIds(final String procedure, final Set<LOC> procedureLocations,
			final Map<LOC, LOC> parent, final Map<LOC, Integer> result) {
		if (procedureLocations == null || procedureLocations.isEmpty()) {
			return;
		}

		final LOC entry = castLocation(mIcfg.getProcedureEntryNodes().get(procedure));
		final LOC entryRep = entry != null && parent.containsKey(entry) ? find(parent, entry) : null;
		final Map<LOC, Integer> compToId = new HashMap<>();
		int nextId = 2;
		for (final LOC loc : orderedLocations(procedureLocations)) {
			final LOC rep = find(parent, loc);
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

	private Map<LOC, Integer> splitAtGuardsAndWrites(final Map<LOC, Integer> foundationalMap) {
		final Map<LOC, Integer> abstractLocationMapping = new HashMap<>(foundationalMap);
		final Map<LOC, Set<IProgramVar>> mutexGuardToVarsMap = computeMutexVars(false);
		if (mutexGuardToVarsMap.isEmpty()) {
			return abstractLocationMapping;
		}
		final Set<IProgramVar> relevantGuardVars = mutexGuardToVarsMap.values().stream().flatMap(Set::stream)
				.collect(Collectors.toSet());
		final Map<String, Set<LOC>> locationsByProcedure = groupByProcedure(foundationalMap.keySet());
		for (final String procedure : sortedKeys(locationsByProcedure)) {
			final Set<LOC> procedureLocations = locationsByProcedure.get(procedure);
			if (procedureLocations == null || procedureLocations.isEmpty()) {
				continue;
			}
			int nextFreshId = nextFreshIdForProcedure(procedureLocations, abstractLocationMapping);
			for (final LOC loc : orderedLocationsInProcedureFlow(procedure, procedureLocations)) {
				if (!mutexGuardToVarsMap.containsKey(loc) && !writesRelevantGuardVar(loc, relevantGuardVars)) {
					continue;
				}
				abstractLocationMapping.put(loc, nextFreshId);
				nextFreshId++;
			}
		}
		return abstractLocationMapping;
	}

	private Map<LOC, Integer> threePhaseMutexSplitting() {
		final Map<LOC, Integer> result = singletonPerProcedureMapping();
		final Map<LOC, Set<IProgramVar>> mutexGuardToVarsMap = computeMutexVars(true);
		if (mutexGuardToVarsMap.isEmpty()) {
			return result;
		}

		final Map<String, Set<LOC>> locationsByProcedure = groupByProcedure(result.keySet());
		for (final String procedure : sortedKeys(locationsByProcedure)) {
			final Set<LOC> procedureLocations = locationsByProcedure.get(procedure);
			if (procedureLocations == null || procedureLocations.isEmpty()) {
				continue;
			}
			final List<LOC> ordered = orderedLocationsInProcedureFlow(procedure, procedureLocations);
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

	private int firstMutexInteractionIndex(final List<LOC> ordered,
			final Map<LOC, Set<IProgramVar>> mutexGuardToVarsMap, final Set<IProgramVar> guardVars) {
		int firstGuard = -1;
		int firstWrite = -1;
		for (int i = 0; i < ordered.size(); i++) {
			final LOC loc = ordered.get(i);
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

	private int lastGuardVarWriteIndex(final List<LOC> ordered, final Set<IProgramVar> guardVars) {
		int lastWrite = -1;
		for (int i = 0; i < ordered.size(); i++) {
			if (writesAnyOf(ordered.get(i), guardVars)) {
				lastWrite = i;
			}
		}
		return lastWrite;
	}

	private boolean writesAnyOf(final LOC loc, final Set<IProgramVar> vars) {
		if (vars.isEmpty()) {
			return false;
		}
		for (final IcfgEdge edge : loc.getOutgoingEdges()) {
			if (edge.getTransformula() == null) {
				continue;
			}
			if (edge.getTransformula().getAssignedVars().stream().anyMatch(vars::contains)) {
				return true;
			}
		}
		return false;
	}

	private Map<LOC, Integer> singletonPerProcedureMapping() {
		final Map<LOC, Integer> result = new HashMap<>();
		for (final LOC loc : collectReachableFromEntries()) {
			result.put(loc, 1);
		}
		return result;
	}

	private int nextFreshIdForProcedure(final Set<LOC> procedureLocations, final Map<LOC, Integer> mapping) {
		return procedureLocations.stream().map(mapping::get).filter(id -> id != null).max(Integer::compareTo).orElse(0)
				+ 1;
	}

	private boolean writesRelevantGuardVar(final LOC loc, final Set<IProgramVar> relevantGuardVars) {
		if (relevantGuardVars.isEmpty()) {
			return false;
		}
		for (final IcfgEdge edge : loc.getOutgoingEdges()) {
			if (edge.getTransformula() == null) {
				continue;
			}
			final boolean writesRelevantVar = edge.getTransformula().getAssignedVars().stream()
					.anyMatch(relevantGuardVars::contains);
			if (writesRelevantVar) {
				return true;
			}
		}
		return false;
	}

	private Map<String, Set<LOC>> groupByProcedure(final Set<LOC> locations) {
		final Map<String, Set<LOC>> locationsByProcedure = new HashMap<>();
		for (final LOC loc : locations) {
			locationsByProcedure.computeIfAbsent(loc.getProcedure(), ignored -> new LinkedHashSet<>()).add(loc);
		}
		return locationsByProcedure;
	}

	private List<LOC> orderedLocationsInProcedureFlow(final String procedure, final Set<LOC> procedureLocations) {
		final LOC entry = castLocation(mIcfg.getProcedureEntryNodes().get(procedure));
		if (entry == null) {
			return orderedLocations(procedureLocations);
		}
		final LinkedHashSet<LOC> ordered = new LinkedHashSet<>();
		final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(entry);
		while (iter.hasNext()) {
			final LOC loc = iter.next();
			if (procedure.equals(loc.getProcedure()) && procedureLocations.contains(loc)) {
				ordered.add(loc);
			}
		}
		ordered.addAll(orderedLocations(procedureLocations));
		return new ArrayList<>(ordered);
	}

	private List<LOC> orderedLocations(final Set<LOC> locations) {
		final List<LOC> ordered = new ArrayList<>(locations);
		ordered.sort(Comparator.comparing((final LOC loc) -> loc.getProcedure()).thenComparing(Object::toString));
		return ordered;
	}

	private List<String> sortedKeys(final Map<String, ?> map) {
		return map.keySet().stream().sorted().toList();
	}

	private Set<LOC> collectReachableFromEntries() {
		final Set<LOC> reachableFromEntries = new LinkedHashSet<>();
		new IcfgLocationIterator<>(mIcfg.getProcedureEntryNodes().values()).asStream()
				.forEach(reachableFromEntries::add);
		return reachableFromEntries;
	}

	private boolean isFoundationalSplitEdge(final IcfgEdge edge) {
		if (edge.getTransformula() == null) {
			return false;
		}
		return edge.getTransformula().getAssignedVars().stream().anyMatch(IProgramVar::isGlobal);
	}

	@SuppressWarnings("unchecked")
	private LOC castLocation(final IcfgLocation location) {
		return (LOC) location;
	}

	private LOC find(final Map<LOC, LOC> parent, final LOC location) {
		final LOC currentParent = parent.get(location);
		if (currentParent == null || currentParent.equals(location)) {
			return location;
		}
		final LOC root = find(parent, currentParent);
		parent.put(location, root);
		return root;
	}

	private void union(final Map<LOC, LOC> parent, final LOC left, final LOC right) {
		final LOC leftRoot = find(parent, left);
		final LOC rightRoot = find(parent, right);
		if (!leftRoot.equals(rightRoot)) {
			parent.put(rightRoot, leftRoot);
		}
	}

	public Set<IProgramVar> getGuardVars(final List<IcfgEdge> outgoing, final boolean fullyPrecise) {
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

	public Set<IProgramVar> getGuardVarsStrict(final List<IcfgEdge> outgoing) {
		final List<Term> guards = collectGuardTerms(outgoing);
		if (guards.isEmpty()) {
			return Set.of();
		}
		final Set<IProgramVar> freeVars = new HashSet<>();
		for (final Term guard : guards) {
			// Keep guards separate; complementary guards can collapse to true
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

	public boolean shouldDifferentiate(final List<IcfgEdge> outgoing, final boolean fullyPrecise) {
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

	public boolean shouldDifferentiateStrict(final List<IcfgEdge> outgoing) {
		return !getGuardVarsStrict(outgoing).isEmpty();
	}

	private List<Term> collectGuardTerms(final List<IcfgEdge> outgoing) {
		return outgoing.stream().map(IcfgEdge::getTransformula).filter(tf -> tf != null)
				.map(tf -> TransFormulaUtils.computeGuardTerm(mServices, mManagedScript, tf, false)).toList();
	}
}
