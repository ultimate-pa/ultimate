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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

final class ControlPartitioningHeuristics {
	private final ManagedScript mManagedScript;
	private final IIcfg<IcfgLocation> mIcfg;
	private final Map<TermVariable, IProgramVar> mTermToGlobalMap;
	private final IUltimateServiceProvider mServices;

	ControlPartitioningHeuristics(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg) {
		mManagedScript = icfg.getCfgSmtToolkit().getManagedScript();
		mIcfg = icfg;
		mTermToGlobalMap = mIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals().stream()
				.collect(Collectors.toMap(IProgramVar::getTermVariable, v -> v));
		mServices = services;
	}

	Map<IcfgLocation, Integer> splitAtNonLockGuardsAndWrites(final Set<IProgramVar> lockVars) {
		return splitAtGuardsAndWrites(computeFoundationalBaseMapping(lockVars), lockVars);
	}

	private Map<IcfgLocation, Set<IProgramVar>> computeGuardVars() {
		final Map<IcfgLocation, Set<IProgramVar>> guardVarsByLocation = new HashMap<>();
		for (final IcfgLocation loc : collectReachableFromEntries()) {
			final List<IcfgEdge> outgoing = loc.getOutgoingEdges();
			final Set<IProgramVar> guardVars = getGuardVars(outgoing);
			if (!guardVars.isEmpty()) {
				guardVarsByLocation.put(loc, guardVars);
			}
		}
		return guardVarsByLocation;
	}

	private Map<IcfgLocation, Integer> computeFoundationalBaseMapping(final Set<IProgramVar> lockVars) {
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
				if (!isFoundationalSplitEdge(edge, lockVars)) {
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
			final Set<IProgramVar> lockVars) {
		final Map<IcfgLocation, Integer> abstractLocationMapping = new HashMap<>(foundationalMap);
		final Map<IcfgLocation, Set<IProgramVar>> guardVarsByLocation = computeGuardVars();
		if (!lockVars.isEmpty()) {
			guardVarsByLocation.values().forEach(vars -> vars.removeAll(lockVars));
			guardVarsByLocation.values().removeIf(Set::isEmpty);
		}
		if (guardVarsByLocation.isEmpty()) {
			return abstractLocationMapping;
		}
		final Set<IProgramVar> relevantGuardVars = guardVarsByLocation.values().stream().flatMap(Set::stream)
				.collect(Collectors.toSet());
		final Map<String, Set<IcfgLocation>> locationsByProcedure = groupByProcedure(foundationalMap.keySet());
		for (final String procedure : sortedKeys(locationsByProcedure)) {
			final Set<IcfgLocation> procedureLocations = locationsByProcedure.get(procedure);
			if (procedureLocations == null || procedureLocations.isEmpty()) {
				continue;
			}
			int nextFreshId = nextFreshIdForProcedure(procedureLocations, abstractLocationMapping);
			for (final IcfgLocation loc : orderedLocationsInProcedureFlow(procedure, procedureLocations)) {
				if (!guardVarsByLocation.containsKey(loc) && !writesAnyOf(loc, relevantGuardVars)) {
					continue;
				}
				abstractLocationMapping.put(loc, nextFreshId);
				nextFreshId++;
			}
		}
		return abstractLocationMapping;
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

	private boolean isFoundationalSplitEdge(final IcfgEdge edge, final Set<IProgramVar> lockVars) {
		if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
			return true;
		}
		if (lockVars.isEmpty()) {
			return InterferenceUtils.referencesGlobals(edge.getTransformula());
		}
		return !lockVars.containsAll(InterferenceUtils.getReferencedGlobals(edge.getTransformula()));
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

	private Set<IProgramVar> getGuardVars(final List<IcfgEdge> outgoing) {
		final List<Term> guards = collectGuardTerms(outgoing);
		final Set<IProgramVar> allVars = new HashSet<>();
		for (final Term term : guards) {
			final Set<IProgramVar> freeVars = Arrays.stream(term.getFreeVars()).filter(mTermToGlobalMap::containsKey)
					.map(mTermToGlobalMap::get).collect(Collectors.toSet());
			allVars.addAll(freeVars);
		}
		return allVars;
	}

	private List<Term> collectGuardTerms(final List<IcfgEdge> outgoing) {
		return outgoing.stream().map(IcfgEdge::getTransformula).filter(tf -> tf != null)
				.map(tf -> TransFormulaUtils.computeGuardTerm(mServices, mManagedScript, tf, false)).toList();
	}
}
