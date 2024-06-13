/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * An Empire annotation. Can serve as proof of the program's correctness.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of program statements
 */
public class EmpireAnnotation<PLACE> {
	private final Set<Pair<Territory<PLACE>, IPredicate>> mEmpire;

	/**
	 * Construct the Empire Annotation with given Territories and Law
	 *
	 * @param territoryLawMap
	 *            Map from Territory to corresponding IPredicate Law object
	 */
	public EmpireAnnotation(final Set<Pair<Territory<PLACE>, IPredicate>> territoryLawPairs) {
		mEmpire = territoryLawPairs;
	}

	public EmpireAnnotation(final Map<Territory<PLACE>, IPredicate> lawMap) {
		mEmpire = lawMap.entrySet().stream().map(e -> new Pair<Territory<PLACE>, IPredicate>(e.getKey(), e.getValue()))
				.collect(Collectors.toSet());
	}

	/**
	 * Get all Regions contained in the Empire.
	 *
	 * @return Set of Regions in Empire
	 */
	public Set<Region<PLACE>> getColony() {
		final Set<Region<PLACE>> colony =
				mEmpire.stream().flatMap(p -> p.getFirst().getRegions().stream()).collect(Collectors.toSet());
		return colony;
	}

	public Set<Territory<PLACE>> getTerritories() {
		return Collections.unmodifiableSet(mEmpire.stream().map(p -> p.getFirst()).collect(Collectors.toSet()));
	}

	/**
	 * Get all regions of the Empire which are not in territory and which don't overlap with any of the territory's
	 * regions
	 *
	 * @param territory
	 *            Territory to determine the outlander for
	 * @return Outlander of the Empire wrt. territory
	 */
	public Set<Region<PLACE>> getOutlanderRegions(final Territory<PLACE> territory) {
		final Set<Region<PLACE>> outRegions = DataStructureUtils.difference(getColony(), territory.getRegions());
		final Set<Region<PLACE>> outlanderRegions = new HashSet<>();
		final Set<PLACE> places = territory.getPlaces();
		for (final Region<PLACE> region : outRegions) {
			if (DataStructureUtils.haveEmptyIntersection(places, region.getPlaces())) {
				outlanderRegions.add(region);
			}
		}
		return outlanderRegions;
	}

	/**
	 * Return the Law corresponding to territory.
	 *
	 * @param territory
	 *            Territory of which the Law should be returned.
	 * @return Law corresponding to territory.
	 */
	public Set<IPredicate> getLawSet(final Territory<PLACE> territory) {
		return mEmpire.stream().filter(p -> p.getFirst().equals(territory)).map(p -> p.getSecond())
				.collect(Collectors.toSet());
	}

	/**
	 * Return the Set of all Territories of the Empire that contain the given Marking in its treaty.
	 *
	 * @param marking
	 * @return Set of Territories containing the Marking
	 */
	public Set<Pair<Territory<PLACE>, IPredicate>> getMarkingTerritories(final Marking<PLACE> marking) {
		return mEmpire.stream().filter(p -> p.getFirst().containsMarking(marking)).collect(Collectors.toSet());
	}

	/**
	 * Determine all successor (territory, law)-pairs wrt. a territory and transition for given bystanders and successor
	 * places of a transition. Successor territories only contain all bystander regions and for each successor place one
	 * region that contains the place.
	 *
	 * @param bystanders
	 *            Set of regions of the predecessor territory that do not contain any predecessor place of the
	 *            transition.
	 * @param successorPlaces
	 *            Successor places of the transition
	 * @return Set of all successor (territory, law)-pairs
	 */
	public Set<Pair<Territory<PLACE>, IPredicate>> getSuccessorPairs(final Set<Region<PLACE>> bystanders,
			final Set<PLACE> successorPlaces) {
		final var result = new HashSet<Pair<Territory<PLACE>, IPredicate>>();
		for (final Pair<Territory<PLACE>, IPredicate> pair : mEmpire) {
			final var territory = pair.getFirst();
			if (!territory.getRegions().containsAll(bystanders)
					|| !territory.getPlaces().containsAll(successorPlaces)) {
				continue;
			}
			final var potentialSuccessors = DataStructureUtils.difference(territory.getRegions(), bystanders).stream()
					.collect(Collectors.toSet());
			if (potentialSuccessors.size() != successorPlaces.size()) {
				continue;
			}
			var discard = false;
			for (final PLACE succPlace : successorPlaces) {
				final var succRegions =
						potentialSuccessors.stream().filter(r -> r.contains(succPlace)).collect(Collectors.toSet());
				if (succRegions.size() != 1) {
					discard = true;
					break;
				}
				potentialSuccessors.removeAll(succRegions);
			}
			if (!discard) {
				result.add(pair);
			}
		}
		return result;
	}

	public Set<Pair<Territory<PLACE>, IPredicate>> getEmpire() {
		return mEmpire;
	}

	/**
	 * Get the size of the Empire i.e. number of Territories in the Empire.
	 *
	 * @return Number of Territories
	 */
	public final long getEmpireSize() {
		return mEmpire.size();
	}

	public final int getRegionCount() {
		return getColony().size();
	}

	/**
	 * Get the size of the Law i.e. sum of all formulae.
	 *
	 * @return Size of the law as long.
	 */
	public final long getLawSize() {
		final DAGSize sizeComputation = new DAGSize();
		final long size =
				mEmpire.stream().collect(Collectors.summingLong(x -> sizeComputation.size(x.getSecond().getFormula())));
		return size;
	}

	/**
	 * Get the sum of Law size and Empire size
	 *
	 * @return Empire annotation size as long
	 */
	public final long getAnnotationSize() {
		return getEmpireSize() + getLawSize();
	}

	@Override
	public String toString() {
		if (mEmpire.isEmpty()) {
			return "[empty empire]";
		}
		final int keyLen = mEmpire.stream().map(Object::toString).mapToInt(String::length).max().getAsInt();
		final var sb = new StringBuilder();
		for (final var entry : mEmpire) {
			sb.append('\t');
			sb.append(String.format("%-" + keyLen + "s", entry.getKey()));
			sb.append("  :  ");
			sb.append(entry.getValue());
			sb.append('\n');
		}
		return sb.toString();
	}
}
