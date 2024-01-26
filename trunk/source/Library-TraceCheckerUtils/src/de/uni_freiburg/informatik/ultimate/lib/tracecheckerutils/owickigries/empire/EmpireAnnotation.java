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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * An Empire annotation. Can serve as proof of the program's correctness.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of program statements
 */
public class EmpireAnnotation<PLACE> {
	private final Map<Territory<PLACE>, IPredicate> mLaw;

	/**
	 * Construct the Empire Annotation with given Territories and Law
	 *
	 * @param territoryLawMap
	 *            Map from Territory to corresponding IPredicate Law object
	 */
	public EmpireAnnotation(final Map<Territory<PLACE>, IPredicate> territoryLawMap) {
		mLaw = territoryLawMap;
	}

	/**
	 * Get all Regions contained in the Empire.
	 *
	 * @return Set of Regions in Empire
	 */
	public Set<Region<PLACE>> getColony() {
		return mLaw.keySet().stream().flatMap(t -> t.getRegions().stream()).collect(Collectors.toSet());
	}

	public Set<Territory<PLACE>> getTerritories() {
		return Collections.unmodifiableSet(mLaw.keySet());
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
	public IPredicate getLaw(final Territory<PLACE> territory) {
		return mLaw.get(territory);
	}

	/**
	 * Get the whole Law Hashtable which contains all (Territory, Law) pairs.
	 *
	 * @return Law Hashtable
	 */
	public Map<Territory<PLACE>, IPredicate> getLaw() {
		return mLaw;
	}

	/**
	 * Get the size of the Empire i.e. number of Territories in the Empire.
	 *
	 * @return Number of Territories
	 */
	public final long getEmpireSize() {
		return mLaw.size();
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
		final long size = mLaw.entrySet().stream()
				.collect(Collectors.summingLong(x -> sizeComputation.size(x.getValue().getFormula())));
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
		if (mLaw.isEmpty()) {
			return "[empty empire]";
		}
		final int keyLen = mLaw.keySet().stream().map(Object::toString).mapToInt(String::length).max().getAsInt();
		final var sb = new StringBuilder();
		for (final var entry : mLaw.entrySet()) {
			sb.append('\t');
			sb.append(String.format("%-" + keyLen + "s", entry.getKey()));
			sb.append("  :  ");
			sb.append(entry.getValue());
			sb.append('\n');
		}
		return sb.toString();
	}
}
