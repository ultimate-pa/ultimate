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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * An Empire annotation. Can serve as proof of the program's correctness.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of program statements
 * @param <LETTER>
 *            The type of places in the Petri program
 */
public class EmpireAnnotation<PLACE, LETTER> {
	Set<Territory<PLACE, LETTER>> mEmpire;
	HashMap<Territory<PLACE, LETTER>, TerritoryLaw<PLACE, LETTER>> mLaw;

	/**
	 * Construct the Empire Annotation with given Territories and Law
	 *
	 * @param territoryLawMap
	 *            Map from Territory to corresponding TerritoryLaw object
	 */
	public EmpireAnnotation(final HashMap<Territory<PLACE, LETTER>, TerritoryLaw<PLACE, LETTER>> territoryLawMap) {
		mEmpire = territoryLawMap.keySet();
		mLaw = territoryLawMap;
	}

	public Set<Region<PLACE, LETTER>> getColony() {
		final Set<Region<PLACE, LETTER>> colony =
				mEmpire.stream().flatMap(t -> t.getRegions().stream()).collect(Collectors.toSet());
		return colony;
	}

	public Set<Territory<PLACE, LETTER>> getTerritories() {
		return mEmpire;
	}

	/**
	 * Return the Law corresponding to territory.
	 *
	 * @param territory
	 *            Territory of which the Law should be returned.
	 * @return Law corresponding to territory.
	 */
	public IPredicate getLaw(final Territory<PLACE, LETTER> territory) {
		return mLaw.get(territory).getLaw();
	}

	/**
	 * Get the whole Law Hashtable which contains all (Territory, Law) pairs.
	 *
	 * @return Law Hashtable
	 */
	public Map<Territory<PLACE, LETTER>, TerritoryLaw<PLACE, LETTER>> getLaw() {
		return mLaw;
	}

	/**
	 * Get the size of the Empire i.e. number of Territories in the Empire.
	 *
	 * @return Number of Territories
	 */
	public final long getEmpireSize() {
		final long size = mEmpire.size();
		return size;
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
				.collect(Collectors.summingLong(x -> sizeComputation.size(x.getValue().getLaw().getFormula())));
		return size;
	}

	/**
	 * Get a List containing the sorted numbers of Regions for all Territories.
	 *
	 * @return Sorted List containing the numbers of Regions for all Territories.
	 */
	public List<Integer> getRegionPerTerritory() {
		final List<Integer> regionPerTerritory = new ArrayList<>();
		for (final Territory<PLACE, LETTER> territory : mEmpire) {
			regionPerTerritory.add(territory.getRegions().size());
		}
		regionPerTerritory.sort(null);
		return regionPerTerritory;
	}

	/**
	 * Get the sum of Law size and Empire size
	 *
	 * @return Empire annotation size as long
	 */
	public final long getAnnotationSize() {
		return getEmpireSize() + getLawSize();
	}
}
