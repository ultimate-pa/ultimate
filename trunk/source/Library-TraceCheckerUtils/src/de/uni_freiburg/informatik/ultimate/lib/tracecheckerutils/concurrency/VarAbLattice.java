/*
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.CanonicalLatticeForMaps;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PowersetLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.UpsideDownLattice;

public class VarAbLattice<L extends IAction> implements ILattice<VarAbsConstraints<L>> {
	Set<IProgramVar> mAllVars;
	Set<L> mAllLetters;
	VarAbsConstraints<L> mBottom;
	private UpsideDownLattice<Map<L, Set<IProgramVar>>> mMapLattice;
	

	// This lattice Should be an UpsideDownLattice of a Powersetlattice
	public VarAbLattice(final Set<IProgramVar> allVars, final Set<L> allLetters) {
		mAllVars = allVars;
		mAllLetters = allLetters;
		final Map<L, Set<IProgramVar>> inConstr = new HashMap<>();
		final Map<L, Set<IProgramVar>> outConstr = new HashMap<>();
		mMapLattice = new UpsideDownLattice<>(new CanonicalLatticeForMaps<>(new PowersetLattice<>(allVars)));

		for (final L l : mAllLetters) {
			inConstr.put(l, mAllVars);
			outConstr.put(l, mAllVars);
		}
		mBottom = new VarAbsConstraints<>(inConstr, outConstr);
	}

	@Override
	public ComparisonResult compare(final VarAbsConstraints<L> o1, final VarAbsConstraints<L> o2) {

		return ComparisonResult.aggregate(mMapLattice.compare(o1.getInContraintsMap(), o2.getInContraintsMap()),
				mMapLattice.compare(o1.getOutContraintsMap(), o2.getOutContraintsMap()));
	}
	
	/*

	public ComparisonResult compareMapsSameLetters(final Map<L, Set<IProgramVar>> m1,
			final Map<L, Set<IProgramVar>> m2) {
		boolean m2subsetm1 = true;
		boolean m1subsetm2 = true;
		for (final Entry<L, Set<IProgramVar>> en : m1.entrySet()) {
			if (en.getValue().containsAll(m2.get(en.getKey()))) {
				m2subsetm1 = false;
			}
			if (m2.get(en.getKey()).containsAll(en.getValue())) {
				m1subsetm2 = false;
			}
		}
		if (!m1subsetm2 && !m2subsetm1) {
			return ComparisonResult.INCOMPARABLE;
		} else if (m1subsetm2) {
			if (m2subsetm1) {
				return ComparisonResult.EQUAL;
			}
			return ComparisonResult.STRICTLY_GREATER;
		}
		// See reasoning; m1: L-> {x,y}, m2: L -> {x,y}; m1subsetm2 =false, m2subsetm1 = true; m1 strictly smaller
		// m2, since the more constraints the smaller
		return ComparisonResult.STRICTLY_SMALLER;
	}

	public boolean allSameSetsContainMoreElements(final Map<L, Set<IProgramVar>> m1,
			final Map<L, Set<IProgramVar>> m2) {
		for (final Entry<L, Set<IProgramVar>> en : m2.entrySet()) {
			if (!m1.get(en.getKey()).containsAll(en.getValue())) {
				return false;
			}
		}
		return true;
	}

	public ComparisonResult compareMaps(final Map<L, Set<IProgramVar>> m1, final Map<L, Set<IProgramVar>> m2) {
		// If m1 contains the same letters <L> as m1, only the set differs
		if (m1.keySet().equals(m2.keySet())) {
			return compareMapsSameLetters(m1, m2);
		}
		// If m1 contains more letters <L> that are constrained by the same Sets of ProgramVars -> m1 is strictly
		// smaller (if the sets of m1 contain same or more constraining vars)
		if (!m1.keySet().containsAll(m2.keySet()) && !m2.keySet().containsAll(m1.keySet())) {
			return ComparisonResult.INCOMPARABLE;
		}
		if (m1.keySet().containsAll(m2.keySet())) {
			return allSameSetsContainMoreElements(m1, m2) ? ComparisonResult.STRICTLY_SMALLER
					: ComparisonResult.INCOMPARABLE;

		}
		if (m2.keySet().containsAll(m1.keySet())) {
			return allSameSetsContainMoreElements(m2, m1) ? ComparisonResult.STRICTLY_GREATER
					: ComparisonResult.INCOMPARABLE;
		}
		return ComparisonResult.INCOMPARABLE;
	}
	*/

	@Override
	public VarAbsConstraints<L> getBottom() {

		return mBottom;
	}

	@Override
	public VarAbsConstraints<L> getTop() {
		// TODO Auto-generated method stub
		return new VarAbsConstraints<>(Collections.emptyMap(), Collections.emptyMap());
	}

	@Override
	public VarAbsConstraints<L> supremum(final VarAbsConstraints<L> h1, final VarAbsConstraints<L> h2) {
		// TODO Auto-generated method stub
		// the supremum (h1 OR h2) should usually be a Object with all the InConstraints and all the OutConstraints.
		// Since we have to think inversely, it should be the Object with the Cut of all Constraints (h1 AND h2)
		/* return new VarAbsConstraints<>(supremumMaps(h1.getInContraintsMap(), h2.getInContraintsMap()),
				supremumMaps(h1.getOutContraintsMap(), h2.getOutContraintsMap()));
		*/
		return new VarAbsConstraints<>(mMapLattice.supremum(new HashMap<>(h1.getInContraintsMap()), new HashMap<>(h2.getInContraintsMap())), 
				mMapLattice.supremum(new HashMap<>(h1.getOutContraintsMap()), new HashMap<>(h2.getOutContraintsMap())));

	}
	
	/*
	public Map<L, Set<IProgramVar>> supremumMaps(final Map<L, Set<IProgramVar>> m1, final Map<L, Set<IProgramVar>> m2) {
		// This Part is taken from /heavily inspired by CanonicalLatticeForMaps... Do I credit Dominik here; in the
		// Header? How?
		final Map<L, Set<IProgramVar>> smaller;
		final Map<L, Set<IProgramVar>> bigger;
		if (m1.size() < m2.size()) {
			smaller = m1;
			bigger = m2;
		} else {
			smaller = m2;
			bigger = m1;
		}
		final Map<L, Set<IProgramVar>> result = new HashMap<>();
		for (final Entry<L, Set<IProgramVar>> en : smaller.entrySet()) {
			if (bigger.containsKey(en.getKey())) {
				final Set<IProgramVar> value = new HashSet<>(en.getValue());
				value.removeAll(bigger.get(en.getKey()));
				result.put(en.getKey(), value);
			}
		}
		return result;
	}
	*/

	@Override
	// Look at commentary on supremum. infimum and supremum is flipped in this class. infimum is h1 OR h2
	public VarAbsConstraints<L> infimum(final VarAbsConstraints<L> h1, final VarAbsConstraints<L> h2) {
		return new VarAbsConstraints<>(mMapLattice.infimum(new HashMap<>(h1.getInContraintsMap()), new HashMap<>(h2.getInContraintsMap())),
				mMapLattice.infimum(new HashMap<>(h1.getOutContraintsMap()), new HashMap<>(h2.getOutContraintsMap())));
		
		
		
		/*
		final Map<L, Set<IProgramVar>> inResult = new HashMap<>(h1.getInContraintsMap());
		final Map<L, Set<IProgramVar>> OutResult = new HashMap<>(h1.getOutContraintsMap());
		// final VarAbsConstraints<L> inResult = new VarAbsConstraints<>(h1.getCopyOfInContraintsMap(),
		// h2.getCopyOfOutContraintsMap());
		for (final Entry<L, Set<IProgramVar>> en : h2.getInContraintsMap().entrySet()) {
			if (inResult.containsKey(en.getKey())) {
				inResult.get(en.getKey()).addAll(en.getValue());
			} else {
				inResult.put(en.getKey(), en.getValue());
			}
		}
		for (final Entry<L, Set<IProgramVar>> en : h2.getOutContraintsMap().entrySet()) {
			// result.addOutVars(en.getKey(), en.getValue());
			if (OutResult.containsKey(en.getKey())) {
				OutResult.get(en.getKey()).addAll(en.getValue());
			} else {
				OutResult.put(en.getKey(), en.getValue());
			}
		}
		return new VarAbsConstraints<>(inResult, OutResult);
		*/
	}

}
