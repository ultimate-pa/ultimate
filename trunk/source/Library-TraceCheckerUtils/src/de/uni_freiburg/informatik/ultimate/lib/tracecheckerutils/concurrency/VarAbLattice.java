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

import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;

public class VarAbLattice<L extends IAction> implements ILattice<VarAbsConstraints<L>> {
	ILattice<Set<IProgramVar>> mLattice;

	// This lattice Should be an UpsideDownLattice of a Powersetlattice
	public VarAbLattice(final ILattice<Set<IProgramVar>> lattice) {
		mLattice = lattice;

	}

	@Override
	public ComparisonResult compare(final VarAbsConstraints<L> o1, final VarAbsConstraints<L> o2) {

		return ComparisonResult.aggregate(compareMaps(o1.getCopyOfInContraintsMap(), o2.getCopyOfInContraintsMap()),
				compareMaps(o1.getCopyOfOutContraintsMap(), o2.getCopyOfOutContraintsMap()));
	}

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

	@Override
	public VarAbsConstraints<L> getBottom() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarAbsConstraints<L> getTop() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarAbsConstraints<L> supremum(final VarAbsConstraints<L> h1, final VarAbsConstraints<L> h2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public VarAbsConstraints<L> infimum(final VarAbsConstraints<L> h1, final VarAbsConstraints<L> h2) {
		// TODO Auto-generated method stub
		return null;
	}

}
