/*
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.CanonicalLatticeForMaps;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PowersetLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.UpsideDownLattice;

public class VarAbLattice<L extends IAction> implements ILattice<VarAbsConstraints<L>> {
	private final Set<L> mAllLetters;
	private final VarAbsConstraints<L> mBottom;
	private final UpsideDownLattice<Map<L, Set<IProgramVar>>> mMapLattice;

	public VarAbLattice(final Set<IProgramVar> allVars, final Set<L> allLetters) {
		mAllLetters = allLetters;
		mMapLattice = new UpsideDownLattice<>(new CanonicalLatticeForMaps<>(new PowersetLattice<>(allVars)));

		final Map<L, Set<IProgramVar>> inConstr = new HashMap<>();
		final Map<L, Set<IProgramVar>> outConstr = new HashMap<>();
		for (final L l : mAllLetters) {
			inConstr.put(l, allVars);
			outConstr.put(l, allVars);
		}
		mBottom = new VarAbsConstraints<>(inConstr, outConstr);
	}

	@Override
	public ComparisonResult compare(final VarAbsConstraints<L> o1, final VarAbsConstraints<L> o2) {
		return ComparisonResult.aggregate(mMapLattice.compare(o1.getInContraintsMap(), o2.getInContraintsMap()),
				mMapLattice.compare(o1.getOutContraintsMap(), o2.getOutContraintsMap()));
	}

	@Override
	public VarAbsConstraints<L> getBottom() {
		return mBottom;
	}

	@Override
	public VarAbsConstraints<L> getTop() {
		return new VarAbsConstraints<>(Collections.emptyMap(), Collections.emptyMap());
	}

	@Override
	public VarAbsConstraints<L> supremum(final VarAbsConstraints<L> h1, final VarAbsConstraints<L> h2) {
		// the supremum (h1 OR h2) should usually be a Object with all the InConstraints and all the OutConstraints.
		// Since we have to think inversely, it should be the Object with the Cut of all Constraints (h1 AND h2)
		return new VarAbsConstraints<>(mMapLattice.supremum(h1.getInContraintsMap(), h2.getInContraintsMap()),
				mMapLattice.supremum(h1.getOutContraintsMap(), h2.getOutContraintsMap()));
	}

	@Override
	public VarAbsConstraints<L> infimum(final VarAbsConstraints<L> h1, final VarAbsConstraints<L> h2) {
		// Look at commentary on supremum. infimum and supremum is flipped in this class. infimum is h1 OR h2
		return new VarAbsConstraints<>(mMapLattice.infimum(h1.getInContraintsMap(), h2.getInContraintsMap()),
				mMapLattice.infimum(h1.getOutContraintsMap(), h2.getOutContraintsMap()));
	}
}
