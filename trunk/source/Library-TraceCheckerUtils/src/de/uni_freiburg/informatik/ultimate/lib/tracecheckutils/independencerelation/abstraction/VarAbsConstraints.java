/*
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.independencerelation.abstraction;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.CanonicalLatticeForMaps;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PowersetLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.UpsideDownLattice;

public class VarAbsConstraints<L extends IAction> {
	private final Map<L, Set<IProgramVar>> mInConstr;
	private final Map<L, Set<IProgramVar>> mOutConstr;

	public VarAbsConstraints(final Map<L, Set<IProgramVar>> in, final Map<L, Set<IProgramVar>> out) {
		mInConstr = in;
		mOutConstr = out;
	}

	public Set<IProgramVar> getInConstraints(final L letter) {
		if (mInConstr.containsKey(letter)) {
			return Collections.unmodifiableSet(mInConstr.get(letter));
		}
		return Collections.emptySet();
	}

	public Set<IProgramVar> getOutConstraints(final L letter) {
		if (mOutConstr.containsKey(letter)) {
			return Collections.unmodifiableSet(mOutConstr.get(letter));
		}
		return Collections.emptySet();
	}

	/**
	 * Creates a copy of this instance, where the constraints for the given letter have been extended with the given
	 * sets of variables.
	 *
	 * @param letter
	 *            The letter whose constraints shall be changed. Constraints for all other letters remain unchanged.
	 * @param additionalInConstraints
	 *            Additional variables to add to the input constraints for the given letter.
	 * @param additionalOutConstraints
	 *            Additional variables to add to the output constraints for the given letter.
	 * @return the modified copy
	 */
	public VarAbsConstraints<L> withExtendedConstraints(final L letter, final Set<IProgramVar> additionalInConstraints,
			final Set<IProgramVar> additionalOutConstraints) {
		// We make shallow copies of the maps here. This is ok, because the original map and its values will never be
		// mutated, and the copy will only be mutated in this method (replacing a value, not mutating the old value).

		final Map<L, Set<IProgramVar>> nInConstr = new HashMap<>(mInConstr);
		nInConstr.merge(letter, additionalInConstraints, DataStructureUtils::union);

		final Map<L, Set<IProgramVar>> nOutConstr = new HashMap<>(mOutConstr);
		nOutConstr.merge(letter, additionalOutConstraints, DataStructureUtils::union);

		return new VarAbsConstraints<>(nInConstr, nOutConstr);
	}

	@Override
	public int hashCode() {
		// TODO consider caching this
		return Objects.hash(mInConstr, mOutConstr);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final VarAbsConstraints other = (VarAbsConstraints) obj;
		return Objects.equals(mInConstr, other.mInConstr) && Objects.equals(mOutConstr, other.mOutConstr);
	}

	public static final class Lattice<L extends IAction> implements ILattice<VarAbsConstraints<L>> {
		private final VarAbsConstraints<L> mBottom;
		private final UpsideDownLattice<Map<L, Set<IProgramVar>>> mMapLattice;

		public Lattice(final Set<IProgramVar> allVars, final Set<L> allLetters) {
			mMapLattice =
					new UpsideDownLattice<>(new CanonicalLatticeForMaps<>(new PowersetLattice<>(allVars), allLetters));
			mBottom = new VarAbsConstraints<>(mMapLattice.getBottom(), mMapLattice.getBottom());
		}

		@Override
		public ComparisonResult compare(final VarAbsConstraints<L> o1, final VarAbsConstraints<L> o2) {
			return ComparisonResult.aggregate(mMapLattice.compare(o1.mInConstr, o2.mInConstr),
					mMapLattice.compare(o1.mOutConstr, o2.mOutConstr));
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
			return new VarAbsConstraints<>(mMapLattice.supremum(h1.mInConstr, h2.mInConstr),
					mMapLattice.supremum(h1.mOutConstr, h2.mOutConstr));
		}

		@Override
		public VarAbsConstraints<L> infimum(final VarAbsConstraints<L> h1, final VarAbsConstraints<L> h2) {
			// Look at commentary on supremum. infimum and supremum is flipped in this class. infimum is h1 OR h2
			return new VarAbsConstraints<>(mMapLattice.infimum(h1.mInConstr, h2.mInConstr),
					mMapLattice.infimum(h1.mOutConstr, h2.mOutConstr));
		}
	}
}