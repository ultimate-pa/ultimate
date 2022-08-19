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

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.LazyInt;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitSubSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.CanonicalLatticeForMaps;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.UpsideDownLattice;

/**
 * Represents constrained variables for individual statements. Used as abstraction levels by
 * {@link de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.SpecificVariableAbstraction}.
 *
 * @author Marcel Rogg
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of statements being constrained
 */
public class VarAbsConstraints<L extends IAction> {
	private final LazyInt mHash;
	private final Map<L, BitSubSet<IProgramVar>> mInConstr;
	private final Map<L, BitSubSet<IProgramVar>> mOutConstr;
	private final BitSubSet<IProgramVar> mEmpty;

	/**
	 * Constructor.
	 *
	 * Use with care! The given maps as well as all sets stored within them are expected to never be modified! In many
	 * cases, it is better to use the methods {@link Lattice#getBottom()}, {@link Lattice#getTop()} and
	 * {{@link #withModifiedConstraints(IAction, Set, Set)} to create new constraints.
	 *
	 * @param in
	 *            maps letters to the set of constrained inVars
	 * @param out
	 *            maps letters to the set of constrained outVars
	 */
	VarAbsConstraints(final Map<L, BitSubSet<IProgramVar>> in, final Map<L, BitSubSet<IProgramVar>> out,
			final BitSubSet<IProgramVar> empty) {
		mInConstr = in;
		mOutConstr = out;
		mHash = new LazyInt(() -> HashUtils.hashJenkins(17, mInConstr, mOutConstr));

		assert empty.isEmpty();
		mEmpty = empty;
	}

	/**
	 * Returns an (unmodifiable) view of a letter's constrained inVars.
	 */
	public BitSubSet<IProgramVar> getInConstraints(final L letter) {
		if (mInConstr.containsKey(letter)) {
			return mInConstr.get(letter);
		}
		return mEmpty;
	}

	/**
	 * Returns an (unmodifiable) view of a letter's constrained outVars.
	 */
	public BitSubSet<IProgramVar> getOutConstraints(final L letter) {
		if (mOutConstr.containsKey(letter)) {
			return mOutConstr.get(letter);
		}
		return mEmpty;
	}

	/**
	 * Creates a copy of this instance, where the constraints for the given letter have been replaced with the given
	 * sets of variables.
	 *
	 * @param letter
	 *            The letter whose constraints shall be changed. Constraints for all other letters remain unchanged.
	 * @param inConstraints
	 *            Input constraints for the given letter.
	 * @param outConstraints
	 *            Output constraints for the given letter.
	 * @return the modified copy
	 */
	public VarAbsConstraints<L> withModifiedConstraints(final L letter, final BitSubSet<IProgramVar> inConstraints,
			final BitSubSet<IProgramVar> outConstraints) {
		// We make shallow copies of the maps here. This is ok, because the maps' values are immutable, and the copy
		// will only be mutated in this method (replacing a value, not mutating the old value).

		final Map<L, BitSubSet<IProgramVar>> nInConstr = new HashMap<>(mInConstr);
		nInConstr.put(letter, inConstraints);

		final Map<L, BitSubSet<IProgramVar>> nOutConstr = new HashMap<>(mOutConstr);
		nOutConstr.put(letter, outConstraints);

		return new VarAbsConstraints<>(nInConstr, nOutConstr, mEmpty);
	}

	@Override
	public int hashCode() {
		return mHash.get();
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
		final VarAbsConstraints<L> other = (VarAbsConstraints<L>) obj;
		return Objects.equals(mInConstr, other.mInConstr) && Objects.equals(mOutConstr, other.mOutConstr);
	}

	/**
	 * The natural lattice structure for {@link VarAbsConstraints}.
	 *
	 * The ordering implemented here follows the idea of abstraction levels: A smaller {@link VarAbsConstraints}
	 * instance represents a lower abstraction level, i.e., it is <em>more</em> constraining.
	 *
	 * @param <L>
	 *            The type of constrained letters
	 */
	public static final class Lattice<L extends IAction> implements ILattice<VarAbsConstraints<L>> {
		private final BitSubSet.Factory<IProgramVar> mFactory;
		private final UpsideDownLattice<Map<L, BitSubSet<IProgramVar>>> mMapLattice;
		private final VarAbsConstraints<L> mBottom;

		/**
		 * Creates a new lattice for {@link VarAbsConstraints} of a specific program.
		 *
		 * @param allLetters
		 *            The set of all statements occurring in the program
		 * @param factory
		 *            Used to create and compare values
		 */
		public Lattice(final Set<L> allLetters, final BitSubSet.Factory<IProgramVar> factory) {
			mFactory = factory;
			mMapLattice = new UpsideDownLattice<>(new CanonicalLatticeForMaps<>(factory, allLetters));
			mBottom = new VarAbsConstraints<>(mMapLattice.getBottom(), mMapLattice.getBottom(), factory.empty());
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
			return new VarAbsConstraints<>(Collections.emptyMap(), Collections.emptyMap(), mFactory.empty());
		}

		@Override
		public VarAbsConstraints<L> supremum(final VarAbsConstraints<L> h1, final VarAbsConstraints<L> h2) {
			// the supremum (h1 OR h2) should usually be a Object with all the InConstraints and all the OutConstraints.
			// Since we have to think inversely, it should be the Object with the Cut of all Constraints (h1 AND h2)
			return new VarAbsConstraints<>(mMapLattice.supremum(h1.mInConstr, h2.mInConstr),
					mMapLattice.supremum(h1.mOutConstr, h2.mOutConstr), mFactory.empty());
		}

		@Override
		public VarAbsConstraints<L> infimum(final VarAbsConstraints<L> h1, final VarAbsConstraints<L> h2) {
			// Look at commentary on supremum. infimum and supremum is flipped in this class. infimum is h1 OR h2
			return new VarAbsConstraints<>(mMapLattice.infimum(h1.mInConstr, h2.mInConstr),
					mMapLattice.infimum(h1.mOutConstr, h2.mOutConstr), mFactory.empty());
		}
	}
}
