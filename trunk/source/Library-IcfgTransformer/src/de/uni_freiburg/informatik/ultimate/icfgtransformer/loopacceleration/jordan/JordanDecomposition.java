/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Represents a decomposition of a {@link QuadraticMatrix} into a product of
 * three matrices M * J * M^{-1}, where J is in Jordan normal form and M is a
 * invertible matrix that we call modal matrix.
 * https://en.wikipedia.org/wiki/Jordan_normal_form
 *
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class JordanDecomposition {

	public enum JordanDecompositionStatus {
		SUCCESS,
		/**
		 * We support the transformation to JNF only if each eigenvalue is either -1,0 or 1.
		 */
		UNSUPPORTED_EIGENVALUES
	};

	private final JordanDecompositionStatus mStatus;
	private final QuadraticMatrix mJnf;
	private final RationalMatrix mModal;
	private final RationalMatrix mInverseModal;
	/**
	 * Contains triple (ev, bs, occ) if there are exactly occ Jordan blocks of size
	 * bs for eigenvalue ev.
	 */
	private final NestedMap2<Integer, Integer, Integer> mJordanBlockSizes;

	public JordanDecomposition(final JordanDecompositionStatus status, final QuadraticMatrix jnf,
			final RationalMatrix modal, final RationalMatrix inverseModal,
			final NestedMap2<Integer, Integer, Integer> jordanBlockSizes) {
		assert (status == JordanDecompositionStatus.SUCCESS) ^ (jnf == null) : "provide JNF iff success";
		assert (jnf == null) == (jordanBlockSizes == null) : "all or nothing";
		if (jordanBlockSizes != null) {
			assert jordanBlockSizes.keySet().stream()
					.allMatch(x -> x == -1 || x == 0 || x == 1) : "only supported eigenvalues as keys";
		}
		mStatus = status;
		mJnf = jnf;
		mModal = modal;
		mInverseModal = inverseModal;
		mJordanBlockSizes = jordanBlockSizes;
	}

	public JordanDecompositionStatus getStatus() {
		return mStatus;
	}

	public QuadraticMatrix getJnf() {
		return mJnf;
	}

	public RationalMatrix getModal() {
		return mModal;
	}

	public RationalMatrix getInverseModal() {
		return mInverseModal;
	}

	public NestedMap2<Integer, Integer, Integer> getJordanBlockSizes() {
		return mJordanBlockSizes;
	}

}