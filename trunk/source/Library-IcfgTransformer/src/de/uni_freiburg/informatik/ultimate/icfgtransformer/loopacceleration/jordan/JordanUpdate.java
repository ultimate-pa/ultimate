/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * This class represents a linear update by a list of Jordan decompositions.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class JordanUpdate {
	public enum JordanTransformationStatus {
		SUCCESS,
		/**
		 * We support the transformation to JNF only if each eigenvalue is either -1,0 or 1.
		 */
		UNSUPPORTED_EIGENVALUES
	};

	private final JordanUpdate.JordanTransformationStatus mStatus;
	private final QuadraticMatrix mJnf;
	private final RationalMatrix mModal;
	private final RationalMatrix mInverseModal;
	/**
	 * Contains triple (ev, bs, occ) if there are exactly occ Jordan blocks of size bs for eigenvalue ev.
	 */
	private final NestedMap2<Integer, Integer, Integer> mJordanBlockSizes;

	public JordanUpdate(final JordanUpdate.JordanTransformationStatus status, final QuadraticMatrix jnf,
			final RationalMatrix modal, final RationalMatrix inverseModal,
			final NestedMap2<Integer, Integer, Integer> jordanBlockSizes) {
		super();
		assert (status == JordanTransformationStatus.SUCCESS) ^ (jnf == null) : "provide JNF iff success";
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

	public JordanUpdate.JordanTransformationStatus getStatus() {
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