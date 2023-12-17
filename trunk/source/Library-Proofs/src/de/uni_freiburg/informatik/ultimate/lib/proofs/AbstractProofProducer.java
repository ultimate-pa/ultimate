/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs;

/**
 * Base class for implementations of {@link IProofProducer}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <A>
 *            The type of abstraction for which a proof shall be produced (see {@link IProofProducer}).
 * @param <P>
 *            The type of proof that shall be produced (see {@link IProofProducer}).
 * @param <A0>
 *            The type of abstraction natively supported by the class that inherits from {@link AbstractProofProducer}.
 *            Proofs for other kinds of abstractions can be computed by post-processing.
 * @param <P0>
 *            The type of proof natively supported by the class that inherits from {@link AbstractProofProducer}. Proofs
 *            of other kinds can be computed by post-processing.
 */
public abstract class AbstractProofProducer<A, P, A0, P0> implements IProofProducer<A, P> {
	protected final A0 mProgram;
	protected final IProofPostProcessor<A0, P0, A, P> mPost;

	private P0 mInternalProof;
	private P mProof;

	protected AbstractProofProducer(final A0 program, final IProofPostProcessor<A0, P0, A, P> post) {
		mProgram = program;
		mPost = post;

		assert post.getTransformedProgram() == mProgram : "proof post processor program does not match";
	}

	@Override
	public final A getProgram() {
		return mPost.getOriginalProgram();
	}

	@Override
	public final P getOrComputeProof() {
		if (mProof == null) {
			mProof = mPost.processProof(getOrComputeInternalProof());
		}
		return mProof;
	}

	protected final P0 getOrComputeInternalProof() {
		if (mInternalProof == null) {
			mInternalProof = computeProof();
		}
		return mInternalProof;
	}

	protected abstract P0 computeProof();
}
