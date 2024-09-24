/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs;

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * An interface for classes that compute some kind of proof artifact for a program.
 *
 * An instance of this interface is always bound to a specific program. This program should not change, and is typically
 * provided to the constructor.
 *
 * Beyond that, proof producers are typically stateful and may gather information necessary to compute a proof, e.g.
 * during verification of the program. The method {@link #isReadyToComputeProof()} can be used to determine if all
 * information to compute a proof has been collected. If so, invoking {@link #getOrComputeProof()} should produce the
 * desired proof.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <PROGRAM>
 *            The type of program for which a proof is produced
 * @param <PROOF>
 *            The type of proof which is produced
 */
public interface IProofProducer<PROGRAM, PROOF extends IProof> {
	/**
	 * Retrieves the (fixed) program for which this instance computes a proof.
	 *
	 * @return
	 */
	PROGRAM getProgram();

	/**
	 * Determines if the producer has all the necessary information available to compute a proof.
	 *
	 * @return true if a call to {@link #getOrComputeProof()} will succeed, false otherwise.
	 */
	boolean isReadyToComputeProof();

	/**
	 * Attempts to compute the proof artifact. If successful, the artifact must be cached and returned again on
	 * subsequent calls.
	 *
	 * @throws UnsupportedOperationException
	 *             If not all the necessary information to compute the proof is available.
	 *
	 * @return the computed proof artifact, if successful. If unsuccessful, an exception is thrown.
	 */
	PROOF getOrComputeProof();

	IStatisticsDataProvider getStatistics();
}
