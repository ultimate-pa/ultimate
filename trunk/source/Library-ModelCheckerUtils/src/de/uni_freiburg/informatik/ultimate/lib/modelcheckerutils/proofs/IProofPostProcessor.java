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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.proofs;

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Post-processes a proof artifact of some kind, resulting in a new proof artifact. This post-processing may for
 * instance be intended to accommodate a transformation of the program whose correctness is proven by the proof, or to
 * implement a change of proof format, or both.
 *
 * An instance of this interface is always bound to a specific pair of an original program and a transformed program
 * (which may be equal, if no program transformation took place). These programs should not change, and are typically
 * provided to the constructor. If a transformation took place, additional information may also be provided to the
 * constructor, and be used to implement the post-processing.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <INPROGRAM>
 *            The type of program for which a proof is provided as input to the post processor
 * @param <INPROOF>
 *            The type of proof which is provided as input to the post processor
 * @param <OUTPROGRAM>
 *            The type of program for which this instance provides proofs
 * @param <OUTPROOF>
 *            The type of proof resulting from the post-processing
 */
public interface IProofPostProcessor<INPROGRAM, INPROOF, OUTPROGRAM, OUTPROOF> {
	OUTPROGRAM getOriginalProgram();

	INPROGRAM getTransformedProgram();

	/**
	 * Given a proof for {@link #getTransformedProgram()}, computes a proof for {@link #getOriginalProgram()}.
	 *
	 * @param proof
	 *            the given input proof
	 * @return the post-processed proof
	 */
	OUTPROOF processProof(INPROOF proof);

	IStatisticsDataProvider getStatistics();
}
