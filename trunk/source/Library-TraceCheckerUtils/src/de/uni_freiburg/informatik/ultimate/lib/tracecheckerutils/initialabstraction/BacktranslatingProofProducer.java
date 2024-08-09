/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.IProof;
import de.uni_freiburg.informatik.ultimate.lib.proofs.IProofProducer;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Helper class that wraps a proof producer for an initial abstraction, and backtranslates the produced proof to a proof
 * for the original {@link IIcfg}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <INPROOF>
 *            The type of proof produced for the initial abstraction
 */
public class BacktranslatingProofProducer<INPROOF extends IProof>
		implements IProofProducer<IIcfg<IcfgLocation>, IProof> {
	private final IIcfg<IcfgLocation> mIcfg;
	private final IProofProducer<?, INPROOF> mUnderlying;
	private final Function<INPROOF, ? extends IProof> mBacktranslator;

	private IProof mBacktranslatedProof;

	public BacktranslatingProofProducer(final IIcfg<IcfgLocation> icfg, final IProofProducer<?, INPROOF> underlying,
			final Function<INPROOF, ? extends IProof> backtranslator) {
		mIcfg = icfg;
		mUnderlying = underlying;
		mBacktranslator = backtranslator;
	}

	@Override
	public IIcfg<IcfgLocation> getProgram() {
		return mIcfg;
	}

	@Override
	public boolean isReadyToComputeProof() {
		return mUnderlying.isReadyToComputeProof();
	}

	@Override
	public IProof getOrComputeProof() {
		if (mBacktranslatedProof == null) {
			final var proof = mUnderlying.getOrComputeProof();
			mBacktranslatedProof = mBacktranslator.apply(proof);
		}
		return mBacktranslatedProof;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mUnderlying.getStatistics();
	}
}
