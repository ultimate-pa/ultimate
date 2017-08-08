/*
 * Copyright (C) 2017 Ben Biesenbach (ben.biesenbach@gmx.de)
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * A {@link IIcfgTransformer} that accelerates the first loop if finds and creates a new accelerated {@link IIcfg}.
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Ben Biesenbach (Ben.Biesenbach@gmx.de)
 *
 */
public class IcfgLoopAcceleration<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	/**
	 * Different options for the loop acceleration
	 *
	 * @author Ben Biesenbach (Ben.Biesenbach@gmx.de)
	 *
	 */
	public enum LoopAccelerationOptions {
		/**
		 * If the {@link IIcfg} contains a loop that cannot be accelerated with a valid underapproximation, throw an
		 * exception.
		 */
		THROW_EXEPTION,

		/**
		 * If the acceleration contains an overapproximation (i.e., some variables had to be overapproximated with *),
		 * add the acceleration and mark it as overapproximation. If a loop can -- for some reason -- not be
		 * accelerated, just ignore it with a warning.
		 */
		MARK_AS_OVERAPPROX,

		/**
		 * Only add an acceleration if it is a valid underapproximation and ignore all other loops.
		 */
		DO_NOT_ACCELERATE
	}

	private final IIcfg<OUTLOC> mResultIcfg;

	/**
	 * Default constructor.
	 *
	 * @param logger
	 * @param originalIcfg
	 * @param outLocationClass
	 * @param funLocFac
	 * @param newIcfgIdentifier
	 * @param transformer
	 * @param backtranslationTracker
	 * @param services
	 * @param replacementVarFactory
	 * @param option
	 */
	public IcfgLoopAcceleration(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer,
			final IBacktranslationTracker backtranslationTracker, final IUltimateServiceProvider services,
			final LoopAccelerationOptions option) {
		mResultIcfg = accelerat(logger, originalIcfg, outLocationClass, funLocFac, newIcfgIdentifier, transformer,
				backtranslationTracker, services, option);
	}

	@SuppressWarnings("unchecked")
	private IIcfg<OUTLOC> accelerat(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer,
			final IBacktranslationTracker backtranslationTracker, final IUltimateServiceProvider services,
			final LoopAccelerationOptions option) {
		if (option.equals(LoopAccelerationOptions.DO_NOT_ACCELERATE)) {
			return (IIcfg<OUTLOC>) originalIcfg;
		}
		// get the loop
		final LoopDetectionBB<INLOC, OUTLOC> loopDetection = new LoopDetectionBB<>(logger, originalIcfg,
				outLocationClass, funLocFac, newIcfgIdentifier, transformer, backtranslationTracker, services);
		final IIcfg<OUTLOC> loop = loopDetection.getLoop();

		// create the matrix
		final MatrixBB matrix = new LoopAccelerationMatrix<>(logger, loop).getResult();
		// calculate the alphas
		final AlphaSolver<INLOC> alphaSolver =
				new AlphaSolver<>(logger, (IIcfg<INLOC>) loop, matrix.getMatrix(), matrix.getLGS(), services);
		// add guard and final icfg
		return loopDetection.rejoin(alphaSolver.getResult(), alphaSolver.getN(), alphaSolver.getGuardSubstitute());
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}