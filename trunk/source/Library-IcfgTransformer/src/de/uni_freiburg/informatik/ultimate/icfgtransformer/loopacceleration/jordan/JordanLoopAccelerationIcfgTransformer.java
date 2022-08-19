/*
 * Copyright (C) 2021 Miriam Herzig
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformationBacktranslator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.CopyingTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanLoopAcceleration.JordanLoopAccelerationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class JordanLoopAccelerationIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final IIcfg<INLOC> mOriginalIcfg;
	private final ITransformulaTransformer mTransformer;
	private final IUltimateServiceProvider mServices;
	private final IIcfg<OUTLOC> mResult;

	public JordanLoopAccelerationIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final String newIcfgIdentifier, final IcfgTransformationBacktranslator backtranslationTracker,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mOriginalIcfg = originalIcfg;
		mServices = services;
		mTransformer = new JordanLoopAccelerationTransformer(mLogger,
				originalIcfg.getCfgSmtToolkit().getManagedScript(), originalIcfg.getCfgSmtToolkit());
		mResult = new IcfgTransformer<>(mLogger, originalIcfg, funLocFac, backtranslationTracker, outLocationClass,
				newIcfgIdentifier, mTransformer).getResult();
	}

	private final class JordanLoopAccelerationTransformer extends CopyingTransformulaTransformer {

		public JordanLoopAccelerationTransformer(final ILogger logger, final ManagedScript managedScript,
				final CfgSmtToolkit oldToolkit) {
			super(logger, managedScript, oldToolkit);
		}

		@Override
		public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
				final UnmodifiableTransFormula tf) {
			if (oldEdge.getSource() == oldEdge.getTarget()) {
				// self loop, lets accelerate
				final UnmodifiableTransFormula oldTf = oldEdge.getTransformula();
				final JordanLoopAccelerationResult jlar = JordanLoopAcceleration.accelerateLoop(mServices,
						mOriginalIcfg.getCfgSmtToolkit().getManagedScript(), oldTf, !false);
				mLogger.info("Jordan loop acceleration statistics: " + jlar.getJordanLoopAccelerationStatistics());
				if (jlar.getAccelerationStatus() == JordanLoopAccelerationResult.AccelerationStatus.SUCCESS) {
					mLogger.info("Accelerated %s to %s", oldTf, jlar.getTransFormula());
					final String shortDescrption = "Jordan loop acceleration statistics";
					final StatisticsData statistics = new StatisticsData();
					statistics.aggregateBenchmarkData(jlar.getJordanLoopAccelerationStatistics());
					final String id = "IcfgTransformer";
					mServices.getResultService().reportResult(id,
							new StatisticsResult<>(id, shortDescrption, statistics));
					return new TransformulaTransformationResult(jlar.getTransFormula());
				} else {
					throw new IllegalArgumentException(jlar.getAccelerationStatus() + " " + jlar.getErrorMessage());
					// return super.transform(oldEdge, tf);
				}
			} else {
				return super.transform(oldEdge, tf);
			}
		}
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResult;
	}
}