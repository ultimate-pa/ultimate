/*
 * Copyright (C) 2022 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformationBacktranslator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.CopyingTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/**
 * Class for applying the qvasr loop summarization technique in conjunction with IcfgTransformation.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IIcfg<INLOC> mOriginalIcfg;
	private final ITransformulaTransformer mTransformer;
	private final IUltimateServiceProvider mServices;
	private final IIcfg<OUTLOC> mResult;

	/**
	 * Construct a new qvasr loop icfgtransformer.
	 *
	 * @param logger
	 *            An {@link ILogger}
	 * @param originalIcfg
	 *            The original {@link IIcfg}
	 * @param outLocationClass
	 *            outlocation class
	 * @param funLocFac
	 *            A {@link ILocationFactory}
	 * @param newIcfgIdentifier
	 *            New name for the transformed {@link IIcfg}
	 * @param backtranslationTracker
	 *            An {@link IcfgTransformationBacktranslator}
	 * @param services
	 *            An {@link IUltimateServiceProvider}
	 */
	public QvasrIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final String newIcfgIdentifier, final IcfgTransformationBacktranslator backtranslationTracker,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mOriginalIcfg = originalIcfg;
		mServices = services;
		mScript = originalIcfg.getCfgSmtToolkit().getManagedScript();
		mTransformer = new QvasrLoopAccelerationTransformer(mLogger, originalIcfg.getCfgSmtToolkit().getManagedScript(),
				originalIcfg.getCfgSmtToolkit());
		mResult = new IcfgTransformer<>(mLogger, originalIcfg, funLocFac, backtranslationTracker, outLocationClass,
				newIcfgIdentifier, mTransformer).getResult();
	}

	private final class QvasrLoopAccelerationTransformer extends CopyingTransformulaTransformer {

		public QvasrLoopAccelerationTransformer(final ILogger logger, final ManagedScript managedScript,
				final CfgSmtToolkit oldToolkit) {
			super(logger, managedScript, oldToolkit);
		}

		@Override
		public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
				final UnmodifiableTransFormula tf) {
			final QvasrSummarizer qvasrSummarizer = new QvasrSummarizer(mLogger, mServices, mScript);
			if (oldEdge.getSource() == oldEdge.getTarget()) {
				mLogger.debug("Found loop, starting Qvasr summarization.");
				final UnmodifiableTransFormula oldTf = oldEdge.getTransformula();
				if (!SmtUtils.containsArrayVariables(oldTf.getFormula()) || !SmtUtils.isArrayFree(oldTf.getFormula())) {
					return super.transform(oldEdge, tf);
				}
				final UnmodifiableTransFormula loopAccel = qvasrSummarizer.summarizeLoop(oldTf);
				return new TransformulaTransformationResult(loopAccel);
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