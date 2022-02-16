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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasrs;

import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformationBacktranslator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRDetection;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Class for applying the qvasr loop summarization technique in conjunction with IcfgTransformation.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrsIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final ManagedScript mScript;
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
	public QvasrsIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer,
			final IcfgTransformationBacktranslator backtranslationTracker, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		mScript = originalIcfg.getCfgSmtToolkit().getManagedScript();
		mResult = transform(originalIcfg, funLocFac, backtranslationTracker, outLocationClass, newIcfgIdentifier,
				transformer);
	}

	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IcfgTransformationBacktranslator backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer) {
		transformer.preprocessIcfg(originalIcfg);
		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(mLogger, funLocFac,
				backtranslationTracker, transformer, originalIcfg, resultIcfg);
		processLocations(originalIcfg, originalIcfg.getInitialNodes(), lst, funLocFac);
		lst.finish();
		return resultIcfg;
	}

	private void processLocations(final IIcfg<INLOC> originalIcfg, final Set<INLOC> init,
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst, final ILocationFactory<INLOC, OUTLOC> funLocFac) {

		/*
		 * Finding loops using FastUPR loop detector. {@link FastUPRDetection}
		 */
		final FastUPRDetection<INLOC> loopDetector = new FastUPRDetection<>(mLogger, originalIcfg);
		final Map<INLOC, Deque<IcfgEdge>> loopsWithLoopHead = loopDetector.getLoopEdgePathsWithLoopHead();
		final List<INLOC> loopHeads = loopDetector.getLoopHeads();
		final Map<INLOC, QvasrsAbstraction> qvasrsAbstractions = new HashMap<>();

		final QvasrsSummarizer qvasrsSummarizer = new QvasrsSummarizer(mLogger, mServices, mScript);
		for (final Entry<INLOC, Deque<IcfgEdge>> loopMap : loopsWithLoopHead.entrySet()) {
			final Map<INLOC, QvasrsAbstraction> mapping = new HashMap<>();
			qvasrsAbstractions.put(loopMap.getKey(),
					qvasrsSummarizer.computeQvasrsAbstraction(edgesToFormula(loopMap.getValue()), true));
		}

		final IcfgLocationIterator<INLOC> iter = new IcfgLocationIterator<>(init);

		// we need to create new return transitions after new call transitions have been created
		final List<Triple<OUTLOC, OUTLOC, IcfgEdge>> rtrTransitions = new ArrayList<>();

		while (iter.hasNext()) {
			final INLOC oldSource = iter.next();
			OUTLOC newSource;
			if (loopHeads.contains(oldSource)) {
				final QvasrsAbstraction abstraction = qvasrsAbstractions.get(oldSource);
				final Map<Term, OUTLOC> qvasrsStateToLoc = new HashMap<>();
				for (final Term state : abstraction.getStates()) {
					qvasrsStateToLoc.put(state, funLocFac.createLocation(oldSource, oldSource.getDebugIdentifier(),
							oldSource.getProcedure()));
				}
				/*
				 * TODO insert new paths.
				 */
				mLogger.debug("H");
			} else {
				for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
					newSource = lst.createNewLocation(oldSource);
					@SuppressWarnings("unchecked")
					final OUTLOC newTarget = lst.createNewLocation((INLOC) oldTransition.getTarget());
					if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
						rtrTransitions.add(new Triple<>(newSource, newTarget, oldTransition));
					} else {
						lst.createNewTransition(newSource, newTarget, oldTransition);
					}
				}
			}

		}
		rtrTransitions.forEach(a -> lst.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));
	}

	private UnmodifiableTransFormula edgesToFormula(final Deque<IcfgEdge> loopEdges) {
		final List<UnmodifiableTransFormula> edgeTransitions = new ArrayList<>();
		for (final IcfgEdge edge : loopEdges) {
			edgeTransitions.add(edge.getTransformula());
		}
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mScript, true, true, false, false,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.POLY_PAC,
				edgeTransitions);
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResult;
	}
}