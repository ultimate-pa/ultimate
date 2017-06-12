/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * The main class for Fast Acceleration of Ultimately Periodic Relations
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class FastUPRTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final IIcfg<OUTLOC> mResultIcfg;
	private final ManagedScript mManagedScript;
	private final IBacktranslationTracker mBacktranslationTracker;
	private final ILocationFactory<INLOC, OUTLOC> mLocationFactory;
	private final IUltimateServiceProvider mServices;
	private final FastUPRReplacementMethod mReplacementMethod;
	private int mLoopFailures;
	private int mLoops;
	private final FastUPRBenchmark mBenchmark;

	/**
	 * Calls the FastUPR LoopAcceleration package - the transformed icfg is return by the getResult() Method.
	 *
	 * @param logger
	 *            A {@link ILogger} for Debug Logging
	 * @param originalIcfg
	 *            The original {@link IIcfg} to be transformed.
	 * @param outLocationClass
	 *            The class type of the {@link IIcfg} Output.
	 * @param locationFactory
	 *            A location factory
	 * @param newIcfgIdentifier
	 *            The Identifier of the new {@link IIcfg}.
	 * @param transformer
	 *            The Transformer used to create locations and transitions for the new {@link IIcfg}.
	 * @param backtranslationTracker
	 *            A backtranslation tracker
	 * @param services
	 *            An {@link IUltimateServiceProvider}
	 * @param replaceMethod
	 *            {@link FastUPRReplacementMethod} to use: REPLACE_LOOP_EDGE replaces the loop edge with an accelerated
	 *            edge (in place), REPLACE_EXIT_EDGE merges the loop edge with the exit edge.
	 */
	public FastUPRTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> locationFactory,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer,
			final IBacktranslationTracker backtranslationTracker, final IUltimateServiceProvider services,
			final FastUPRReplacementMethod replaceMethod) {
		mBenchmark = new FastUPRBenchmark();
		mLoopFailures = 0;
		mLoops = 0;
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mReplacementMethod = replaceMethod;
		mLogger = Objects.requireNonNull(logger);
		mLocationFactory = Objects.requireNonNull(locationFactory);
		mManagedScript = origIcfg.getCfgSmtToolkit().getManagedScript();
		mBacktranslationTracker = backtranslationTracker;
		mServices = services;
		// perform transformation last
		mLogger.debug("Starting fastUPR Transformation");
		mResultIcfg = transform(origIcfg, Objects.requireNonNull(newIcfgIdentifier),
				Objects.requireNonNull(outLocationClass), transformer);
		mLogger.debug(mBenchmark.toString());
		mServices.getResultService().reportResult(FastUPR.PLUGIN_ID,
				new StatisticsResult<>(FastUPR.PLUGIN_NAME, "FastUPR Benchmark Results:", mBenchmark));
	}

	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> originalIcfg, final String newIcfgIdentifier,
			final Class<OUTLOC> outLocationClass, final ITransformulaTransformer transformer) {

		mLogger.debug("Getting List of loop paths ...");

		final FastUPRDetection<INLOC> loopDetection = new FastUPRDetection<>(mLogger, originalIcfg);
		final List<Deque<IcfgEdge>> loopEdgePaths = loopDetection.getLoopEdgePaths();

		if (loopEdgePaths.isEmpty()) {
			mLogger.debug("No loop paths found");
		} else {
			mLogger.debug("Found " + loopEdgePaths.size() + " loop paths");
			mLoops = loopEdgePaths.size();
		}

		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);

		final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(mLocationFactory,
				mBacktranslationTracker, transformer, originalIcfg, resultIcfg);

		mLogger.debug("Transforming loops into icfg...");
		getLoopIcfg(loopEdgePaths, resultIcfg, originalIcfg, lst);
		mLogger.debug("Icfg created.");
		return resultIcfg;
	}

	private void getLoopIcfg(final List<Deque<IcfgEdge>> loopEdgePaths, final BasicIcfg<OUTLOC> resultIcfg,
			final IIcfg<INLOC> origIcfg, final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {

		final Map<IcfgEdge, UnmodifiableTransFormula> loopMapping = new HashMap<>();

		for (final Deque<IcfgEdge> path : loopEdgePaths) {
			if (path == null || path.isEmpty()) {
				continue;
			}

			IcfgEdge loopEdge = path.getFirst();

			mBenchmark.startRun(loopEdge.getSource());

			final List<UnmodifiableTransFormula> formulas = new ArrayList<>();

			UnmodifiableTransFormula resultFormula = null;

			try {
				while (!path.isEmpty()) {
					formulas.add(path.pop().getTransformula());
					if (!path.isEmpty() && path.getFirst().getSource().getOutgoingEdges().size() > 1) {
						throw new IllegalArgumentException("Can't compute nondeterministic paths");
					}
				}

				final UnmodifiableTransFormula formula = TransFormulaUtils.sequentialComposition(mLogger, mServices,
						mManagedScript, true, false, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
						SimplificationTechnique.SIMPLIFY_DDA, formulas);
				final FastUPRCore fastUpr = new FastUPRCore(formula, mManagedScript, mLogger, mServices);

				if (mReplacementMethod == FastUPRReplacementMethod.REPLACE_LOOP_EDGE) {
					resultFormula = fastUpr.getResult();
				} else if (mReplacementMethod == FastUPRReplacementMethod.REPLACE_EXIT_EDGE) {
					resultFormula = fastUpr.getExitEdgeResult(getExitEdgeFormula(loopEdge));
				}

				if (resultFormula == null) {
					throw new IllegalArgumentException("FastUPR couldn't compute a loop acceleration.");
				}

				mLogger.debug("Result Formula:" + resultFormula.toString());
				mBenchmark.endRun(true);

			} catch (final Exception e) {
				mLogger.error("", e);
				loopEdge = null;
				mLoopFailures++;
				mBenchmark.endRun(false);
				// TODO: ADD SETTING TO throw exception or whatever when FastUPR
				// couldn't handle the loop.

				// throw new IllegalArgumentException("FastUPR can't handle the
				// loop given.");
			}

			if (loopEdge != null) {
				loopMapping.put(loopEdge, resultFormula);
				final String formulaString = resultFormula.getFormula().toStringDirect();
				mLogger.debug("resultFormula: " + formulaString);
			}

		}

		mLogger.debug("FastUPR found a total of " + loopEdgePaths.size()
				+ " loops and computed accelerated formulas for " + (mLoops - mLoopFailures) + " loops.");

		final Set<INLOC> init = origIcfg.getInitialNodes();
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();

		mLogger.debug("Starting main transformation loop...");

		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();

			if (!closed.add(oldSource)) {
				continue;
			}

			final OUTLOC newSource = lst.createNewLocation(oldSource);
			resultIcfg.addOrdinaryLocation(newSource); // Needed?

			if (mReplacementMethod.equals(FastUPRReplacementMethod.REPLACE_LOOP_EDGE)) {
				createNewLocations(oldSource, newSource, closed, resultIcfg, lst, loopMapping);
			} else if (mReplacementMethod.equals(FastUPRReplacementMethod.REPLACE_EXIT_EDGE)) {
				createNewLocationsWithReplaceExit(oldSource, newSource, closed, resultIcfg, lst, loopMapping);
			}
		}
	}

	private static IcfgEdge getExitEdge(final IcfgEdge loopEdge) {
		final IcfgLocation loc = loopEdge.getSource();
		if (loc.getOutgoingEdges().size() != 2) {
			throw new IllegalArgumentException(
					"Exit Edge Merging can only be done if the loop head has two outgoing edges.");
		}
		for (final IcfgEdge e : loc.getOutgoingEdges()) {
			if (!e.equals(loopEdge)) {
				return e;
			}
		}
		throw new IllegalArgumentException("Loop Edge exists twice.");
	}

	private UnmodifiableTransFormula getExitEdgeFormula(final IcfgEdge loopEdge) {
		return getExitEdge(loopEdge).getTransformula();
	}

	@SuppressWarnings("unchecked")
	private void createNewLocations(final INLOC oldSource, final OUTLOC newSource, final Set<INLOC> closed,
			final BasicIcfg<OUTLOC> result, final TransformedIcfgBuilder<INLOC, OUTLOC> lst,
			final Map<IcfgEdge, UnmodifiableTransFormula> loopMapping) {

		result.addOrdinaryLocation(newSource);

		for (final IcfgEdge oldEdge : oldSource.getOutgoingEdges()) {
			if (loopMapping.containsKey(oldEdge)) {
				final IcfgEdge newTrans =
						lst.createNewInternalTransition(newSource, newSource, loopMapping.get(oldEdge), false);
				newSource.addOutgoing(newTrans);
				newSource.addIncoming(newTrans);
				continue;
			}
			final INLOC oldTarget = (INLOC) oldEdge.getTarget();
			final OUTLOC newTarget = lst.createNewLocation(oldTarget);
			final IcfgEdge newEdge = lst.createNewTransition(newSource, newTarget, oldEdge);
			newSource.addOutgoing(newEdge);
			newTarget.addIncoming(newEdge);

			if (!closed.add(oldTarget)) {
				return;
			}

			createNewLocations(oldTarget, newTarget, closed, result, lst, loopMapping);
		}
	}

	@SuppressWarnings("unchecked")
	private void createNewLocationsWithReplaceExit(final INLOC oldSource, final OUTLOC newSource,
			final Set<INLOC> closed, final BasicIcfg<OUTLOC> result, final TransformedIcfgBuilder<INLOC, OUTLOC> lst,
			final Map<IcfgEdge, UnmodifiableTransFormula> loopMapping) {

		result.addOrdinaryLocation(newSource);

		for (final Entry<IcfgEdge, UnmodifiableTransFormula> entry : loopMapping.entrySet()) {
			final IcfgEdge edge = entry.getKey();
			if (edge.getSource().equals(oldSource)) {
				// IS A LOOP HEAD
				final IcfgEdge exit = getExitEdge(edge);
				final INLOC oldTarget = (INLOC) exit.getTarget();
				final OUTLOC newTarget = lst.createNewLocation(oldTarget);
				final IcfgEdge newTrans =
						lst.createNewInternalTransition(newSource, newTarget, entry.getValue(), false);
				newSource.addOutgoing(newTrans);
				newTarget.addIncoming(newTrans);
				if (!closed.add(oldTarget)) {
					return;
				}
				createNewLocationsWithReplaceExit(oldTarget, newTarget, closed, result, lst, loopMapping);
				return;
			}
		}

		for (final IcfgEdge oldEdge : oldSource.getOutgoingEdges()) {
			if (loopMapping.containsKey(oldEdge)) {
				final IcfgEdge newTrans =
						lst.createNewInternalTransition(newSource, newSource, loopMapping.get(oldEdge), false);
				newSource.addOutgoing(newTrans);
				newSource.addIncoming(newTrans);
				continue;
			}
			final INLOC oldTarget = (INLOC) oldEdge.getTarget();
			final OUTLOC newTarget = lst.createNewLocation(oldTarget);
			final IcfgEdge newEdge = lst.createNewTransition(newSource, newTarget, oldEdge);
			newSource.addOutgoing(newEdge);
			newTarget.addIncoming(newEdge);

			if (!closed.add(oldTarget)) {
				return;
			}

			createNewLocationsWithReplaceExit(oldTarget, newTarget, closed, result, lst, loopMapping);
		}
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}

	public int getSuccessfulAccelerations() {
		return mLoops - mLoopFailures;
	}

	public int getTotalLoopsFound() {
		return mLoops;
	}

	/**
	 * How should FastUPR replace loops?s *
	 *
	 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
	 *
	 */
	public enum FastUPRReplacementMethod {
		/**
		 * Replace the loop edge in-place (might be slow)
		 */
		REPLACE_LOOP_EDGE,

		/**
		 * replace the exit edge with a merge of the loop edge and the exit edge (unknown behavior for already
		 * transformed Icfg - e.g. if the exit edge was already merged with other edges)
		 */
		REPLACE_EXIT_EDGE,
	}
}
