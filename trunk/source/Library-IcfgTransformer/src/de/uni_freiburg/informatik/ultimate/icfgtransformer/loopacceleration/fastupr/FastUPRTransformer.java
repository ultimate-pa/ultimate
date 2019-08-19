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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;

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
	 * Calls the FastUPR LoopAcceleration package - the transformed icfg is
	 * return by the getResult() Method.
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
	 *            The Transformer used to create locations and transitions for
	 *            the new {@link IIcfg}.
	 * @param backtranslationTracker
	 *            A backtranslation tracker
	 * @param services
	 *            An {@link IUltimateServiceProvider}
	 * @param replaceMethod
	 *            {@link FastUPRReplacementMethod} to use: REPLACE_LOOP_EDGE
	 *            replaces the loop edge with an accelerated edge (in place),
	 *            REPLACE_EXIT_EDGE merges the loop edge with the exit edge.
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

		final BasicIcfg<OUTLOC> resultIcfg = new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(),
				outLocationClass);

		final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(mLogger, mLocationFactory,
				mBacktranslationTracker, transformer, originalIcfg, resultIcfg);

		mLogger.debug("Transforming loops into icfg...");

		getLoopIcfg(loopEdgePaths, resultIcfg, originalIcfg, lst);

		mLogger.debug("Icfg created.");

		return resultIcfg;
	}

	@SuppressWarnings("unchecked")
	private void getLoopIcfg(final List<Deque<IcfgEdge>> loopEdgePaths, final BasicIcfg<OUTLOC> resultIcfg,
			final IIcfg<INLOC> origIcfg, final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {

		final Map<IcfgEdge, LoopEdgeElement> loopMapping = new HashMap<>();

		for (final Deque<IcfgEdge> path : loopEdgePaths) {

			if (path == null || path.isEmpty()) {
				continue;
			}

			IcfgEdge loopEdge = path.getFirst();

			mBenchmark.startRun(loopEdge.getSource());

			final List<UnmodifiableTransFormula> formulas = new ArrayList<>();

			UnmodifiableTransFormula resultFormula = null;

			final IcfgEdge assertionEdge = null;
			final IcfgEdge assertionExit = null;
			IcfgEdge loopEntry = null;
			IcfgEdge falseEdge = null;
			IcfgEdge loopExit = null;

			try {

				while (!path.isEmpty()) {
					final IcfgEdge edge = path.getFirst();

					if (edge.equals(loopEdge) && edge.getTransformula().getFormula().toString().equals("true")
							&& edge.getSource().getOutgoingEdges().size() == 2) {
						// LoopEdge is actually LoopEntry

						loopEntry = edge;
						falseEdge = edge.getSource().getOutgoingEdges().get(0) == edge
								? edge.getSource().getOutgoingEdges().get(1)
								: edge.getSource().getOutgoingEdges().get(0);
						path.pop();
					} else if (edge.getSource().getOutgoingEdges().size() == 2
							&& edge.getSource().getIncomingEdges().get(0).equals(loopEntry)) {
						// LoopEdge after LoopEntry

						loopExit = findLoopExit(edge, falseEdge);
						formulas.add(edge.getTransformula());
						path.pop();
					} else if (!edge.equals(loopEdge) && edge.getSource().getOutgoingEdges().size() > 1) {

						throw new IllegalArgumentException("Cannot compute nondeterministic paths.");

					} else {
						// Just an ordinary edge - those exist! At least, if you
						// believe in the rumors.

						formulas.add(edge.getTransformula());
						path.pop();
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
				loopMapping.put(loopEdge,
						new LoopEdgeElement(loopEntry, loopEdge, loopExit, resultFormula, assertionEdge));
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

		final Deque<IcfgEdge> addLast = new ArrayDeque<>();

		// while (!open.isEmpty()) {
		// final INLOC oldSource = open.removeFirst();
		// if (!closed.add(oldSource)) {
		// continue;
		// }
		//
		// final OUTLOC newSource = lst.createNewLocation(oldSource);
		// createNewLocationsUntransformed(oldSource, newSource, closed, open,
		// lst, addLast);
		//
		// }
		//
		// while (!addLast.isEmpty()) {
		// final IcfgEdge oldEdge = addLast.pop();
		// if (oldEdge instanceof IIcfgReturnTransition<?, ?>
		// && !lst.isCorrespondingCallContained((IIcfgReturnTransition<?, ?>)
		// oldEdge)) {
		// addLast.addLast(oldEdge);
		// continue;
		// }
		//
		// final INLOC oldS = (INLOC) oldEdge.getSource();
		// final OUTLOC newS = lst.createNewLocation(oldS);
		// final INLOC oldT = (INLOC) oldEdge.getTarget();
		// final OUTLOC newT = lst.createNewLocation(oldT);
		// lst.createNewTransition(newS, newT, oldEdge);
		// }

		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();

			if (!closed.add(oldSource)) {
				continue;
			}

			final OUTLOC newSource = lst.createNewLocation(oldSource);
			if (mReplacementMethod.equals(FastUPRReplacementMethod.REPLACE_LOOP_EDGE)) {
				createNewLocations(oldSource, newSource, closed, open, resultIcfg, lst, loopMapping, addLast);
			} else if (mReplacementMethod.equals(FastUPRReplacementMethod.REPLACE_EXIT_EDGE)) {
				createNewLocationsWithReplaceExit(oldSource, newSource, closed, resultIcfg, lst, loopMapping, addLast);
			}
		}
		while (!addLast.isEmpty()) {
			final IcfgEdge oldEdge = addLast.pop();
			if (oldEdge instanceof IIcfgReturnTransition<?, ?>
					&& !lst.isCorrespondingCallContained((IIcfgReturnTransition<?, ?>) oldEdge)) {
				addLast.add(oldEdge);
				continue;
			}
			final INLOC oldS = (INLOC) oldEdge.getSource();
			final OUTLOC newS = lst.createNewLocation(oldS);
			final INLOC oldT = (INLOC) oldEdge.getTarget();
			final OUTLOC newT = lst.createNewLocation(oldT);
			final IcfgEdge newEdge = lst.createNewTransition(newS, newT, oldEdge);

			if (!closed.add(oldT)) {
				continue;
			}

			if (mReplacementMethod.equals(FastUPRReplacementMethod.REPLACE_LOOP_EDGE)) {
				createNewLocations(oldS, newS, closed, open, resultIcfg, lst, loopMapping, addLast);
			} else if (mReplacementMethod.equals(FastUPRReplacementMethod.REPLACE_EXIT_EDGE)) {
				createNewLocationsWithReplaceExit(oldS, newS, closed, resultIcfg, lst, loopMapping, addLast);
			}

		}
	}

	private void createNewLocationsUntransformed(final INLOC oldSource, final OUTLOC newSource, final Set<INLOC> closed,
			final Deque<INLOC> open, final TransformedIcfgBuilder<INLOC, OUTLOC> lst, final Deque<IcfgEdge> addLast) {
		for (final IcfgEdge oldEdge : oldSource.getOutgoingEdges()) {

			final INLOC oldTarget = (INLOC) oldEdge.getTarget();
			open.add(oldTarget);
			final OUTLOC newTarget = lst.createNewLocation(oldTarget);
			if (oldEdge instanceof IIcfgReturnTransition<?, ?>) {
				addLast.add(oldEdge);
			} else {
				lst.createNewTransition(newSource, newTarget, oldEdge);
			}

		}

	}

	private static IcfgEdge findLoopExit(final IcfgEdge edge, final IcfgEdge falseEdge) {
		for (final IcfgEdge e : edge.getSource().getOutgoingEdges()) {
			if (e.getTarget().equals(falseEdge.getTarget())) {
				return e;
			}
		}
		throw new IllegalArgumentException("No exit edge found.");
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
			final Deque<INLOC> open, final BasicIcfg<OUTLOC> result, final TransformedIcfgBuilder<INLOC, OUTLOC> lst,
			final Map<IcfgEdge, LoopEdgeElement> loopMapping, final Deque<IcfgEdge> addLast) {

		for (final IcfgEdge oldEdge : oldSource.getOutgoingEdges()) {

			if (oldEdge instanceof IIcfgReturnTransition<?, ?>
					&& !lst.isCorrespondingCallContained((IIcfgReturnTransition<?, ?>) oldEdge)) {
				addLast.add(oldEdge);
				continue;
			}

			if (loopMapping.containsKey(oldEdge)) {

				final LoopEdgeElement element = loopMapping.get(oldEdge);

				if (element.getEntryEdge() != null && element.getExitEdge() != null) {
					final IcfgEdge newTrans = lst.createNewInternalTransition(newSource, newSource,
							loopMapping.get(oldEdge).getFormula(), false);
					newSource.addOutgoing(newTrans);
					newSource.addIncoming(newTrans);
					final INLOC oldTarget = (INLOC) element.getExitEdge().getTarget();
					final OUTLOC newTarget = lst.createNewLocation(oldTarget);
					final IcfgEdge exitEdge = lst.createNewTransition(newSource, newTarget, element.getExitEdge());
					mBacktranslationTracker.rememberRelation(element.getExitEdge(), exitEdge);
					open.add(oldTarget);
					continue;

				} else {
					final IcfgEdge newTrans = lst.createNewInternalTransition(newSource, newSource,
							loopMapping.get(oldEdge).getFormula(), false);
					mBacktranslationTracker.rememberRelation(oldEdge, newTrans);
					continue;
				}
			}

			final INLOC oldTarget = (INLOC) oldEdge.getTarget();
			final OUTLOC newTarget = lst.createNewLocation(oldTarget);
			lst.createNewTransition(newSource, newTarget, oldEdge);

			open.add(oldTarget);
		}

	}

	@SuppressWarnings("unchecked")
	private void createNewLocationsWithReplaceExit(final INLOC oldSource, final OUTLOC newSource,
			final Set<INLOC> closed, final BasicIcfg<OUTLOC> result, final TransformedIcfgBuilder<INLOC, OUTLOC> lst,
			final Map<IcfgEdge, LoopEdgeElement> loopMapping, final Deque<IcfgEdge> addLast) {

		for (final IcfgEdge e : loopMapping.keySet()) {
			if (e.getSource().equals(oldSource)) {
				// IS A LOOP HEAD
				final IcfgEdge exit = getExitEdge(e);
				final INLOC oldTarget = (INLOC) exit.getTarget();
				final OUTLOC newTarget = lst.createNewLocation(oldTarget);
				final IcfgEdge newEdge = lst.createNewInternalTransition(newSource, newTarget,
						loopMapping.get(e).getFormula(), false);
				mBacktranslationTracker.rememberRelation(e, newEdge);
				continue;
			}
		}

		for (final IcfgEdge oldEdge : oldSource.getOutgoingEdges()) {

			if (oldEdge instanceof IIcfgReturnTransition<?, ?>
					&& !lst.isCorrespondingCallContained((IIcfgReturnTransition<?, ?>) oldEdge)) {
				addLast.add(oldEdge);
				continue;
			}

			if (loopMapping.containsKey(oldEdge)) {
				continue;
			}

			final INLOC oldTarget = (INLOC) oldEdge.getTarget();
			final OUTLOC newTarget = lst.createNewLocation(oldTarget);
			final IcfgEdge newEdge = lst.createNewTransition(newSource, newTarget, oldEdge);

			if (!closed.add(oldTarget)) {
				continue;
			}

			createNewLocationsWithReplaceExit(oldTarget, newTarget, closed, result, lst, loopMapping, addLast);

		}

	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
	// add fresh location to resultIcfg

	public int getSuccessfulAccelerations() {
		return mLoops - mLoopFailures;
	}

	public int getTotalLoopsFound() {
		return mLoops;
	}

	/**
	 * REPLACE_LOOP_EDGE replaces the loop edge in place (might be slow),
	 * REPLACE_EXIT_EDGE replaces the exit edge with a merge of the loop edge
	 * and the exit edge (unknown behavior for already transformed Icfg - e.g.
	 * if the exit edge was already merged with other edges)
	 *
	 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
	 *
	 */
	public enum FastUPRReplacementMethod {
		REPLACE_LOOP_EDGE, REPLACE_EXIT_EDGE,
	}

	private class LoopEdgeElement {
		public final IcfgEdge mEntryEdge;
		public final IcfgEdge mLoopEdge;
		public final IcfgEdge mExitEdge;
		public final UnmodifiableTransFormula mResultFormula;
		public final IcfgEdge mAssertionExit;

		public LoopEdgeElement(final IcfgEdge entry, final IcfgEdge loopEdge, final IcfgEdge exit, final UnmodifiableTransFormula result,
				final IcfgEdge assertionexit) {
			mEntryEdge = entry;
			mLoopEdge = loopEdge;
			mExitEdge = exit;
			mResultFormula = result;
			mAssertionExit = assertionexit;
		}

		public IcfgEdge getEntryEdge() {
			return mEntryEdge;
		}

		public IcfgEdge getLoopEdge() {
			return mLoopEdge;
		}

		public UnmodifiableTransFormula getFormula() {
			return mResultFormula;
		}

		public IcfgEdge getAssertionExt() {
			return mAssertionExit;
		}

		public IcfgEdge getExitEdge() {
			return mExitEdge;
		}

	}

}
