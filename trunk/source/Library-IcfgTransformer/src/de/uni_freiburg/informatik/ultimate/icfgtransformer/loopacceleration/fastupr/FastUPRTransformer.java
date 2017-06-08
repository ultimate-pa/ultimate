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
	private final IIcfg<INLOC> mOriginalIcfg;

	public FastUPRTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> locationFactory,
			String newIcfgIdentifier, ITransformulaTransformer transformer,
			final IBacktranslationTracker backtranslationTracker, IUltimateServiceProvider services) {
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		mLocationFactory = Objects.requireNonNull(locationFactory);
		mManagedScript = origIcfg.getCfgSmtToolkit().getManagedScript();
		mBacktranslationTracker = backtranslationTracker;
		mServices = services;
		// perform transformation last
		mLogger.debug("Starting fastUPR Transformation");
		mOriginalIcfg = origIcfg;
		mResultIcfg = transform(origIcfg, Objects.requireNonNull(newIcfgIdentifier),
				Objects.requireNonNull(outLocationClass), transformer);
	}

	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> originalIcfg, final String newIcfgIdentifier,
			final Class<OUTLOC> outLocationClass, ITransformulaTransformer transformer) {

		mLogger.debug("Getting List of loop paths ...");

		final FastUPRDetection<INLOC, OUTLOC> loopDetection = new FastUPRDetection<>(mLogger, originalIcfg,
				outLocationClass, newIcfgIdentifier);
		// final List<Deque<INLOC>> loopPaths = loopDetection.getLoopPaths();
		final List<Deque<IcfgEdge>> loopEdgePaths = loopDetection.getLoopEdgePaths();

		if (loopEdgePaths.isEmpty()) {
			mLogger.debug("No loop paths found");
		} else {
			mLogger.debug("Found " + loopEdgePaths.size() + " loop paths");
		}

		final BasicIcfg<OUTLOC> resultIcfg = new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(),
				outLocationClass);

		final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(mLocationFactory,
				mBacktranslationTracker, transformer, originalIcfg, resultIcfg);

		mLogger.debug("Transforming loop into icfg...");

		getLoopIcfg(loopEdgePaths, resultIcfg, originalIcfg, lst);

		mLogger.debug("Icfg created.");

		return resultIcfg;
	}

	private void getLoopIcfg(List<Deque<IcfgEdge>> loopEdgePaths, final BasicIcfg<OUTLOC> resultIcfg,
			final IIcfg<INLOC> origIcfg, final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {

		final Map<IcfgEdge, UnmodifiableTransFormula> loopMapping = new HashMap<>();

		for (final Deque<IcfgEdge> path : loopEdgePaths) {

			if (path == null || path.isEmpty()) {
				continue;
			}

			IcfgEdge loopEdge = path.getFirst();

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
				resultFormula = fastUpr.getResult();
				mLogger.debug("Result Formula:" + resultFormula.toString());

				if (loopEdge != null) {
					loopMapping.put(loopEdge, resultFormula);
					final String formulaString = resultFormula.getFormula().toStringDirect();
					mLogger.debug("resultFormula: " + formulaString);
				} else {
					throw new IllegalArgumentException("FastUPR couldn't compute a loop acceleration.");
				}

			} catch (final Exception e) {
				mLogger.error("", e);
				loopEdge = null;
				// TODO: ADD SETTING TO throw exception or whatever when FastUPR
				// couldn't handle the loop.

				// throw new IllegalArgumentException("FastUPR can't handle the
				// loop given.");
			}

		}

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

			createNewLocations(oldSource, newSource, closed, resultIcfg, lst, loopMapping);
			// createNewLocationsSplit(oldSource, newSource, closed, resultIcfg,
			// lst, loopMapping);
		}
	}

	@SuppressWarnings("unchecked")
	private void createNewLocations(final INLOC oldSource, final OUTLOC newSource, final Set<INLOC> closed,
			final BasicIcfg<OUTLOC> result, final TransformedIcfgBuilder<INLOC, OUTLOC> lst,
			Map<IcfgEdge, UnmodifiableTransFormula> loopMapping) {

		result.addOrdinaryLocation(newSource);

		for (final IcfgEdge oldEdge : oldSource.getOutgoingEdges()) {
			if (loopMapping.containsKey(oldEdge)) {
				final IcfgEdge newTrans = lst.createNewInternalTransition(newSource, newSource,
						loopMapping.get(oldEdge), false);
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
	private void createNewLocationsSplit(final INLOC oldSource, OUTLOC newSource, final Set<INLOC> closed,
			final BasicIcfg<OUTLOC> result, final TransformedIcfgBuilder<INLOC, OUTLOC> lst,
			Map<IcfgEdge, UnmodifiableTransFormula> loopMapping) {

		OUTLOC source = newSource;

		for (final IcfgEdge oldEdge : oldSource.getOutgoingEdges()) {
			if (loopMapping.containsKey(oldEdge)) {
				final OUTLOC loopExit = createFreshLocation(oldSource, result);

				final IcfgEdge newTrans = lst.createNewInternalTransition(newSource, loopExit, loopMapping.get(oldEdge),
						false);
				newSource.addOutgoing(newTrans);
				loopExit.addIncoming(newTrans);
				source = loopExit;
				continue;
			}
		}

		for (final IcfgEdge oldEdge : oldSource.getOutgoingEdges()) {
			if (loopMapping.containsKey(oldEdge)) {
				continue;
			}
			final INLOC oldTarget = (INLOC) oldEdge.getTarget();
			final OUTLOC newTarget = lst.createNewLocation(oldTarget);
			final IcfgEdge newEdge = lst.createNewTransition(source, newTarget, oldEdge);
			source.addOutgoing(newEdge);
			newTarget.addIncoming(newEdge);

			if (!closed.add(oldTarget)) {
				return;
			}

			createNewLocationsSplit(oldTarget, newTarget, closed, result, lst, loopMapping);

		}
	}

	private OUTLOC createFreshLocation(INLOC oldLoc, BasicIcfg<OUTLOC> resultIcfg) {

		final String proc = oldLoc.getProcedure();
		final OUTLOC freshLoc = mLocationFactory.createLocation(oldLoc, oldLoc.getDebugIdentifier(), proc);

		// determine attributes of location
		final boolean isInitial = false;
		final Set<INLOC> errorLocs = mOriginalIcfg.getProcedureErrorNodes().get(proc);
		final boolean isError = errorLocs != null && errorLocs.contains(oldLoc);
		final boolean isProcEntry = false;
		final boolean isProcExit = false;
		final boolean isLoopLocation = false;

		// add fresh location to resultIcfg
		resultIcfg.addLocation(freshLoc, isInitial, isError, isProcEntry, isProcExit, isLoopLocation);

		return freshLoc;
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
	// add fresh location to resultIcfg
}
