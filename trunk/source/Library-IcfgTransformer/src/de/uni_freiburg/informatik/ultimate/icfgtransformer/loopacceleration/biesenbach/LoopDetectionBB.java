/*
 * Copyright (C) 2017 Ben Biesenbach (Ben.Biesenbach@gmx.de)
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

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Extracts the loops from an {@link IIcfg}.
 *
 * @param <INLOC>
 *            The type of the locations of the IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the IIcfg with only loops left.
 *
 * @author Ben Biesenbach (Ben.Biesenbach@gmx.de)
 */
public class LoopDetectionBB<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {

	private final ILogger mLogger;
	private final Deque<IIcfg<OUTLOC>> mLoopIcfgs = new ArrayDeque<>();

	/**
	 * Extracts the loops from an {@link IIcfg}.
	 *
	 * @param logger
	 * @param originalIcfg
	 * @param outLocationClass
	 * @param funLocFac
	 * @param newIcfgIdentifier
	 * @param transformer
	 * @param backtranslationTracker
	 * @param services
	 */
	@SuppressWarnings("unchecked")
	public LoopDetectionBB(final ILogger logger, final IIcfg<INLOC> originalIcfg, final Class<OUTLOC> outLocationClass,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer, final IBacktranslationTracker backtranslationTracker,
			final IUltimateServiceProvider services) {

		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		mLogger.info("BB_Start...");
		transformer.preprocessIcfg(origIcfg);

		for (final INLOC loopHead : origIcfg.getLoopLocations()) {
			// get path for every loop
			final Deque<INLOC> path = new ArrayDeque<>();
			path.addLast(loopHead);
			final Deque<INLOC> loopPath = getLoopPath(path);

			// set loopHead as initialNode
			final BasicIcfg<OUTLOC> initHelper =
					new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
			final TransformedIcfgBuilder<INLOC, OUTLOC> lstHelper =
					new TransformedIcfgBuilder<>(funLocFac, backtranslationTracker, transformer, origIcfg, initHelper);
			initHelper.addLocation((OUTLOC) loopPath.getFirst(), true, false, true, false, true);
			initHelper.addLocation((OUTLOC) origIcfg.getProcedureExitNodes().values().iterator().next(), false, false,
					false, true, false);
			lstHelper.finish();

			// get loop as Icfg
			final BasicIcfg<OUTLOC> resultLoop =
					new BasicIcfg<>(newIcfgIdentifier, initHelper.getCfgSmtToolkit(), outLocationClass);
			transformer.preprocessIcfg(initHelper);
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(funLocFac,
					backtranslationTracker, transformer, (IIcfg<INLOC>) initHelper, resultLoop);
			transformPathToIcfg((IIcfg<INLOC>) initHelper, loopPath, lst);
			lst.finish();

			mLoopIcfgs.addLast(resultLoop);
		}

		final LoopAccelerationMatrix<OUTLOC> lam = new LoopAccelerationMatrix<>(mLogger, mLoopIcfgs.getLast());

		mLogger.info("BB_End...");

		// Notes:
		// Get the "guard" part of a transformula:
		// UnmodifiableTransFormula guardTf = TransFormulaUtils.computeGuard(mOriginalTransFormula, mMgScript, services,
		// mLogger);

		// mark something as overapproximation
		// new Overapprox("loop acceleration: ... ", null).annotate(icfgedge)

		// add some setting s.t. one can switch between "throw exception", "mark as overapprox", "do not accelerate"

		// eliminate quantifiers
		// Term simplfiedTerm = PartialQuantifierElimination.tryToEliminate(services, mLogger, mgdScript, term,
		// SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
	}

	@SuppressWarnings("unchecked")
	private Deque<INLOC> getLoopPath(final Deque<INLOC> path) {
		Deque<INLOC> loopPath = null;
		for (final IcfgEdge transition : path.getLast().getOutgoingEdges()) {
			if (transition.getTarget().equals(path.getFirst())) {
				path.addLast((INLOC) transition.getTarget());
				return path;
			}
			final Deque<INLOC> newPath = new ArrayDeque<>(path);
			newPath.addLast((INLOC) transition.getTarget());
			final Deque<INLOC> returnedPath = getLoopPath(newPath);
			if (returnedPath != null) {
				loopPath = returnedPath;
			}
		}
		return loopPath;
	}

	@SuppressWarnings("unchecked")
	private void transformPathToIcfg(final IIcfg<INLOC> origIcfg, final Deque<INLOC> path,
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {

		final Deque<INLOC> open = new ArrayDeque<>();
		open.add(path.removeFirst());

		// Add the loopBody to the Icfg
		while (!open.isEmpty() && !path.isEmpty()) {

			final INLOC oldSource = open.removeFirst();
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				final INLOC oldTarget;

				// Check if transition is part of the path
				if (oldTransition.getTarget().equals(path.getFirst())) {
					oldTarget = (INLOC) oldTransition.getTarget();
					open.add(oldTarget);
				} else {
					oldTarget = origIcfg.getProcedureExitNodes().values().iterator().next();
				}

				// create new Nodes and Edges
				final OUTLOC newSource;
				newSource = lst.createNewLocation(oldSource);
				final OUTLOC newTarget = lst.createNewLocation(oldTarget);
				lst.createNewTransition(newSource, newTarget, oldTransition);
			}
			if (!path.isEmpty()) {
				path.removeFirst();
			}
		}
	}

	public IIcfg<OUTLOC> getResult() {
		return mLoopIcfgs.getFirst();
	}

	public Deque<IIcfg<OUTLOC>> getAllResults() {
		return mLoopIcfgs;
	}
}