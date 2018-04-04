/*
 * Copyright (C) 2017 Usman Ahmed (usm422@gmail.com)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.ahmed;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
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

/**
 * An IcfgTransformer that accelerates loops based on
 * "Under-approximating loops in C programs for fast counterexample detection".
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Usman Ahmed (usm422@gmail.com)
 *
 */
public class AhmedLoopAccelerationIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final BasicIcfg<OUTLOC> mResultIcfg;
	private final IUltimateServiceProvider mServices;

	/**
	 * Constructs a LoopAccelerationIcfgTransformer.
	 *
	 * @param logger
	 *            A {@link ILogger} instance that is used for debug logging.
	 * @param originalIcfg
	 *            an input {@link IIcfg}.
	 * @param funLocFac
	 *            A location factory.
	 * @param backtranslationTracker
	 *            A backtranslation tracker.
	 * @param outLocationClass
	 *            The class object of the type of locations of the output {@link IIcfg}.
	 * @param newIcfgIdentifier
	 *            The identifier of the new {@link IIcfg}
	 * @param transformer
	 *            The transformer that should be applied to each transformula of each transition of the input
	 *            {@link IIcfg} to create a new {@link IIcfg}.
	 * @param services
	 */
	public AhmedLoopAccelerationIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer, final IUltimateServiceProvider services) {
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		mServices = Objects.requireNonNull(services);

		// perform transformation last
		mResultIcfg = new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> icfgBuilder =
				new TransformedIcfgBuilder<>(logger, funLocFac, backtranslationTracker, transformer, origIcfg,
						mResultIcfg);
		processLocations(origIcfg.getInitialNodes(), icfgBuilder);
		icfgBuilder.finish();
	}

	private void processLocations(final Set<INLOC> init, final TransformedIcfgBuilder<INLOC, OUTLOC> icfgBuilder) {
		mLogger.debug("Entry");

		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();

		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();
			if (!closed.add(oldSource)) {
				continue;
			}

			final OUTLOC newSource = icfgBuilder.createNewLocation(oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				final INLOC oldTarget = (INLOC) oldTransition.getTarget();
				open.add(oldTarget);
				final OUTLOC newTarget = icfgBuilder.createNewLocation(oldTarget);
				icfgBuilder.createNewTransition(newSource, newTarget, oldTransition);
			}
		}
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}
