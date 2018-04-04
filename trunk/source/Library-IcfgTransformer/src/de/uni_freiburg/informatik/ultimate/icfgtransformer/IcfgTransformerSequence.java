/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * A {@link IIcfgTransformer} that creates a new {@link IIcfg} with a sequence of {@link ITransformulaTransformer}. Each
 * {@link ITransformulaTransformer} in the sequence is applied to the output of the previous
 * {@link ITransformulaTransformer} of the sequence. The first one takes the input {@link IIcfg} as input, the output of
 * the last one is the output of this {@link IIcfgTransformer}.
 *
 * @param <INLOC>
 *            The type of the locations of the input {@link IIcfg}.
 * @param <OUTLOC>
 *            The type of the locations of the output {@link IIcfg}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgTransformerSequence<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final IIcfg<OUTLOC> mResultIcfg;
	private final String mIdentifier;

	/**
	 * Default constructor.
	 *
	 * @param originalIcfg
	 *            an input {@link IIcfg}.
	 * @param funLocFacFirst
	 *            A location factory for creating new locations of type OUTLOC from old locations of type INLOC.
	 * @param funLocFacRest
	 *            A location factory for creating new locations of type OUTLOC from old locations of type OUTLOC.
	 * @param backtranslationTracker
	 *            A backtranslation tracker.
	 * @param outLocationClass
	 *            The class object of the type of locations of the output {@link IIcfg}.
	 * @param newIcfgIdentifier
	 *            The identifier of the new {@link IIcfg}
	 * @param transformers
	 *            The sequence of transformers that should be applied to each transformula of each transition of the
	 *            input {@link IIcfg} to create a new {@link IIcfg}.
	 */
	public IcfgTransformerSequence(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFacFirst, final ILocationFactory<OUTLOC, OUTLOC> funLocFacRest,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier, final List<ITransformulaTransformer> transformers) {
		mLogger = Objects.requireNonNull(logger);
		mIdentifier = newIcfgIdentifier;
		final Iterator<ITransformulaTransformer> iter = Objects.requireNonNull(transformers).iterator();
		if (iter.hasNext()) {
			final ITransformulaTransformer first = iter.next();
			final String ident = getIdentifier(iter, 1);
			final BasicIcfg<OUTLOC> intermediateIcfg =
					transform(logger, originalIcfg, funLocFacFirst, backtranslationTracker, outLocationClass, ident,
							first);
			mResultIcfg =
					transformRest(intermediateIcfg, funLocFacRest, backtranslationTracker, outLocationClass, iter);
		} else {
			throw new IllegalArgumentException("Cannot transform witout transformers");
		}
	}

	private BasicIcfg<OUTLOC> transformRest(final BasicIcfg<OUTLOC> outIcfg,
			final ILocationFactory<OUTLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final Iterator<ITransformulaTransformer> transformerIter) {
		BasicIcfg<OUTLOC> currentIcfg = outIcfg;
		int iteration = 1;
		while (transformerIter.hasNext()) {
			final ITransformulaTransformer transformer = transformerIter.next();
			iteration++;
			currentIcfg = transform(mLogger, currentIcfg, funLocFac, backtranslationTracker, outLocationClass,
					getIdentifier(transformerIter, iteration), transformer);
		}
		return currentIcfg;
	}

	private static <IN extends IcfgLocation, OUT extends IcfgLocation> BasicIcfg<OUT> transform(final ILogger logger,
			final IIcfg<IN> originalIcfg, final ILocationFactory<IN, OUT> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUT> outLocationClass,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer) {
		transformer.preprocessIcfg(originalIcfg);
		final BasicIcfg<OUT> resultIcfg =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		final TransformedIcfgBuilder<IN, OUT> lst =
				new TransformedIcfgBuilder<>(logger, funLocFac, backtranslationTracker, transformer, originalIcfg,
						resultIcfg);
		processLocations(originalIcfg.getInitialNodes(), lst);
		lst.finish();
		return resultIcfg;
	}

	private static <IN extends IcfgLocation, OUT extends IcfgLocation> void processLocations(final Set<IN> init,
			final TransformedIcfgBuilder<IN, OUT> lst) {

		final Deque<IN> open = new ArrayDeque<>(init);
		final Set<IN> closed = new HashSet<>();
		final List<Triple<OUT, OUT, IcfgEdge>> later = new ArrayList<>();
		while (!open.isEmpty()) {
			final IN oldSource = open.removeFirst();
			if (!closed.add(oldSource)) {
				continue;
			}

			final OUT newSource = lst.createNewLocation(oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				@SuppressWarnings("unchecked")
				final IN oldTarget = (IN) oldTransition.getTarget();
				open.add(oldTarget);
				final OUT newTarget = lst.createNewLocation(oldTarget);
				if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
					later.add(new Triple<>(newSource, newTarget, oldTransition));
				} else {
					lst.createNewTransition(newSource, newTarget, oldTransition);
				}

			}
		}

		later.forEach(a -> lst.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));
	}

	private String getIdentifier(final Iterator<ITransformulaTransformer> iter, final int iteration) {
		if (iter.hasNext()) {
			return mIdentifier + "_" + iteration;
		}
		return mIdentifier;
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}
