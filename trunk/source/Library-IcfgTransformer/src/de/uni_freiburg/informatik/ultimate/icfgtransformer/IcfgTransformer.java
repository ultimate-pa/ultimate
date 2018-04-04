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

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * A basic {@link IIcfgTransformer} that applies some {@link ITransformulaTransformer} to each transformula of an input
 * {@link IIcfg} and thus creates a new {@link IIcfg}.
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final IIcfg<OUTLOC> mResultIcfg;
	private final ILogger mLogger;

	/**
	 * Default constructor.
	 *
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
	 */
	public IcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer) {
		mLogger = Objects.requireNonNull(logger);
		mResultIcfg = transform(originalIcfg, funLocFac, backtranslationTracker, outLocationClass, newIcfgIdentifier,
				transformer);
	}

	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer) {
		transformer.preprocessIcfg(originalIcfg);
		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst =
				new TransformedIcfgBuilder<>(mLogger, funLocFac, backtranslationTracker, transformer, originalIcfg,
						resultIcfg);
		processLocations(originalIcfg.getInitialNodes(), lst);
		lst.finish();
		return resultIcfg;
	}

	private void processLocations(final Set<INLOC> init, final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {
		final IcfgLocationIterator<INLOC> iter = new IcfgLocationIterator<>(init);

		// we need to create new return transitions after new call transitions have been created
		final List<Triple<OUTLOC, OUTLOC, IcfgEdge>> rtrTransitions = new ArrayList<>();

		while (iter.hasNext()) {
			final INLOC oldSource = iter.next();
			final OUTLOC newSource = lst.createNewLocation(oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				@SuppressWarnings("unchecked")
				final OUTLOC newTarget = lst.createNewLocation((INLOC) oldTransition.getTarget());
				if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
					rtrTransitions.add(new Triple<>(newSource, newTarget, oldTransition));
				} else {
					lst.createNewTransition(newSource, newTarget, oldTransition);
				}
			}
		}

		rtrTransitions.forEach(a -> lst.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}

}
