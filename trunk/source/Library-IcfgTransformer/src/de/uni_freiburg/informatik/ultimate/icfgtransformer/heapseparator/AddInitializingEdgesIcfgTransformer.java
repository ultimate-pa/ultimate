/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * IcfgTransformer that performs the following changes:
 *  <li> the original initial nodes are no more initial
 *  <li> a new initial node is introduced
 *  <li> new internal edges are introduces leading from the new initial node to the old ones
 *  <li> the new edge has a user-specified TransFormula  (passed in constructor of this class)
 *
 * The purpose is to add global initialization code to an IIcfg.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class AddInitializingEdgesIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final BasicIcfg<OUTLOC> mResultIcfg;

	final TransformedIcfgBuilder<INLOC, OUTLOC> mBuilder;

	private final UnmodifiableTransFormula mInitializingTransformula;

	public AddInitializingEdgesIcfgTransformer(final ILogger logger, final CfgSmtToolkit oldCsToolkit,
			final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass,
			final IIcfg<INLOC> originalIcfg,
			final UnmodifiableTransFormula initTf,
			final String newIcfgName) {

		mInitializingTransformula = initTf;

		final ITransformulaTransformer transformer = new IdentityTransformer(oldCsToolkit.getSymbolTable());

		mResultIcfg =
				new BasicIcfg<>(newIcfgName, originalIcfg.getCfgSmtToolkit(), outLocationClass);

		mBuilder =
				new TransformedIcfgBuilder<>(logger, funLocFac, backtranslationTracker, transformer, originalIcfg,
						mResultIcfg);

		process(originalIcfg, funLocFac, backtranslationTracker, outLocationClass, //"freezeVarsFrozen",
				transformer);
	}

	private void process(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final ITransformulaTransformer transformer) {

		transformer.preprocessIcfg(originalIcfg);

		processLocations(originalIcfg.getInitialNodes(), mBuilder);

		/*
		 * Create a new initial location and add an edge with initialization code to each of the old Icfg's intial
		 * locations.
		 */
		final OUTLOC newInitLoc = createAndAddNewInitLocation();
		for (final INLOC originalInitNode : originalIcfg.getInitialNodes()) {
			mBuilder.createNewInternalTransition(newInitLoc, mBuilder.getNewLoc(originalInitNode),
					mInitializingTransformula,
					false);
		}

		mBuilder.finish();
	}

	private OUTLOC createAndAddNewInitLocation() {
		final OUTLOC freshLoc = (OUTLOC) new IcfgLocation(this.getClass().toString(), null);

		// add fresh location to resultIcfg
		mResultIcfg.addLocation(freshLoc, true, false, false, false, false);

		return freshLoc;
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
				// make copies of the old locations, identical except that they are never initial
				final OUTLOC newTarget = lst.createNewLocation((INLOC) oldTransition.getTarget(), false);

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
