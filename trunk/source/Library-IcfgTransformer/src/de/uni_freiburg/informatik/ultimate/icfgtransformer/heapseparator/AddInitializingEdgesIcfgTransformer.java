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
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * The purpose of this class is to add initialization code for global program variables to an IIcfg.
 * <p>
 * Variant of an IcfgTransformer that adds initialization code to the input icfg, otherwise leaves the cfg as it is
 *  (IdentityTransformer as ITransformulaTransformer).
 * <p>
 * The initialization code is a constructor parameter (Transformula).
 * New edges are introduces that hold the initialization code.
 * Where the edge are introduced, depends on the type of each inital edge.
 * If the initial edge is a call, the new edge is inserted immediately after that call. If the initial edge is an
 * internal transition, the new edge is introduced before it.
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

		processLocationsOmitInitEdges(originalIcfg.getInitialNodes(), mBuilder);

		mBuilder.finish();
	}

	private OUTLOC createAndAddNewInitLocation(final INLOC originalInitNode) {
		// TODO: general solution.. this one works for BoogieIcfgLocations
		final String debugString = this.getClass().toString() + "freshInit" + originalInitNode.hashCode();
		final OUTLOC freshLoc = (OUTLOC) new BoogieIcfgLocation(debugString, originalInitNode.getProcedure(), false,
				((BoogieIcfgLocation) originalInitNode).getBoogieASTNode());

		// add fresh location to resultIcfg
		mResultIcfg.addLocation(freshLoc, true, false, false, false, false);

		return freshLoc;
	}

	private void processLocationsOmitInitEdges(final Set<INLOC> init, final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {

		final Set<IcfgEdge> initEdges = new HashSet<>();

		final IcfgLocationIterator<INLOC> iter = new IcfgLocationIterator<>(init);

		// we need to create new return transitions after new call transitions have been created
		final List<Triple<OUTLOC, OUTLOC, IcfgEdge>> rtrTransitions = new ArrayList<>();

		while (iter.hasNext()) {
			final INLOC oldSource = iter.next();



			final OUTLOC newSource = lst.createNewLocation(oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				@SuppressWarnings("unchecked")
				final OUTLOC newTarget = lst.createNewLocation((INLOC) oldTransition.getTarget());

				if (init.contains(oldSource)) {
					// collect init edges for later treatment
					initEdges.add(oldTransition);
					continue;
				}

				if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
					rtrTransitions.add(new Triple<>(newSource, newTarget, oldTransition));
				} else {
					lst.createNewTransition(newSource, newTarget, oldTransition);
				}
			}
		}

		for (final IcfgEdge initEdge : initEdges) {
			if (initEdge instanceof IcfgCallTransition) {
				// add an edge after the initEdge, split the init edge's target node
				final OUTLOC newInitEdgeTarget = createAndAddNewInitLocation((INLOC) initEdge.getTarget());

				final OUTLOC initEdgeSource = mBuilder.createNewLocation((INLOC) initEdge.getSource());

				final OUTLOC oldInitEdgeTargetInNewCfg = mBuilder.createNewLocation((INLOC) initEdge.getTarget());

				// the copy of the init edge leads to newInitEdgeTarget
				mBuilder.createNewTransition(initEdgeSource, newInitEdgeTarget, initEdge);

				/*
				 * insert the edge carrying the new initialization code between newInitEdgeTarget and
				 *  oldInitEdgeTargetInNewCfg
				 */
				mBuilder.createNewInternalTransition(newInitEdgeTarget, oldInitEdgeTargetInNewCfg,
					mInitializingTransformula, false);
			} else if (initEdge instanceof IcfgInternalTransition) {
				// add an edge before the init edge
				throw new UnsupportedOperationException("TOOD: implement this case");
			} else {
				throw new AssertionError("init edge is neither call nor internal transition");
			}
		}

		/*
		 * Delayed processing of return transitions, als they can only be processed once their corresponding call has
		 *  been processed
		 */
		rtrTransitions.forEach(a -> lst.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}
