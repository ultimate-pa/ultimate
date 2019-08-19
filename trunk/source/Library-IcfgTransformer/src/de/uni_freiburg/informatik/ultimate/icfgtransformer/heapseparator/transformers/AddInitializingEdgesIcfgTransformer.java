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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.SuffixedDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * The purpose of this class is to add initialization code for global program variables to an IIcfg.
 * <p>
 * Variant of an IcfgTransformer that adds initialization code to the input icfg, otherwise leaves the cfg as it is
 * (IdentityTransformer as ITransformulaTransformer).
 * <p>
 * The initialization code is a constructor parameter (Transformula). New edges are introduces that hold the
 * initialization code. Where the edge are introduced, depends on the type of each inital edge. If the initial edge is a
 * call, the new edge is inserted immediately after that call. If the initial edge is an internal transition, the new
 * edge is introduced before it.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class AddInitializingEdgesIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final BasicIcfg<OUTLOC> mResultIcfg;

	final TransformedIcfgBuilder<INLOC, OUTLOC> mBuilder;

	private final UnmodifiableTransFormula mInitializingTransformula;

	private final IIcfg<INLOC> mInputIcfg;

	public AddInitializingEdgesIcfgTransformer(final ILogger logger, final CfgSmtToolkit oldCsToolkit,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final IIcfg<INLOC> originalIcfg,
			final UnmodifiableTransFormula initTf, final String newIcfgName) {

		mInitializingTransformula = initTf;

		final ITransformulaTransformer transformer = new IdentityTransformer(oldCsToolkit);

		mResultIcfg = new BasicIcfg<>(newIcfgName, originalIcfg.getCfgSmtToolkit(), outLocationClass);

		mBuilder = new TransformedIcfgBuilder<>(logger, funLocFac, backtranslationTracker, transformer, originalIcfg,
				mResultIcfg);

		mInputIcfg = originalIcfg;

		process(originalIcfg, funLocFac, backtranslationTracker, outLocationClass);
	}

	private void process(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass) {

		processLocationsOmitInitEdges(originalIcfg.getInitialNodes(), mBuilder);

		mBuilder.finish();
	}

	private void processLocationsOmitInitEdges(final Set<INLOC> initLocations,
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst) {

		final Set<IcfgEdge> initEdges = new HashSet<>();
		final HashRelation<IcfgEdge, IcfgEdge> edgesSucceedingInitEdges = new HashRelation<>();

		final IcfgLocationIterator<INLOC> iter = new IcfgLocationIterator<>(initLocations);

		// we need to create new return transitions after new call transitions have been created
		final List<Triple<OUTLOC, OUTLOC, IcfgEdge>> rtrTransitions = new ArrayList<>();

		/*
		 * recreate the full icfg like the input icfg (via calls to lst), except for
		 *  - return edges (which are cached, as usual in icfgtransformers, and reproduced after this loop)
		 *  - initial edges
		 *  - edges directly succeeding initial edges
		 *   the latter two are saved for further processing
		 */
		while (iter.hasNext()) {
			final INLOC oldSource = iter.next();

			outer: for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {

				// do not treat init edges here, collect them instead
				if (initLocations.contains(oldSource)) {
					// collect init edges for later treatment
					initEdges.add(oldTransition);
					continue;
				}

				// also do not treat edges directly after an init edge here, collect them, too
				for (final IcfgEdge incomingEdge : oldSource.getIncomingEdges()) {
					if (initLocations.contains(incomingEdge.getSource())) {
						// incomingEdge is an initial edge
						edgesSucceedingInitEdges.addPair(incomingEdge, oldTransition);
						continue outer;
					}
				}
				@SuppressWarnings("unchecked")
				final OUTLOC newTarget = lst.createNewLocation((INLOC) oldTransition.getTarget());
				final OUTLOC newSource = lst.createNewLocation(oldSource);

				if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
					rtrTransitions.add(new Triple<>(newSource, newTarget, oldTransition));
				} else {
					lst.createNewTransition(newSource, newTarget, oldTransition);
				}
			}
		}

		assert initEdges.stream().map(e -> e.getTarget()).collect(Collectors.toSet()).size() == initEdges
				.size() : "two init edges leading to the same location??";

		for (final IcfgEdge initEdge : initEdges) {
			if (initEdge instanceof IcfgCallTransition) {
				/*
				 * basic idea:
				 * <li> split target location of each init edge in two, say s1, s2
				 * <li> connect the splits
				 *  with an edge holding the initialization code
				 * <li> the edge properties have to be correctly split up, too: s1 is procedure entry location, s2 is
				 *  not, s2 takes over all other flags from the original init edge target (loop entry, proc exit etc)
				 *  neither should be an init location (assertion)
				 * <li> both locations are fresh
				 * <li> both locations take over BoogieASTNode, procedure from the original init target
				 */

				// add an edge after the initEdge, split the init edge's target node
				final INLOC oldInitTarget = (INLOC) initEdge.getTarget();
				assert oldInitTarget.getIncomingEdges().size() == 1;

				// the source of the init edge is unchanged
				final OUTLOC initEdgeSource = mBuilder.createNewLocation((INLOC) initEdge.getSource());

//				assert !mBuilder.hasNewLoc(oldInitTarget) : "init edge target should not have been recreated " + "here";



				final String succeedingProcedureAfterInitEdge = initEdge.getSucceedingProcedure();
				final Pair<OUTLOC, OUTLOC> split = splitLocation(oldInitTarget, succeedingProcedureAfterInitEdge);

				// final OUTLOC oldInitEdgeTargetInNewCfg = mBuilder.createNewLocation((INLOC) initEdge.getTarget());

				// the copy of the init edge leads to newInitEdgeTarget
				mBuilder.createNewTransition(initEdgeSource, split.getFirst(), initEdge);

				/*
				 * insert the edge carrying the new initialization code between newInitEdgeTarget and
				 * oldInitEdgeTargetInNewCfg
				 */
				mBuilder.createNewInternalTransition(split.getFirst(), split.getSecond(), mInitializingTransformula, false);

				/*
				 * recreate the outgoing transitions of the original init edge, now outgoing from s2
				 */
				for (final IcfgEdge succEdge : edgesSucceedingInitEdges.getImage(initEdge)) {
					mBuilder.createNewTransition(split.getSecond(),
							mBuilder.createNewLocation((INLOC) succEdge.getTarget()), succEdge);
				}
			} else if (initEdge instanceof IcfgInternalTransition) {
				/*
				 *  add an edge before the init edge
				 *   - split init location in two
				 *   - create new edge e, insert as (split1, e, split2)
				 *   - insert init edge as (split2, initedge, oldinitedgetarget)
				 */
				final INLOC oldInitSource = (INLOC) initEdge.getSource();
				final INLOC oldInitTarget = (INLOC) initEdge.getTarget();

				final Pair<OUTLOC, OUTLOC> split = splitLocation(oldInitSource, initEdge.getSucceedingProcedure());

				mBuilder.createNewInternalTransition(split.getFirst(), split.getSecond(), mInitializingTransformula,
						false);

				mBuilder.createNewTransition(split.getSecond(), mBuilder.createNewLocation(oldInitTarget), initEdge);

				/*
				 * recreate the outgoing transitions of the original init edge, still outgoing from s2
				 * (doing this because the "initEdge instanceof IcfgCallTransition" case works this way)
				 */
				for (final IcfgEdge succEdge : edgesSucceedingInitEdges.getImage(initEdge)) {
					mBuilder.createNewTransition(mBuilder.createNewLocation(oldInitTarget),
							mBuilder.createNewLocation((INLOC) succEdge.getTarget()), succEdge);
				}


			} else {
				throw new AssertionError("init edge is neither call nor internal transition");
			}
		}

		/*
		 * Delayed processing of return transitions, also, they can only be processed once their corresponding call has
		 * been processed
		 */
		rtrTransitions.forEach(a -> lst.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));
	}

	private Pair<OUTLOC, OUTLOC> splitLocation(final INLOC oldInitTarget, final String containingprocedure) {
		Pair<OUTLOC, OUTLOC> p;
		{
			final boolean wasProcedureEntryNode = !mInputIcfg.getProcedureEntryNodes().isEmpty()
					&& mInputIcfg.getProcedureEntryNodes().get(containingprocedure).equals(oldInitTarget);
			final OUTLOC s1 = createAndAddNewLocation(oldInitTarget,
					mInputIcfg.getInitialNodes().contains(oldInitTarget),
					false,
					wasProcedureEntryNode,
					false,
					false,
					new SuffixedDebugIdentifier(oldInitTarget.getDebugIdentifier(), "_split-1"));

			final boolean wasProcedureExitNode = !mInputIcfg.getProcedureExitNodes().isEmpty()
					&& mInputIcfg.getProcedureExitNodes().get(containingprocedure).equals(oldInitTarget);
			final OUTLOC s2 = createAndAddNewLocation(oldInitTarget, false,
					mInputIcfg.getProcedureErrorNodes().get(containingprocedure)
					.contains(oldInitTarget),
					false,
					wasProcedureExitNode,
					mInputIcfg.getLoopLocations().contains(oldInitTarget),
					new SuffixedDebugIdentifier(oldInitTarget.getDebugIdentifier(), "_split-2"));
			p = new Pair<>(s1, s2);
		}
		return p;
	}

	private OUTLOC createAndAddNewLocation(final INLOC originalInitNode, final boolean isInitial, final boolean isError,
			final boolean isProcEntry, final boolean isProcExit, final boolean isLoopLocation,
			final DebugIdentifier locName) {
		// TODO: general solution.. this one works for BoogieIcfgLocations
		// final String debugString = this.getClass().toString() + "freshInit" + originalInitNode.hashCode();
		final OUTLOC freshLoc = (OUTLOC) new BoogieIcfgLocation(locName, originalInitNode.getProcedure(), false,
				((BoogieIcfgLocation) originalInitNode).getBoogieASTNode());

		// add fresh location to resultIcfg
		mResultIcfg.addLocation(freshLoc, isInitial, isError, isProcEntry, isProcExit, isLoopLocation);

		return freshLoc;
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}
