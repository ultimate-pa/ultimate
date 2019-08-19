/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Transform an {@link Icfg} by TODO (Back)transform a proof for the large block encoded {@link Icfg} to a proof for the
 * original {@link Icfg} by TODO
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class BranchUnfoldIcfgTransformer {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final PredicateFactory mPredicateFactory;
	private final IPredicateUnifier mPredicateUnifier;
	/**
	 * Map that assigns to each large block encoded icfg location the corresponding location in the orginal icfg
	 */
	private IIcfg<IcfgLocation> mInputIcfg;

	private final HashRelation<IcfgLocation, IcfgLocation> mOldLoc2NewLoc = new HashRelation<>();
	private BasicIcfg<IcfgLocation> mResultIcfg;
	private ArrayDeque<Pair<IcfgLocation, Integer>> mWorklist;
	// private HashSet<Pair<IcfgLocation, Integer>> mVisited;

	public BranchUnfoldIcfgTransformer(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mPredicateFactory = predicateFactory;
		mPredicateUnifier = predicateUnifier;
	}

	public IIcfg<IcfgLocation> transform(final IIcfg<IcfgLocation> inputIcfg) {
		mInputIcfg = inputIcfg;

		final IValueConstruction<IcfgEdge, Integer> edgeNumberVc = new IValueConstruction<IcfgEdge, Integer>() {
			int mCounter = 0;

			@Override
			public Integer constructValue(final IcfgEdge key) {
				return mCounter++;
			}
		};

		final ConstructionCache<IcfgEdge, Integer> edgeNumberConstructor = new ConstructionCache<>(edgeNumberVc);

		final IValueConstruction<Pair<IcfgLocation, Integer>, IcfgLocation> resultLocationVc =
				new IValueConstruction<Pair<IcfgLocation, Integer>, IcfgLocation>() {

					@Override
					public IcfgLocation constructValue(final Pair<IcfgLocation, Integer> pair) {
						final IcfgLocation inputLoc = pair.getFirst();
						final boolean initial = mInputIcfg.getInitialNodes().contains(inputLoc);
						final BranchUnfoldDebugIdentifier debugIdentifier = new BranchUnfoldDebugIdentifier(
								inputLoc.getDebugIdentifier(), this.getClass(), pair.getSecond());
						final IcfgLocation resultLoc = new IcfgLocation(debugIdentifier, inputLoc.getProcedure());
						final boolean isInitial = initial;
						final boolean isError =
								mInputIcfg.getProcedureErrorNodes().get(inputLoc.getProcedure()).contains(inputLoc);
						final boolean isProcEntry = initial;
						final boolean isProcExit = false;
						final boolean isLoopLocation = mInputIcfg.getLoopLocations().contains(inputLoc);
						mResultIcfg.addLocation(resultLoc, isInitial, isError, isProcEntry, isProcExit, isLoopLocation);
						mOldLoc2NewLoc.addPair(inputLoc, resultLoc);
						// if (!mVisited.contains(pair)) {
						// mVisited.add(pair);
						mWorklist.add(pair);
						// }
						return resultLoc;
					}
				};

		final ConstructionCache<Pair<IcfgLocation, Integer>, IcfgLocation> resultLocationConstructor =
				new ConstructionCache<>(resultLocationVc);

		final String identifier = inputIcfg.getIdentifier() + this.getClass();
		mResultIcfg = new BasicIcfg<>(identifier, inputIcfg.getCfgSmtToolkit(), IcfgLocation.class);
		final IcfgEdgeFactory edgeFac = mResultIcfg.getCfgSmtToolkit().getIcfgEdgeFactory();
		mWorklist = new ArrayDeque<>();
		// mVisited = new HashSet<>();
		for (final IcfgLocation loc : mInputIcfg.getInitialNodes()) {
			final Pair<IcfgLocation, Integer> initialPair = new Pair<>(loc, 0);
			resultLocationConstructor.getOrConstruct(initialPair);
		}
		while (!mWorklist.isEmpty()) {
			final Pair<IcfgLocation, Integer> some = mWorklist.removeFirst();
			final IcfgLocation sourceLoc = resultLocationConstructor.getOrConstruct(some);
			for (final IcfgEdge edge : some.getFirst().getOutgoingEdges()) {
				final Integer edgeNumber = edgeNumberConstructor.getOrConstruct(edge);
				final Pair<IcfgLocation, Integer> targetPair = new Pair<>(edge.getTarget(), edgeNumber);
				final IcfgLocation targetLoc = resultLocationConstructor.getOrConstruct(targetPair);

				final IcfgInternalTransition newEdge =
						edgeFac.createInternalTransition(sourceLoc, targetLoc, new Payload(), edge.getTransformula());
				sourceLoc.addOutgoing(newEdge);
				newEdge.setSource(sourceLoc);
				newEdge.setTarget(targetLoc);
				targetLoc.addIncoming(newEdge);
			}
		}
		return mResultIcfg;
	}

	public Map<IcfgLocation, IPredicate> transform(final Map<IcfgLocation, IPredicate> hoareAnnotation) {
		final Map<IcfgLocation, IPredicate> result = new HashMap<>();
		for (final IcfgLocation oldLoc : mOldLoc2NewLoc.getDomain()) {
			final List<IPredicate> preds = new ArrayList<>();
			for (final IcfgLocation newLoc : mOldLoc2NewLoc.getImage(oldLoc)) {
				preds.add(hoareAnnotation.get(newLoc));
			}
			result.put(oldLoc, mPredicateFactory.or(preds));

		}
		mInputIcfg = null;
		return result;
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class BranchUnfoldDebugIdentifier extends DebugIdentifier {

		private final int mNumber;
		private final Class<?> mCreatingClass;
		private final DebugIdentifier mOriginalIdentifier;

		public BranchUnfoldDebugIdentifier(final DebugIdentifier originalIdentifier, final Class<?> creatingClass,
				final int number) {
			// TODO: Matthias, check if this is what you need here
			mNumber = number;
			mCreatingClass = creatingClass;
			mOriginalIdentifier = originalIdentifier;
		}

		@Override
		public String toString() {
			return mOriginalIdentifier.toString() + mCreatingClass.getSimpleName() + mNumber;
		}

	}

}
