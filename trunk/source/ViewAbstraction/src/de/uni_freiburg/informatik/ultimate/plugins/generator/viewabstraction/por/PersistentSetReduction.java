/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstraction plug-in.
 *
 * The ULTIMATE ViewAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.por;

import java.util.HashSet;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ProcedureMultiplier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IcfgDuplicator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ThreadBasedPersistentSets;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.ThreadSeparatingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule.RuleInstance;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IThreadBasedConfiguration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class PersistentSetReduction<T, C extends IThreadBasedConfiguration<T, C>> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final BoogieIcfgContainer mOriginalIcfg;
	private final IIndependenceRelation<?, ? super CodeBlock> mIndependence;
	private final int mThreadInstanceCount;

	private final Function<T, IcfgLocation> mGetThreadLocation;
	private final Function<CodeBlock, IRule<C>> mEdge2Rule;

	private final String mMainProcedure;

	// TODO preference order used by sleep sets, if applicable
	private final IDfsOrder<IcfgEdge, ?> mDfsOrder = null;

	private final BasicIcfg<IcfgLocation> mDuplicatedIcfg;
	private Function<IcfgEdge, CodeBlock> mGetOriginalEdge;
	private BiFunction<IcfgLocation, String, IcfgLocation> mGetNewLocation;

	private final Program<C> mReducedProgram;
	private final IPersistentSetChoice<RuleInstance<C>, C> mPersistentSets;

	public PersistentSetReduction(final IUltimateServiceProvider services, final BoogieIcfgContainer icfg,
			final Program<C> program, final IIndependenceRelation<?, IcfgEdge> independence,
			final int threadInstanceCount, final Function<T, IcfgLocation> getThreadLocation,
			final Function<CodeBlock, IRule<C>> edge2Rule) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(PersistentSetReduction.class);
		mOriginalIcfg = icfg;
		mIndependence = independence;
		mThreadInstanceCount = threadInstanceCount;
		mGetThreadLocation = getThreadLocation;
		mEdge2Rule = edge2Rule;

		mMainProcedure =
				DataStructureUtils.getOneAndOnly(mOriginalIcfg.getInitialNodes(), "initial node").getProcedure();
		mDuplicatedIcfg = createIcfgWithThreadInstances();

		mPersistentSets = getPersistentSets();
		final var reducedRules = program.getRules().stream().map(r -> new PersistentRule<>(r, mPersistentSets))
				.collect(Collectors.toList());
		mReducedProgram = new Program<>(reducedRules);
	}

	public Program<C> getReducedProgram() {
		return mReducedProgram;
	}

	public IStatisticsDataProvider getStatistics() {
		return mPersistentSets.getStatistics();
	}

	private BasicIcfg<IcfgLocation> createIcfgWithThreadInstances() {
		final var duplicator =
				new IcfgDuplicator(mLogger, mServices, mOriginalIcfg.getCfgSmtToolkit().getManagedScript(),
						new BlockEncodingBacktranslator(IcfgEdge.class, Term.class, mLogger));
		final var duplicatedIcfg = duplicator.copy(mOriginalIcfg, "_Persistent", true);
		final var locationCopyMap = duplicator.getOld2NewLocationMapping();

		final var originalInitial = Set.copyOf(duplicatedIcfg.getInitialNodes());

		final var edgeMap = new BidirectionalMap<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>>();
		edgeMap.putAll(duplicator.getOld2NewEdgeMapping());
		final var edgeNew2OldMap = edgeMap.inverse();

		// create copies of initial procedure
		final var copyDirectives = new HashRelation<String, String>();
		for (int i = 0; i < mThreadInstanceCount; ++i) {
			copyDirectives.addPair(mMainProcedure, getThreadInstanceName(i));
		}
		final var multiplier = new ProcedureMultiplier(mServices, duplicatedIcfg, copyDirectives);

		// Only the copies of the initial procedure shall be initial, not the original itself.
		duplicatedIcfg.makeNonInitial(originalInitial);

		// create mappings for translation
		mGetOriginalEdge = edge -> (CodeBlock) edgeNew2OldMap.get(multiplier.getOriginalEdge(edge));
		mGetNewLocation = (loc, procCopy) -> multiplier.getDuplicatedLocation(locationCopyMap.get(loc), procCopy);

		return duplicatedIcfg;
	}

	private IPersistentSetChoice<RuleInstance<C>, C> getPersistentSets() {
		// Make sure two actions from the same thread copy are not considered independent.
		final var independence = new ThreadSeparatingIndependenceRelation<>(new PetrifiedIndependence<>());

		// Create a persistent set computation that works in mDuplicatedIcfg
		// TODO see how to handle error locations
		final var underlyingPersistent = new CachedPersistentSetChoice<>(
				new ThreadBasedPersistentSets<>(mServices, mDuplicatedIcfg, independence, null, Set.of()),
				pred -> ((IMLPredicate) pred).getProgramPoints());

		// used to create MLPredicates from configurations of type C
		final var factory = new PredicateFactory(mServices, mDuplicatedIcfg.getCfgSmtToolkit().getManagedScript(),
				mDuplicatedIcfg.getCfgSmtToolkit().getSymbolTable());

		return new PetrifiedPersistentSets(underlyingPersistent, factory);
	}

	private String getThreadInstanceName(final int thread) {
		return mMainProcedure + "~inst" + thread;
	}

	private class PetrifiedIndependence<S> implements IIndependenceRelation<S, IcfgEdge> {
		@Override
		public boolean isSymmetric() {
			return mIndependence.isSymmetric();
		}

		@Override
		public boolean isConditional() {
			return false;
		}

		@Override
		public Dependence isIndependent(final Object state, final IcfgEdge a, final IcfgEdge b) {
			final CodeBlock originalA = mGetOriginalEdge.apply(a);
			assert originalA != null : "could not determine original edge for " + a;
			final CodeBlock originalB = mGetOriginalEdge.apply(b);
			assert originalB != null : "could not determine original edge for " + b;
			return mIndependence.isIndependent(null, originalA, originalB);
		}

		@Override
		public IStatisticsDataProvider getStatistics() {
			return mIndependence.getStatistics();
		}
	}

	private class PetrifiedPersistentSets implements IPersistentSetChoice<RuleInstance<C>, C> {
		private final IPersistentSetChoice<IcfgEdge, IPredicate> mUnderlying;
		private final PredicateFactory mFactory;

		public PetrifiedPersistentSets(final IPersistentSetChoice<IcfgEdge, IPredicate> underlying,
				final PredicateFactory factory) {
			mUnderlying = underlying;
			mFactory = factory;
		}

		@Override
		public Set<RuleInstance<C>> persistentSet(final C configuration) {
			final var mlPred = makePetrifiedLocations(configuration);
			final var persistent = mUnderlying.persistentSet(mlPred);
			if (persistent == null) {
				return null;
			}

			final var result = new HashSet<RuleInstance<C>>();
			for (final var edgeCopy : persistent) {
				final var cb = mGetOriginalEdge.apply(edgeCopy);
				final var rule = mEdge2Rule.apply(cb);

				// TODO find a less hacky way
				final int thread =
						Integer.parseInt(edgeCopy.getPrecedingProcedure().substring(mMainProcedure.length() + 5));

				result.add(new RuleInstance<>(rule, thread));
			}
			persistent.stream().map(mGetOriginalEdge).map(mEdge2Rule);

			return result;
		}

		private IMLPredicate makePetrifiedLocations(final C configuration) {
			final IcfgLocation[] locations = new IcfgLocation[configuration.numberOfThreads()];
			for (int i = 0; i < configuration.numberOfThreads(); ++i) {
				final var originalLocation = mGetThreadLocation.apply(configuration.getThread(i));
				locations[i] = mGetNewLocation.apply(originalLocation, getThreadInstanceName(i));
			}
			return mFactory.newMLDontCarePredicate(locations);
		}

		@Override
		public IStatisticsDataProvider getStatistics() {
			return mUnderlying.getStatistics();
		}
	}
}