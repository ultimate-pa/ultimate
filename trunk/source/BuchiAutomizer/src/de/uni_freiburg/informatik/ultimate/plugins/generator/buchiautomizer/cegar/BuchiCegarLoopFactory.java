/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.Collections;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainExceptionWrapper;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.AmpleRedAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.NwaInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.Petri2FiniteAutomatonAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PetriInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PetriLbeInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.AbstractionType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.IcfgCompositionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.AutomatonTypeConcurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IWitnessTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WitnessAutomatonAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.IndependenceProviderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <L>
 */
public class BuchiCegarLoopFactory<L extends IIcfgTransition<?>> {
	// Dominik (2025-03-21): Mostly for statistics evaluation.
	// TODO Remove this behaviour after evaluation, or make it into a proper setting.
	private static final boolean USE_EAGER_PRODUCT = false;

	private final IUltimateServiceProvider mServices;
	private final TAPreferences mPrefs;
	private final Class<L> mTransitionClazz;
	private final ICopyActionFactory<L> mCopyFactory;
	private int mNumberOfConstructions;

	private IndependenceProviderFactory<L> mIndependenceProviderFactory;

	public BuchiCegarLoopFactory(final IUltimateServiceProvider services, final TAPreferences taPrefs,
			final Class<L> transitionClazz, final ICopyActionFactory<L> copyFactory) {
		mServices = services;
		mPrefs = taPrefs;
		mTransitionClazz = transitionClazz;
		mCopyFactory = copyFactory;
		mNumberOfConstructions = 0;
	}

	public AbstractBuchiCegarLoop<L, ?> constructCegarLoop(final IIcfg<?> icfg,
			final IWitnessTransformer<L> witnessTransformer,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		final String variableSuffix = mNumberOfConstructions > 0 ? Integer.toString(mNumberOfConstructions) : "";
		mNumberOfConstructions++;
		final RankVarConstructor rankVarConstructor = new RankVarConstructor(icfg.getCfgSmtToolkit(), variableSuffix);
		final PredicateFactory predicateFactory =
				new PredicateFactory(mServices, icfg.getCfgSmtToolkit().getManagedScript(),
						rankVarConstructor.getCsToolkitWithRankVariables().getSymbolTable());
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(mServices,
				rankVarConstructor.getCsToolkitWithRankVariables().getManagedScript(), predicateFactory, false,
				Collections.emptySet());
		if (!IcfgUtils.isConcurrent(icfg)) {
			final IInitialAbstractionProvider<L, INestedWordAutomaton<L, IPredicate>> automatonProvider =
					new NwaInitialAbstractionProvider<>(mServices, stateFactoryForRefinement, true, predicateFactory,
							mPrefs.getHoareSettings());
			return createBuchiAutomatonCegarLoop(icfg, rankVarConstructor, predicateFactory, witnessTransformer,
					stateFactoryForRefinement, automatonProvider, benchmarkGenerator);
		}
		final var petriNetProvider = constructPetriNetProvider(predicateFactory, icfg);
		final AutomatonTypeConcurrent automatonTypeConcurrent = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_AUTOMATON_TYPE, AutomatonTypeConcurrent.class);
		switch (automatonTypeConcurrent) {
		case BUCHI_AUTOMATON:
		case PARTIAL_ORDER_BA:
			final var automatonProvider = createAutomatonProvider(petriNetProvider, automatonTypeConcurrent,
					stateFactoryForRefinement, predicateFactory);
			return createBuchiAutomatonCegarLoop(icfg, rankVarConstructor, predicateFactory, witnessTransformer,
					stateFactoryForRefinement, automatonProvider, benchmarkGenerator);
		case BUCHI_PETRI_NET:
			return new BuchiPetriNetCegarLoop<>(icfg, rankVarConstructor, predicateFactory, mPrefs, mServices,
					mTransitionClazz, constructInitialAbstraction(petriNetProvider, icfg, benchmarkGenerator),
					benchmarkGenerator);
		// case RABIN_PETRI_NET:
		// return new RabinPetriNetCegarLoop<>(icfg, rankVarConstructor, predicateFactory, mPrefs, mServices,
		// mTransitionClazz, new RabinPetriNetWrapper<>(constructInitialAbstraction(petriNetProvider, icfg)),
		// mCegarLoopBenchmark);
		default:
			throw new UnsupportedOperationException(
					"The type " + automatonTypeConcurrent + " is currently not supported.");
		}
	}

	private IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>>
			createAutomatonProvider(final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> petriProvider,
					final AutomatonTypeConcurrent automatonType,
					final PredicateFactoryRefinement stateFactoryForRefinement,
					final PredicateFactory predicateFactory) {
		final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> productProvider;
		if (USE_EAGER_PRODUCT) {
			productProvider = new Petri2FiniteAutomatonAbstractionProvider.Eager<>(mServices, petriProvider,
					stateFactoryForRefinement);
		} else {
			productProvider = new Petri2FiniteAutomatonAbstractionProvider.Lazy<>(mServices, petriProvider,
					stateFactoryForRefinement);
		}

		return switch (automatonType) {
		case BUCHI_AUTOMATON -> productProvider;
		// TODO: Statistics, Check if input automaton meets requirements?
		case PARTIAL_ORDER_BA -> new AmpleRedAbstractionProvider<>(productProvider, mServices,
				stateFactoryForRefinement, icfg -> constructIndependenceRelation(predicateFactory, icfg));
		case BUCHI_PETRI_NET, RABIN_PETRI_NET ->
				throw new AssertionError("Petri nets should be handled elsewhere: " + automatonType);
		};
	}

	private IIndependenceRelation<IPredicate, L> constructIndependenceRelation(final PredicateFactory predicateFactory,
			final IIcfg<?> icfg) {
		if (mPrefs.getNumberOfIndependenceRelations() != 1) {
			throw new UnsupportedOperationException("Multiple independence relations are not supported");
		}
		if (mPrefs.porIndependenceSettings(0).getAbstractionType() != AbstractionType.NONE) {
			throw new UnsupportedOperationException("Abstract independence relations are not supported");
		}

		// If multiple independence relations are created, possibly for different ICFGs, shutdown the old factory and
		// create a new one.
		if (mIndependenceProviderFactory != null) {
			mIndependenceProviderFactory.shutdown();
		}

		mIndependenceProviderFactory = new IndependenceProviderFactory<>(mServices, mPrefs, mCopyFactory);
		final var providers = mIndependenceProviderFactory.createProviders(icfg, predicateFactory);
		assert providers.size() == 1 : "Expected one independence provider, but got " + providers.size();

		final var provider = providers.getFirst();
		provider.initialize();
		return provider.retrieveIndependence();
	}

	@SuppressWarnings("unchecked")
	private IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>>
			constructPetriNetProvider(final PredicateFactory predicateFactory, final IIcfg<?> icfg) {
		final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> petriNetProvider =
				new PetriInitialAbstractionProvider<>(mServices, predicateFactory, true);
		if (!mPrefs.applyOneShotLbe()) {
			return petriNetProvider;
		}
		return new PetriLbeInitialAbstractionProvider<>(mServices, petriNetProvider, mTransitionClazz,
				mPrefs.lbeIndependenceSettings(),
				(IPLBECompositionFactory<L>) new IcfgCompositionFactory(mServices, icfg.getCfgSmtToolkit()));
	}

	private BuchiAutomatonCegarLoop<L> createBuchiAutomatonCegarLoop(final IIcfg<?> icfg,
			final RankVarConstructor rankVarConstructor, final PredicateFactory predicateFactory,
			final IWitnessTransformer<L> witnessTransformer, final PredicateFactoryRefinement stateFactory,
			IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> provider,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		if (witnessTransformer != null) {
			provider = new WitnessAutomatonAbstractionProvider<>(predicateFactory, provider, witnessTransformer);
		}
		return new BuchiAutomatonCegarLoop<>(icfg, rankVarConstructor, predicateFactory, mPrefs, mServices,
				mTransitionClazz, constructInitialAbstraction(provider, icfg, benchmarkGenerator), stateFactory,
				benchmarkGenerator);
	}

	private static Set<IcfgLocation> getAcceptingStates(final IIcfg<?> icfg) {
		final Set<IcfgLocation> allStates =
				icfg.getProgramPoints().values().stream().flatMap(x -> x.values().stream()).collect(Collectors.toSet());
		if (LTLPropertyCheck.getAnnotation(icfg) == null) {
			return allStates;
		}
		return allStates.stream().filter(a -> BuchiProgramAcceptingStateAnnotation.getAnnotation(a) != null)
				.collect(Collectors.toSet());
	}

	private <A extends IAutomaton<L, IPredicate>> A constructInitialAbstraction(
			final IInitialAbstractionProvider<L, A> provider, final IIcfg<?> icfg,
			final BuchiCegarLoopBenchmarkGenerator benchmark) {
		// OverallTime should include InitialAbstractionConstructionTime. Hence we start and stop both stopwatches.
		benchmark.start(CegarLoopStatisticsDefinitions.OverallTime);
		benchmark.start(CegarLoopStatisticsDefinitions.InitialAbstractionConstructionTime);
		try {
			final var abstraction = provider.getInitialAbstraction(icfg, getAcceptingStates(icfg));
			benchmark.addInitialAbstractionStatistics(provider.getStatistics());
			return abstraction;
		} catch (final AutomataOperationCanceledException ex) {
			final RunningTaskInfo runningTaskInfo =
					new RunningTaskInfo(this.getClass(), "constructing initial abstraction");
			ex.addRunningTaskInfo(runningTaskInfo);
			throw new ToolchainExceptionWrapper(Activator.PLUGIN_ID, ex);
		} catch (final ToolchainCanceledException ex) {
			final RunningTaskInfo runningTaskInfo =
					new RunningTaskInfo(this.getClass(), "constructing initial abstraction");
			ex.addRunningTaskInfo(runningTaskInfo);
			throw ex;
		} catch (final AutomataLibraryException e) {
			throw new ToolchainExceptionWrapper(Activator.PLUGIN_ID, e);
		} finally {
			benchmark.stop(CegarLoopStatisticsDefinitions.InitialAbstractionConstructionTime);
			benchmark.stop(CegarLoopStatisticsDefinitions.OverallTime);
		}
	}

	public void shutdown() {
		if (mIndependenceProviderFactory != null) {
			mIndependenceProviderFactory.shutdown();
		}
	}
}
