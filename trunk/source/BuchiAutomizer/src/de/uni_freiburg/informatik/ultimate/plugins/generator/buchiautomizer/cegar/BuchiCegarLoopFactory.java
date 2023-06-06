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
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
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
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.NwaInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.Petri2FiniteAutomatonAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PetriInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PetriLbeInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.IcfgCompositionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.AutomatonTypeConcurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WitnessAutomatonAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessUtils.Property;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <L>
 */
public class BuchiCegarLoopFactory<L extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final TAPreferences mPrefs;
	private final BuchiCegarLoopBenchmarkGenerator mCegarLoopBenchmark;
	private final Class<L> mTransitionClazz;
	private int mNumberOfConstructions;

	public BuchiCegarLoopFactory(final IUltimateServiceProvider services, final TAPreferences taPrefs,
			final Class<L> transitionClazz, final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		mServices = services;
		mPrefs = taPrefs;
		mTransitionClazz = transitionClazz;
		mCegarLoopBenchmark = benchmarkGenerator;
		mNumberOfConstructions = 0;
	}

	public AbstractBuchiCegarLoop<L, ?> constructCegarLoop(final IIcfg<?> icfg,
			final INestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
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
					new NwaInitialAbstractionProvider<>(mServices, stateFactoryForRefinement, true, predicateFactory);
			return createBuchiAutomatonCegarLoop(icfg, rankVarConstructor, predicateFactory, witnessAutomaton,
					stateFactoryForRefinement, automatonProvider);
		}
		final var petriNetProvider = constructPetriNetProvider(predicateFactory, icfg);
		final AutomatonTypeConcurrent automatonTypeConcurrent = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_AUTOMATON_TYPE, AutomatonTypeConcurrent.class);
		switch (automatonTypeConcurrent) {
		case BUCHI_AUTOMATON:
			final var automatonProvider = new Petri2FiniteAutomatonAbstractionProvider.Lazy<>(petriNetProvider,
					stateFactoryForRefinement, new AutomataLibraryServices(mServices));
			return createBuchiAutomatonCegarLoop(icfg, rankVarConstructor, predicateFactory, witnessAutomaton,
					stateFactoryForRefinement, automatonProvider);
		case BUCHI_PETRI_NET:
			return new BuchiPetriNetCegarLoop<>(icfg, rankVarConstructor, predicateFactory, mPrefs, mServices,
					mTransitionClazz, constructInitialAbstraction(petriNetProvider, icfg), mCegarLoopBenchmark);
		// case RABIN_PETRI_NET:
		// return new RabinPetriNetCegarLoop<>(icfg, rankVarConstructor, predicateFactory, mPrefs, mServices,
		// mTransitionClazz, new RabinPetriNetWrapper<>(constructInitialAbstraction(petriNetProvider, icfg)),
		// mCegarLoopBenchmark);
		default:
			throw new UnsupportedOperationException(
					"The type " + automatonTypeConcurrent + " is currently not supported.");
		}
	}

	@SuppressWarnings("unchecked")
	private IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>>
			constructPetriNetProvider(final PredicateFactory predicateFactory, final IIcfg<?> icfg) {
		final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> petriNetProvider =
				new PetriInitialAbstractionProvider<>(mServices, predicateFactory, true);
		if (!mPrefs.applyOneShotLbe()) {
			return petriNetProvider;
		}
		return new PetriLbeInitialAbstractionProvider<>(petriNetProvider, mServices, mTransitionClazz,
				mPrefs.lbeIndependenceSettings(),
				(IPLBECompositionFactory<L>) new IcfgCompositionFactory(mServices, icfg.getCfgSmtToolkit()),
				Activator.PLUGIN_ID);
	}

	private BuchiAutomatonCegarLoop<L> createBuchiAutomatonCegarLoop(final IIcfg<?> icfg,
			final RankVarConstructor rankVarConstructor, final PredicateFactory predicateFactory,
			final INestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton,
			final PredicateFactoryRefinement stateFactory,
			IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> provider) {
		if (witnessAutomaton != null) {
			provider = new WitnessAutomatonAbstractionProvider<>(mServices, predicateFactory, stateFactory, provider,
					extendWitnessAutomaton(witnessAutomaton), Property.TERMINATION);
		}
		return new BuchiAutomatonCegarLoop<>(icfg, rankVarConstructor, predicateFactory, mPrefs, mServices,
				mTransitionClazz, constructInitialAbstraction(provider, icfg), stateFactory, mCegarLoopBenchmark);
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

	private INestedWordAutomaton<WitnessEdge, WitnessNode> extendWitnessAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton) {
		final AutomataLibraryServices automataServices = new AutomataLibraryServices(mServices);
		NestedWordAutomatonReachableStates<WitnessEdge, WitnessNode> reach = null;
		try {
			reach = new NestedWordAutomatonReachableStates<>(automataServices, witnessAutomaton);
		} catch (final AutomataOperationCanceledException ex) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(this.getClass(), "extending witness automaton");
			ex.addRunningTaskInfo(runningTaskInfo);
			throw new ToolchainExceptionWrapper(Activator.PLUGIN_ID, ex);
		}
		return new NestedWordAutomatonFilteredStates<>(automataServices, reach, reach.getStates(),
				reach.getInitialStates(), reach.getStates());
	}

	private <A extends IAutomaton<L, IPredicate>> A
			constructInitialAbstraction(final IInitialAbstractionProvider<L, A> provider, final IIcfg<?> icfg) {
		// OverallTime should include InitialAbstractionConstructionTime. Hence we start and stop both stopwatches.
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.OverallTime);
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.InitialAbstractionConstructionTime);
		try {
			return provider.getInitialAbstraction(icfg, getAcceptingStates(icfg));
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
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.InitialAbstractionConstructionTime);
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.OverallTime);
		}
	}
}
