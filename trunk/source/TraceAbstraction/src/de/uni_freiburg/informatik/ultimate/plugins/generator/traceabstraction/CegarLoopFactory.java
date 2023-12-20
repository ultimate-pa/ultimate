/*
 * Copyright (C) 2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainExceptionWrapper;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.NwaInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PartialOrderAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.Petri2FiniteAutomatonAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PetriInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.PetriLbeInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.CegarLoopForPetriNet;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.IndependenceProviderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.PartialOrderCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessUtils.Property;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * A utility class that allows creating CEGAR loops for different programs (based on some common settings).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of transitions in programs analyzed by the created CEGAR loops
 */
public class CegarLoopFactory<L extends IIcfgTransition<?>> {

	private static final boolean FORCE_FINITE_AUTOMATA_FOR_SEQUENTIAL_PROGRAMS = true;

	private final Class<L> mTransitionClazz;
	private final TAPreferences mPrefs;
	private final Supplier<IPLBECompositionFactory<L>> mCreateCompositionFactory;
	private final ICopyActionFactory<L> mCopyFactory;
	private final boolean mComputeHoareAnnotation;

	private CegarLoopStatisticsGenerator mCegarLoopBenchmark;

	public CegarLoopFactory(final Class<L> transitionClazz, final TAPreferences taPrefs,
			final Supplier<IPLBECompositionFactory<L>> createCompositionFactory,
			final ICopyActionFactory<L> copyFactory, final boolean computeHoareAnnotation) {
		mTransitionClazz = transitionClazz;
		mPrefs = taPrefs;
		mCreateCompositionFactory = createCompositionFactory;
		mCopyFactory = copyFactory;
		mComputeHoareAnnotation = computeHoareAnnotation;
	}

	/**
	 * Creates a new CEGAR loop.
	 *
	 * @param services
	 *            Ultimate services to use. In particular, this may be used to set a timeout.
	 * @param name
	 *            An identifier for the CEGAR loop
	 * @param root
	 *            The control flow graph of the analyzed program
	 * @param errorLocs
	 *            The error locations whose unreachability shall be proven
	 * @param witnessAutomaton
	 *            An (optional) witness automaton
	 * @param rawFloydHoareAutomataFromFile
	 *            A list of automata to use if a CEGAR loop with Floyd/Hoare automata reuse is created
	 *
	 * @return the newly created CEGAR loop
	 */
	public BasicCegarLoop<L, ?> constructCegarLoop(final IUltimateServiceProvider services, final DebugIdentifier name,
			final IIcfg<IcfgLocation> root, final Set<IcfgLocation> errorLocs,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile) {
		mCegarLoopBenchmark = new CegarLoopStatisticsGenerator();

		final LanguageOperation languageOperation = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(TraceAbstractionPreferenceInitializer.LABEL_LANGUAGE_OPERATION, LanguageOperation.class);
		final CfgSmtToolkit csToolkit = root.getCfgSmtToolkit();
		final PredicateFactory predicateFactory = constructPredicateFactory(services, csToolkit);

		final Set<IcfgLocation> hoareAnnotationLocs = mPrefs.getHoareAnnotationPositions().getLocations(root);
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(services,
				csToolkit.getManagedScript(), predicateFactory, mComputeHoareAnnotation, hoareAnnotationLocs);

		if (languageOperation != LanguageOperation.DIFFERENCE) {
			final var abstraction = createAutomataAbstraction(services, root, errorLocs, predicateFactory,
					stateFactoryForRefinement, witnessAutomaton);
			// TODO extract proof producer from IInitialAbstractionProvider and pass to CEGAR loop
			return new IncrementalInclusionCegarLoop<>(name, abstraction, root, csToolkit, predicateFactory, mPrefs,
					errorLocs, mPrefs.interpolation(), null, mComputeHoareAnnotation, services, languageOperation,
					mTransitionClazz, stateFactoryForRefinement);
		}

		if (mPrefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
			final var abstraction = createAutomataAbstraction(services, root, errorLocs, predicateFactory,
					stateFactoryForRefinement, witnessAutomaton);
			// TODO extract proof producer from IInitialAbstractionProvider and pass to CEGAR loop
			return new CegarLoopSWBnonRecursive<>(name, abstraction, root, csToolkit, predicateFactory, mPrefs,
					errorLocs, mPrefs.interpolation(), null, mComputeHoareAnnotation, services, mTransitionClazz,
					stateFactoryForRefinement);
		}

		if ((FORCE_FINITE_AUTOMATA_FOR_SEQUENTIAL_PROGRAMS && !IcfgUtils.isConcurrent(root))
				|| witnessAutomaton != null) {
			return createFiniteAutomataCegarLoop(services, name, root, predicateFactory, errorLocs,
					rawFloydHoareAutomataFromFile, hoareAnnotationLocs, stateFactoryForRefinement, witnessAutomaton);
		}

		switch (mPrefs.getAutomataTypeConcurrency()) {
		case FINITE_AUTOMATA:
			return createFiniteAutomataCegarLoop(services, name, root, predicateFactory, errorLocs,
					rawFloydHoareAutomataFromFile, hoareAnnotationLocs, stateFactoryForRefinement, witnessAutomaton);
		case PARTIAL_ORDER_FA:
			requireNoReuse("POR-based analysis");
			requireNoWitnesses(witnessAutomaton, "POR-based analysis");
			final var factory = new IndependenceProviderFactory<>(services, mPrefs, mCopyFactory);
			return new PartialOrderCegarLoop<>(name,
					createPartialOrderAbstraction(services, predicateFactory, stateFactoryForRefinement, root,
							errorLocs),
					root, csToolkit, predicateFactory, mPrefs, errorLocs, mPrefs.interpolation(), services,
					factory.createProviders(root, predicateFactory), mTransitionClazz, stateFactoryForRefinement);
		case PETRI_NET:
			requireNoReuse("Petri net-based analysis");
			requireNoWitnesses(witnessAutomaton, "Petri net-based analysis");
			return new CegarLoopForPetriNet<>(name,
					createPetriAbstraction(services, predicateFactory, true, root, errorLocs), root, csToolkit,
					predicateFactory, mPrefs, errorLocs, services, mTransitionClazz, stateFactoryForRefinement);
		default:
			throw new AssertionError("Unknown Setting: " + mPrefs.getAutomataTypeConcurrency());
		}
	}

	private void requireNoReuse(final String analysis) {
		if (mPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
			throw new UnsupportedOperationException("Floyd/Hoare automaton reuse not supported for " + analysis);
		}
	}

	private static void requireNoWitnesses(
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final String analysis) {
		if (witnessAutomaton != null) {
			throw new UnsupportedOperationException("Witness automata not supported for " + analysis);
		}
	}

	private static PredicateFactory constructPredicateFactory(final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit) {
		return new PredicateFactory(services, csToolkit.getManagedScript(), csToolkit.getSymbolTable());
	}

	private BasicCegarLoop<L, ?> createFiniteAutomataCegarLoop(final IUltimateServiceProvider services,
			final DebugIdentifier name, final IIcfg<IcfgLocation> root, final PredicateFactory predicateFactory,
			final Set<IcfgLocation> errorLocs,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final Set<IcfgLocation> hoareAnnotationLocs, final PredicateFactoryRefinement stateFactoryForRefinement,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton) {

		// TODO extract proof producer from IInitialAbstractionProvider and pass to CEGAR loops
		final INestedWordAutomaton<L, IPredicate> initialAbstraction = createAutomataAbstraction(services, root,
				errorLocs, predicateFactory, stateFactoryForRefinement, witnessAutomaton);
		final CfgSmtToolkit csToolkit = root.getCfgSmtToolkit();

		switch (mPrefs.getFloydHoareAutomataReuse()) {
		case EAGER:
			return new EagerReuseCegarLoop<>(name, initialAbstraction, root, csToolkit, predicateFactory, mPrefs,
					errorLocs, mPrefs.interpolation(), null, mComputeHoareAnnotation, services, Collections.emptyList(),
					rawFloydHoareAutomataFromFile, mTransitionClazz, stateFactoryForRefinement);
		case LAZY_IN_ORDER:
			return new LazyReuseCegarLoop<>(name, initialAbstraction, root, csToolkit, predicateFactory, mPrefs,
					errorLocs, mPrefs.interpolation(), null, mComputeHoareAnnotation, services, Collections.emptyList(),
					rawFloydHoareAutomataFromFile, mTransitionClazz, stateFactoryForRefinement);
		case NONE:
			return new NwaCegarLoop<>(name, initialAbstraction, root, csToolkit, predicateFactory, mPrefs, errorLocs,
					mPrefs.interpolation(), null, mComputeHoareAnnotation, services, mTransitionClazz,
					stateFactoryForRefinement);
		default:
			throw new AssertionError("Unknown Setting: " + mPrefs.getFloydHoareAutomataReuse());
		}
	}

	private INestedWordAutomaton<L, IPredicate> createAutomataAbstraction(final IUltimateServiceProvider services,
			final IIcfg<IcfgLocation> icfg, final Set<IcfgLocation> errorLocs, final PredicateFactory predicateFactory,
			final PredicateFactoryRefinement stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton) {
		return constructInitialAbstraction(createAutomataAbstractionProvider(services, IcfgUtils.isConcurrent(icfg),
				predicateFactory, stateFactory, witnessAutomaton), icfg, errorLocs);
	}

	private IInitialAbstractionProvider<L, ? extends INestedWordAutomaton<L, IPredicate>>
			createAutomataAbstractionProvider(final IUltimateServiceProvider services, final boolean isConcurrent,
					final PredicateFactory predicateFactory, final PredicateFactoryRefinement stateFactory,
					final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton) {
		if (!isConcurrent) {
			final IInitialAbstractionProvider<L, INestedWordAutomaton<L, IPredicate>> provider =
					new NwaInitialAbstractionProvider<>(services, stateFactory, mPrefs.interprocedural(),
							predicateFactory, mPrefs.getHoareSettings());
			if (witnessAutomaton == null) {
				return provider;
			}
			return new WitnessAutomatonAbstractionProvider<>(services, predicateFactory, stateFactory, provider,
					witnessAutomaton, Property.NON_REACHABILITY);
		}

		final var netProvider = createPetriAbstractionProvider(services, predicateFactory, false);
		if (!mPrefs.applyOneShotPOR()) {
			return new Petri2FiniteAutomatonAbstractionProvider.Eager<>(netProvider, stateFactory,
					new AutomataLibraryServices(services));
		}
		return new PartialOrderAbstractionProvider<>(
				// Partial Order reductions aim to avoid the explicit construction of the full finite automaton.
				// Hence we use the lazy abstraction provider.
				new Petri2FiniteAutomatonAbstractionProvider.Lazy<>(netProvider, stateFactory,
						new AutomataLibraryServices(services)),
				services, stateFactory, predicateFactory, mPrefs.getPartialOrderMode(), mPrefs.getDfsOrderType(),
				mPrefs.getDfsOrderSeed());
	}

	@Deprecated
	public static <L extends IIcfgTransition<?>> BoundedPetriNet<L, IPredicate> createPetriAbstraction(
			final IUltimateServiceProvider services, final IPLBECompositionFactory<L> compositionFactory,
			final PredicateFactory predicateFactory, final Class<L> transitionClazz, final TAPreferences pref,
			final boolean removeDead, final IIcfg<IcfgLocation> icfg, final Set<IcfgLocation> errorLocs) {
		return new CegarLoopFactory<>(transitionClazz, pref, () -> compositionFactory, null, false)
				.createPetriAbstraction(services, predicateFactory, removeDead, icfg, errorLocs);
	}

	private BoundedPetriNet<L, IPredicate> createPetriAbstraction(final IUltimateServiceProvider services,
			final PredicateFactory predicateFactory, final boolean removeDead, final IIcfg<IcfgLocation> icfg,
			final Set<IcfgLocation> errorLocs) {
		return constructInitialAbstraction(createPetriAbstractionProvider(services, predicateFactory, removeDead), icfg,
				errorLocs);
	}

	private IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> createPetriAbstractionProvider(
			final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final boolean removeDead) {
		final var netProvider = new PetriInitialAbstractionProvider<L>(services, predicateFactory, removeDead);
		if (!mPrefs.applyOneShotLbe()) {
			return netProvider;
		}
		return new PetriLbeInitialAbstractionProvider<>(netProvider, services, mTransitionClazz,
				mPrefs.lbeIndependenceSettings(), mCreateCompositionFactory.get());
	}

	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> createPartialOrderAbstraction(
			final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IPetriNet2FiniteAutomatonStateFactory<IPredicate> stateFactory, final IIcfg<IcfgLocation> icfg,
			final Set<IcfgLocation> errorLocs) {
		return constructInitialAbstraction(
				createPartialOrderAbstractionProvider(services, predicateFactory, stateFactory), icfg, errorLocs);
	}

	private IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>>
			createPartialOrderAbstractionProvider(final IUltimateServiceProvider services,
					final PredicateFactory predicateFactory,
					final IPetriNet2FiniteAutomatonStateFactory<IPredicate> stateFactory) {
		final var netProvider = createPetriAbstractionProvider(services, predicateFactory, false);
		return new Petri2FiniteAutomatonAbstractionProvider.Lazy<>(netProvider, stateFactory,
				new AutomataLibraryServices(services));
	}

	private <A extends IAutomaton<L, IPredicate>> A constructInitialAbstraction(
			final IInitialAbstractionProvider<L, A> provider, final IIcfg<IcfgLocation> icfg,
			final Set<IcfgLocation> errorLocs) {
		// OverallTime should include InitialAbstractionConstructionTime. Hence we start and stop both stopwatches.
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.OverallTime);
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.InitialAbstractionConstructionTime);
		try {
			return provider.getInitialAbstraction(icfg, errorLocs);
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

	public CegarLoopStatisticsGenerator getStatistics() {
		return mCegarLoopBenchmark;
	}
}
