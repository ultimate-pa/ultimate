package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.petrinetlbe.PetriNetLargeBlockEncoding.PetriNetLbe;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.CegarLoopForPetriNet;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.PartialOrderCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.NwaInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.PartialOrderAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.Petri2FiniteAutomatonAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.PetriInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.PetriLbeInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class CegarLoopUtils {

	private static final boolean FORCE_FINITE_AUTOMATA_FOR_SEQUENTIAL_PROGRAMS = true;

	private CegarLoopUtils() {
		// do not instantiate utility class
	}

	public static <L extends IIcfgTransition<?>> CegarLoopResult<L> getCegarLoopResult(
			final IUltimateServiceProvider services, final DebugIdentifier name, final IIcfg<IcfgLocation> root,
			final TAPreferences taPrefs, final PredicateFactory predicateFactory, final Set<IcfgLocation> errorLocs,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final boolean computeHoareAnnotation, final Concurrency automataType,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> transitionClazz) {
		final BasicCegarLoop<L> cegarLoop = constructCegarLoop(services, name, root, taPrefs, root.getCfgSmtToolkit(),
				predicateFactory, errorLocs, rawFloydHoareAutomataFromFile, computeHoareAnnotation, automataType,
				compositionFactory, transitionClazz, witnessAutomaton);
		return cegarLoop.runCegar();
	}

	public static <L extends IIcfgTransition<?>> BasicCegarLoop<L> constructCegarLoop(
			final IUltimateServiceProvider services, final DebugIdentifier name, final IIcfg<IcfgLocation> root,
			final TAPreferences taPrefs, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final Set<IcfgLocation> errorLocs,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final boolean computeHoareAnnotation, final Concurrency automataType,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> transitionClazz,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton) {
		final LanguageOperation languageOperation = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(TraceAbstractionPreferenceInitializer.LABEL_LANGUAGE_OPERATION, LanguageOperation.class);

		final Set<IcfgLocation> hoareAnnotationLocs;
		if (computeHoareAnnotation) {
			hoareAnnotationLocs = TraceAbstractionUtils.getLocationsForWhichHoareAnnotationIsComputed(root,
					taPrefs.getHoareAnnotationPositions());
		} else {
			hoareAnnotationLocs = Collections.emptySet();
		}
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(services,
				csToolkit.getManagedScript(), predicateFactory, computeHoareAnnotation, hoareAnnotationLocs);

		BasicCegarLoop<L> result;
		if (languageOperation == LanguageOperation.DIFFERENCE) {
			if (taPrefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
				result = new CegarLoopSWBnonRecursive<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
						taPrefs.interpolation(), computeHoareAnnotation, hoareAnnotationLocs, services, transitionClazz,
						stateFactoryForRefinement, createAutomataAbstractionProvider(services, compositionFactory, root,
								predicateFactory, stateFactoryForRefinement, transitionClazz, taPrefs));
			} else if (FORCE_FINITE_AUTOMATA_FOR_SEQUENTIAL_PROGRAMS && !IcfgUtils.isConcurrent(root)) {
				result = createFiniteAutomataCegarLoop(services, name, root, taPrefs, csToolkit, predicateFactory,
						errorLocs, rawFloydHoareAutomataFromFile, computeHoareAnnotation, hoareAnnotationLocs,
						compositionFactory, transitionClazz, stateFactoryForRefinement);
			} else {
				switch (automataType) {
				case FINITE_AUTOMATA:
					result = createFiniteAutomataCegarLoop(services, name, root, taPrefs, csToolkit, predicateFactory,
							errorLocs, rawFloydHoareAutomataFromFile, computeHoareAnnotation, hoareAnnotationLocs,
							compositionFactory, transitionClazz, stateFactoryForRefinement);
					break;
				case PARTIAL_ORDER_FA:
					if (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
						throw new UnsupportedOperationException("Reuse with POR-based analysis");
					}
					result = new PartialOrderCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
							taPrefs.interpolation(), services, transitionClazz, stateFactoryForRefinement,
							createPartialOrderAbstractionProvider(services, compositionFactory, predicateFactory,
									stateFactoryForRefinement, transitionClazz, taPrefs));
					break;
				case PETRI_NET:
					if (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
						throw new UnsupportedOperationException("Reuse with Petri net-based analysis");
					}
					result = new CegarLoopForPetriNet<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
							services, transitionClazz, stateFactoryForRefinement,
							CegarLoopUtils.<L> createPetriAbstractionProvider(services, compositionFactory,
									predicateFactory, transitionClazz, taPrefs, true));

					break;
				default:
					throw new AssertionError("Unknown Setting: " + automataType);
				}
			}
		} else {
			result = new IncrementalInclusionCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
					taPrefs.interpolation(), computeHoareAnnotation, hoareAnnotationLocs, services, languageOperation,
					transitionClazz, stateFactoryForRefinement,
					createAutomataAbstractionProvider(services, compositionFactory, root, predicateFactory,
							stateFactoryForRefinement, transitionClazz, taPrefs));
		}
		result.setWitnessAutomaton(witnessAutomaton);
		return result;
	}

	private static <L extends IIcfgTransition<?>> BasicCegarLoop<L> createFiniteAutomataCegarLoop(
			final IUltimateServiceProvider services, final DebugIdentifier name, final IIcfg<IcfgLocation> root,
			final TAPreferences taPrefs, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final Set<IcfgLocation> errorLocs,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final boolean computeHoareAnnotation, final Set<IcfgLocation> hoareAnnotationLocs,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {

		final var abstractionProvider = createAutomataAbstractionProvider(services, compositionFactory, root,
				predicateFactory, stateFactoryForRefinement, transitionClazz, taPrefs);

		switch (taPrefs.getFloydHoareAutomataReuse()) {
		case EAGER:
			return new EagerReuseCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
					taPrefs.interpolation(), computeHoareAnnotation, hoareAnnotationLocs, services,
					Collections.emptyList(), rawFloydHoareAutomataFromFile, transitionClazz, stateFactoryForRefinement,
					abstractionProvider);
		case LAZY_IN_ORDER:
			return new LazyReuseCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
					taPrefs.interpolation(), computeHoareAnnotation, hoareAnnotationLocs, services,
					Collections.emptyList(), rawFloydHoareAutomataFromFile, transitionClazz, stateFactoryForRefinement,
					abstractionProvider);
		case NONE:
			return new BasicCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
					taPrefs.interpolation(), computeHoareAnnotation, hoareAnnotationLocs, services, transitionClazz,
					stateFactoryForRefinement, abstractionProvider);
		default:
			throw new AssertionError("Unknown Setting: " + taPrefs.getFloydHoareAutomataReuse());
		}
	}

	public static <L extends IIcfgTransition<?>> boolean hasSufficientThreadInstances(final CegarLoopResult<L> clres) {
		return clres.getResults().entrySet().stream().filter(a -> a.getValue().getResult() == Result.UNSAFE)
				.noneMatch(a -> isInsufficientThreadsLocation(a.getKey()));
	}

	public static boolean isInsufficientThreadsLocation(final IcfgLocation loc) {
		final Check check = Check.getAnnotation(loc);
		return check != null && check.getSpec().contains(Spec.SUFFICIENT_THREAD_INSTANCES);
	}

	private static <L extends IIcfgTransition<?>, F extends IEmptyStackStateFactory<IPredicate> & IPetriNet2FiniteAutomatonStateFactory<IPredicate>>
			IInitialAbstractionProvider<L, ?> createAutomataAbstractionProvider(final IUltimateServiceProvider services,
					final IPLBECompositionFactory<L> compositionFactory, final IIcfg<?> icfg,
					final PredicateFactory predicateFactory, final F stateFactory, final Class<L> transitionClazz,
					final TAPreferences pref) {
		if (!IcfgUtils.isConcurrent(icfg)) {
			return new NwaInitialAbstractionProvider<>(services, stateFactory, pref.interprocedural(),
					predicateFactory);
		}

		final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> netProvider =
				createPetriAbstractionProvider(services, compositionFactory, predicateFactory, transitionClazz, pref,
						false);
		if (!pref.applyOneShotPOR()) {
			return new Petri2FiniteAutomatonAbstractionProvider.Eager<>(netProvider, stateFactory,
					new AutomataLibraryServices(services));
		}

		return new PartialOrderAbstractionProvider<>(
				// Partial Order reductions aim to avoid the explicit construction of the full finite automaton.
				new Petri2FiniteAutomatonAbstractionProvider.Lazy<>(netProvider, stateFactory,
						new AutomataLibraryServices(services)),
				services, stateFactory, predicateFactory, pref.getPartialOrderMode(), pref.getDfsOrderType(),
				pref.getDfsOrderSeed());
	}

	public static <L extends IIcfgTransition<?>> IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>>
			createPetriAbstractionProvider(final IUltimateServiceProvider services,
					final IPLBECompositionFactory<L> compositionFactory, final PredicateFactory predicateFactory,
					final Class<L> transitionClazz, final TAPreferences pref, final boolean removeDead) {
		final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> netProvider =
				new PetriInitialAbstractionProvider<>(services, predicateFactory, removeDead);
		if (pref.useLbeInConcurrentAnalysis() == PetriNetLbe.OFF) {
			return netProvider;
		}
		return new PetriLbeInitialAbstractionProvider<>(netProvider, services, transitionClazz,
				pref.useLbeInConcurrentAnalysis(), compositionFactory);
	}

	private static <L extends IIcfgTransition<?>>
			IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>>
			createPartialOrderAbstractionProvider(final IUltimateServiceProvider services,
					final IPLBECompositionFactory<L> compositionFactory, final PredicateFactory predicateFactory,
					final IPetriNet2FiniteAutomatonStateFactory<IPredicate> stateFactory,
					final Class<L> transitionClazz, final TAPreferences pref) {
		final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> netProvider =
				createPetriAbstractionProvider(services, compositionFactory, predicateFactory, transitionClazz, pref,
						false);
		return new Petri2FiniteAutomatonAbstractionProvider.Lazy<>(netProvider, stateFactory,
				new AutomataLibraryServices(services));
	}
}
