package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency.IRefinableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency.SpecificVariableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency.VariableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.CegarLoopForPetriNet;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.PartialOrderCegarLoop;
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
			final IPLBECompositionFactory<L> compositionFactory,
			final Supplier<ICopyActionFactory<L>> copyFactorySupplier, final Class<L> transitionClazz) {
		final BasicCegarLoop<L> cegarLoop = constructCegarLoop(services, name, root, taPrefs, root.getCfgSmtToolkit(),
				predicateFactory, errorLocs, rawFloydHoareAutomataFromFile, computeHoareAnnotation, automataType,
				compositionFactory, copyFactorySupplier, transitionClazz, witnessAutomaton);
		return cegarLoop.runCegar();
	}

	public static <L extends IIcfgTransition<?>> BasicCegarLoop<L> constructCegarLoop(
			final IUltimateServiceProvider services, final DebugIdentifier name, final IIcfg<IcfgLocation> root,
			final TAPreferences taPrefs, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final Set<IcfgLocation> errorLocs,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final boolean computeHoareAnnotation, final Concurrency automataType,
			final IPLBECompositionFactory<L> compositionFactory,
			final Supplier<ICopyActionFactory<L>> copyFactorySupplier, final Class<L> transitionClazz,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton) {
		final LanguageOperation languageOperation = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(TraceAbstractionPreferenceInitializer.LABEL_LANGUAGE_OPERATION, LanguageOperation.class);

		BasicCegarLoop<L> result;
		if (languageOperation == LanguageOperation.DIFFERENCE) {
			if (taPrefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
				result = new CegarLoopSWBnonRecursive<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
						taPrefs.interpolation(), taPrefs.computeHoareAnnotation(), services, compositionFactory,
						transitionClazz);
			} else if (FORCE_FINITE_AUTOMATA_FOR_SEQUENTIAL_PROGRAMS && !IcfgUtils.isConcurrent(root)) {
				result = createFiniteAutomataCegarLoop(services, name, root, taPrefs, csToolkit, predicateFactory,
						errorLocs, rawFloydHoareAutomataFromFile, computeHoareAnnotation, compositionFactory,
						transitionClazz);
			} else {
				switch (automataType) {
				case FINITE_AUTOMATA:
					result = createFiniteAutomataCegarLoop(services, name, root, taPrefs, csToolkit, predicateFactory,
							errorLocs, rawFloydHoareAutomataFromFile, computeHoareAnnotation, compositionFactory,
							transitionClazz);
					break;
				case PARTIAL_ORDER_FA:
					if (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
						throw new UnsupportedOperationException("Reuse with POR-based analysis");
					}
					result = new PartialOrderCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
							taPrefs.interpolation(), computeHoareAnnotation, services, compositionFactory,
							constructPartialOrderAbstraction(taPrefs, root, copyFactorySupplier), transitionClazz);
					break;
				case PETRI_NET:
					if (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
						throw new UnsupportedOperationException("Reuse with Petri net-based analysis");
					}
					result = new CegarLoopForPetriNet<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
							services, compositionFactory, transitionClazz);

					break;
				default:
					throw new AssertionError("Unknown Setting: " + automataType);
				}
			}
		} else {
			result = new IncrementalInclusionCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
					taPrefs.interpolation(), computeHoareAnnotation, services, languageOperation, compositionFactory,
					transitionClazz);
		}
		result.setWitnessAutomaton(witnessAutomaton);
		return result;
	}

	private static <L extends IIcfgTransition<?>> BasicCegarLoop<L> createFiniteAutomataCegarLoop(
			final IUltimateServiceProvider services, final DebugIdentifier name, final IIcfg<IcfgLocation> root,
			final TAPreferences taPrefs, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final Set<IcfgLocation> errorLocs,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final boolean computeHoareAnnotation, final IPLBECompositionFactory<L> compositionFactory,
			final Class<L> transitionClazz) {
		switch (taPrefs.getFloydHoareAutomataReuse()) {
		case EAGER:
			return new EagerReuseCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
					taPrefs.interpolation(), computeHoareAnnotation, services, Collections.emptyList(),
					rawFloydHoareAutomataFromFile, compositionFactory, transitionClazz);
		case LAZY_IN_ORDER:
			return new LazyReuseCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
					taPrefs.interpolation(), computeHoareAnnotation, services, Collections.emptyList(),
					rawFloydHoareAutomataFromFile, compositionFactory, transitionClazz);
		case NONE:
			return new BasicCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
					taPrefs.interpolation(), computeHoareAnnotation, services, compositionFactory, transitionClazz);
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

	private static <L extends IAction> IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, ?, L>
			constructPartialOrderAbstraction(final TAPreferences prefs, final IIcfg<?> icfg,
					final Supplier<ICopyActionFactory<L>> copyFactorySupplier) {
		switch (prefs.getPorAbstraction()) {
		case VARIABLES_GLOBAL:
			return new VariableAbstraction<>(copyFactorySupplier.get(), icfg.getCfgSmtToolkit());
		case VARIABLES_LOCAL:
			final Set<L> allLetters = new IcfgEdgeIterator(icfg).asStream().map(x -> (L) x).collect(Collectors.toSet());
			return new SpecificVariableAbstraction<>(copyFactorySupplier.get(), icfg.getCfgSmtToolkit(), allLetters);
		case NONE:
			return null;
		default:
			throw new UnsupportedOperationException("Unknown abstraction type: " + prefs.getPorAbstraction());
		}
	}
}
