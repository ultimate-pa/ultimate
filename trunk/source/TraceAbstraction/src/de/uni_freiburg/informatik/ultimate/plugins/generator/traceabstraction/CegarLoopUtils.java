package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.CegarLoopForPetriNet;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.PartialOrderCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
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
		return cegarLoop.iterate();
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

		BasicCegarLoop<L> result;
		if (languageOperation == LanguageOperation.DIFFERENCE) {
			if (taPrefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
				result = new CegarLoopSWBnonRecursive<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
						taPrefs.interpolation(), taPrefs.computeHoareAnnotation(), services, compositionFactory,
						transitionClazz);
			} else {
				switch (automataType) {
				case FINITE_AUTOMATA: {
					switch (taPrefs.getFloydHoareAutomataReuse()) {
					case EAGER:
						result = new EagerReuseCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
								taPrefs.interpolation(), computeHoareAnnotation, services, Collections.emptyList(),
								rawFloydHoareAutomataFromFile, compositionFactory, transitionClazz);
						break;
					case LAZY_IN_ORDER:
						result = new LazyReuseCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
								taPrefs.interpolation(), computeHoareAnnotation, services, Collections.emptyList(),
								rawFloydHoareAutomataFromFile, compositionFactory, transitionClazz);
						break;
					case NONE:
						result = new BasicCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
								taPrefs.interpolation(), computeHoareAnnotation, services, compositionFactory,
								transitionClazz);
						break;
					default:
						throw new AssertionError("Unknown Setting: " + taPrefs.getFloydHoareAutomataReuse());
					}
				}
					break;
				case PARTIAL_ORDER_FA:
					if (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
						throw new UnsupportedOperationException("Reuse with sleep set-based analysis");
					}
					result = new PartialOrderCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
							taPrefs.interpolation(), computeHoareAnnotation, services, compositionFactory,
							transitionClazz);
					break;
				case PETRI_NET: {
					if (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
						throw new UnsupportedOperationException("Reuse with Petri net-based analysis");
					}
					result = new CegarLoopForPetriNet<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
							services, compositionFactory, transitionClazz);
				}
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

	public static <L extends IIcfgTransition<?>> boolean hasSufficientThreadInstances(final CegarLoopResult<L> clres) {
		return clres.getResults().entrySet().stream().filter(a -> a.getValue().getResult() == Result.UNSAFE)
				.noneMatch(a -> isInsufficientThreadsLocation(a.getKey()));
	}

	public static boolean isInsufficientThreadsLocation(final IcfgLocation loc) {
		final Check check = Check.getAnnotation(loc);
		return check != null && check.getSpec().contains(Spec.SUFFICIENT_THREAD_INSTANCES);
	}
}
