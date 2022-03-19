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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding.PetriNetLbe;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.CegarLoopForPetriNet;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.PartialOrderCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.NwaInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.PartialOrderAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.Petri2FiniteAutomatonAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.PetriInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.initialabstraction.PetriLbeInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;
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
	private final boolean mComputeHoareAnnotation;

	public CegarLoopFactory(final Class<L> transitionClazz, final TAPreferences taPrefs,
			final Supplier<IPLBECompositionFactory<L>> createCompositionFactory, final boolean computeHoareAnnotation) {
		mTransitionClazz = transitionClazz;
		mPrefs = taPrefs;
		mCreateCompositionFactory = createCompositionFactory;
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
	public BasicCegarLoop<L> constructCegarLoop(final IUltimateServiceProvider services, final DebugIdentifier name,
			final IIcfg<IcfgLocation> root, final Set<IcfgLocation> errorLocs,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile) {
		final LanguageOperation languageOperation = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(TraceAbstractionPreferenceInitializer.LABEL_LANGUAGE_OPERATION, LanguageOperation.class);
		final CfgSmtToolkit csToolkit = root.getCfgSmtToolkit();
		final PredicateFactory predicateFactory = getPredicateFactory(services, csToolkit);

		final Set<IcfgLocation> hoareAnnotationLocs;
		if (mComputeHoareAnnotation) {
			hoareAnnotationLocs = TraceAbstractionUtils.getLocationsForWhichHoareAnnotationIsComputed(root,
					mPrefs.getHoareAnnotationPositions());
		} else {
			hoareAnnotationLocs = Collections.emptySet();
		}
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(services,
				csToolkit.getManagedScript(), predicateFactory, mComputeHoareAnnotation, hoareAnnotationLocs);

		BasicCegarLoop<L> result;
		if (languageOperation == LanguageOperation.DIFFERENCE) {
			if (mPrefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
				result = new CegarLoopSWBnonRecursive<>(name, root, csToolkit, predicateFactory, mPrefs, errorLocs,
						mPrefs.interpolation(), mComputeHoareAnnotation, hoareAnnotationLocs, services,
						mTransitionClazz, stateFactoryForRefinement,
						createAutomataAbstractionProvider(services, root, predicateFactory, stateFactoryForRefinement));
			} else if (FORCE_FINITE_AUTOMATA_FOR_SEQUENTIAL_PROGRAMS && !IcfgUtils.isConcurrent(root)) {
				result = createFiniteAutomataCegarLoop(services, name, root, predicateFactory, errorLocs,
						rawFloydHoareAutomataFromFile, hoareAnnotationLocs, stateFactoryForRefinement);
			} else {
				switch (mPrefs.getAutomataTypeConcurrency()) {
				case FINITE_AUTOMATA:
					result = createFiniteAutomataCegarLoop(services, name, root, predicateFactory, errorLocs,
							rawFloydHoareAutomataFromFile, hoareAnnotationLocs, stateFactoryForRefinement);
					break;
				case PARTIAL_ORDER_FA:
					if (mPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
						throw new UnsupportedOperationException("Reuse with POR-based analysis");
					}
					result = new PartialOrderCegarLoop<>(name, root, csToolkit, predicateFactory, mPrefs, errorLocs,
							mPrefs.interpolation(), services, mTransitionClazz, stateFactoryForRefinement,
							createPartialOrderAbstractionProvider(services, predicateFactory,
									stateFactoryForRefinement));
					break;
				case PETRI_NET:
					if (mPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
						throw new UnsupportedOperationException("Reuse with Petri net-based analysis");
					}
					result = new CegarLoopForPetriNet<>(name, root, csToolkit, predicateFactory, mPrefs, errorLocs,
							services, mTransitionClazz, stateFactoryForRefinement,
							createPetriAbstractionProvider(services, predicateFactory, true));

					break;
				default:
					throw new AssertionError("Unknown Setting: " + mPrefs.getAutomataTypeConcurrency());
				}
			}
		} else {
			result = new IncrementalInclusionCegarLoop<>(name, root, csToolkit, predicateFactory, mPrefs, errorLocs,
					mPrefs.interpolation(), mComputeHoareAnnotation, hoareAnnotationLocs, services, languageOperation,
					mTransitionClazz, stateFactoryForRefinement,
					createAutomataAbstractionProvider(services, root, predicateFactory, stateFactoryForRefinement));
		}
		result.setWitnessAutomaton(witnessAutomaton);
		return result;
	}

	private static PredicateFactory getPredicateFactory(final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit) {
		return new PredicateFactory(services, csToolkit.getManagedScript(), csToolkit.getSymbolTable());
	}

	private BasicCegarLoop<L> createFiniteAutomataCegarLoop(final IUltimateServiceProvider services,
			final DebugIdentifier name, final IIcfg<IcfgLocation> root, final PredicateFactory predicateFactory,
			final Set<IcfgLocation> errorLocs,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final Set<IcfgLocation> hoareAnnotationLocs, final PredicateFactoryRefinement stateFactoryForRefinement) {

		final var abstractionProvider =
				createAutomataAbstractionProvider(services, root, predicateFactory, stateFactoryForRefinement);
		final CfgSmtToolkit csToolkit = root.getCfgSmtToolkit();

		switch (mPrefs.getFloydHoareAutomataReuse()) {
		case EAGER:
			return new EagerReuseCegarLoop<>(name, root, csToolkit, predicateFactory, mPrefs, errorLocs,
					mPrefs.interpolation(), mComputeHoareAnnotation, hoareAnnotationLocs, services,
					Collections.emptyList(), rawFloydHoareAutomataFromFile, mTransitionClazz, stateFactoryForRefinement,
					abstractionProvider);
		case LAZY_IN_ORDER:
			return new LazyReuseCegarLoop<>(name, root, csToolkit, predicateFactory, mPrefs, errorLocs,
					mPrefs.interpolation(), mComputeHoareAnnotation, hoareAnnotationLocs, services,
					Collections.emptyList(), rawFloydHoareAutomataFromFile, mTransitionClazz, stateFactoryForRefinement,
					abstractionProvider);
		case NONE:
			return new BasicCegarLoop<>(name, root, csToolkit, predicateFactory, mPrefs, errorLocs,
					mPrefs.interpolation(), mComputeHoareAnnotation, hoareAnnotationLocs, services, mTransitionClazz,
					stateFactoryForRefinement, abstractionProvider);
		default:
			throw new AssertionError("Unknown Setting: " + mPrefs.getFloydHoareAutomataReuse());
		}
	}

	private <F extends IEmptyStackStateFactory<IPredicate> & IPetriNet2FiniteAutomatonStateFactory<IPredicate>>
			IInitialAbstractionProvider<L, ?> createAutomataAbstractionProvider(final IUltimateServiceProvider services,
					final IIcfg<?> icfg, final PredicateFactory predicateFactory, final F stateFactory) {
		if (!IcfgUtils.isConcurrent(icfg)) {
			return new NwaInitialAbstractionProvider<>(services, stateFactory, mPrefs.interprocedural(),
					predicateFactory);
		}

		final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> netProvider =
				createPetriAbstractionProvider(services, predicateFactory, false);
		if (!mPrefs.applyOneShotPOR()) {
			return new Petri2FiniteAutomatonAbstractionProvider.Eager<>(netProvider, stateFactory,
					new AutomataLibraryServices(services));
		}

		return new PartialOrderAbstractionProvider<>(
				// Partial Order reductions aim to avoid the explicit construction of the full finite automaton.
				new Petri2FiniteAutomatonAbstractionProvider.Lazy<>(netProvider, stateFactory,
						new AutomataLibraryServices(services)),
				services, stateFactory, predicateFactory, mPrefs.getPartialOrderMode(), mPrefs.getDfsOrderType(),
				mPrefs.getDfsOrderSeed(), Activator.PLUGIN_ID);
	}

	@Deprecated
	public static <L extends IIcfgTransition<?>> IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>>
			createPetriAbstractionProvider(final IUltimateServiceProvider services,
					final IPLBECompositionFactory<L> compositionFactory, final PredicateFactory predicateFactory,
					final Class<L> transitionClazz, final TAPreferences pref, final boolean removeDead) {
		return new CegarLoopFactory<>(transitionClazz, pref, () -> compositionFactory, false)
				.createPetriAbstractionProvider(services, predicateFactory, removeDead);
	}

	private IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> createPetriAbstractionProvider(
			final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final boolean removeDead) {
		final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> netProvider =
				new PetriInitialAbstractionProvider<>(services, predicateFactory, removeDead);
		if (mPrefs.useLbeInConcurrentAnalysis() == PetriNetLbe.OFF) {
			return netProvider;
		}
		return new PetriLbeInitialAbstractionProvider<>(netProvider, services, mTransitionClazz,
				mPrefs.useLbeInConcurrentAnalysis(), mCreateCompositionFactory.get());
	}

	private IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>>
			createPartialOrderAbstractionProvider(final IUltimateServiceProvider services,
					final PredicateFactory predicateFactory,
					final IPetriNet2FiniteAutomatonStateFactory<IPredicate> stateFactory) {
		final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> netProvider =
				createPetriAbstractionProvider(services, predicateFactory, false);
		return new Petri2FiniteAutomatonAbstractionProvider.Lazy<>(netProvider, stateFactory,
				new AutomataLibraryServices(services));
	}
}
