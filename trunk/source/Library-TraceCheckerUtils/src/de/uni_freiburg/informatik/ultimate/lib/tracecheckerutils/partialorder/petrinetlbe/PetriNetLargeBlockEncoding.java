/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe;

import java.util.Arrays;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ICompositionFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.LiptonReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.ConditionTransformingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.DefaultIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.DisjunctiveConditionalIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.UnionIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.DebugPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.Conditionality;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticConditionEliminator;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SyntacticIndependenceRelation;

/**
 * Performs a Large Block Encoding on Petri nets. This operation performs Lipton reduction ({@link LiptonReduction}) and
 * instantiates the parameters in a way suitable (and sound) for Trace abstraction.
 *
 * Furthermore, it implements backtranslation of {@link IProgramExecution}s containing fused transitions as created by
 * Lipton reductions.
 *
 * @author Elisabeth Schanno
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the given Petri net
 */
public class PetriNetLargeBlockEncoding<L extends IIcfgTransition<?>> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private IIndependenceCache<?, L> mIndependenceCache;

	private final BoundedPetriNet<L, IPredicate> mResult;

	private final PetriNetLargeBlockEncodingStatisticsGenerator mStatistics;

	/**
	 * Performs Large Block Encoding on the given Petri net.
	 *
	 * @param services
	 *            A {@link IUltimateServiceProvider} instance.
	 * @param cfgSmtToolkit
	 *            A {@link CfgSmtToolkit} instance that has to contain all procedures and variables that may occur in
	 *            this {@link IIcfg}.
	 * @param petriNet
	 *            The Petri net on which the large block encoding should be performed.
	 * @param petriNetLbeSettings
	 *            Determines the independence relation to be used.
	 * @param compositionFactory
	 *            A composition factory for the letters of the Petri net.
	 * @param predicateFactory
	 *            A predicate factory for predicates of the control flow graph.
	 * @param clazz
	 *
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled.
	 * @throws PetriNetNot1SafeException
	 *             if Petri net is not 1-safe.
	 */
	public PetriNetLargeBlockEncoding(final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final BoundedPetriNet<L, IPredicate> petriNet, final IndependenceSettings independenceSettings,
			ICompositionFactory<L> compositionFactory, final BasicPredicateFactory predicateFactory,
			final IIndependenceCache<?, L> independenceCache, final Class<L> clazz)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		mLogger = services.getLoggingService().getLogger(getClass());
		mServices = services;
		mManagedScript = cfgSmtToolkit.getManagedScript();
		mIndependenceCache = independenceCache;

		final IIndependenceRelation<Set<IPredicate>, L> moverCheck =
				createIndependenceRelation(independenceSettings, predicateFactory);
		if (mIndependenceCache != null) {
			compositionFactory = new CompositionFactoryWithCacheUpdate<>(compositionFactory, mIndependenceCache);
		}

		mLogger.info("Starting large block encoding on Petri net that " + petriNet.sizeInformation());

		final AutomataLibraryServices automataServices = new AutomataLibraryServices(services);
		final CopyPredicatePlaceFactory placeFactory = new CopyPredicatePlaceFactory(predicateFactory);
		final InfeasPostScriptChecker<L, IPredicate> postScriptChecker =
				new InfeasPostScriptChecker<>(mServices, mManagedScript);
		try {
			final LiptonReduction<L, IPredicate> lipton = new LiptonReduction<>(automataServices, petriNet,
					compositionFactory, placeFactory, moverCheck, postScriptChecker);
			mResult = lipton.getResult();
			mStatistics = new PetriNetLargeBlockEncodingStatisticsGenerator(lipton.getStatistics(),
					moverCheck.getStatistics());
		} catch (final AutomataOperationCanceledException | ToolchainCanceledException ce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(petriNet));
			ce.addRunningTaskInfo(runningTaskInfo);
			throw ce;
		}
	}

	private IIndependenceRelation<Set<IPredicate>, L> createIndependenceRelation(
			final IndependenceSettings independenceSettings, final BasicPredicateFactory predicateFactory) {

		final boolean conditional = independenceSettings.getConditionality() != Conditionality.UNCONDITIONAL;

		final IIndependenceRelation<IPredicate, L> semanticCheck;
		switch (independenceSettings.getIndependenceType()) {
		case SEMANTIC:
			mLogger.info("Petri net LBE is using semantic-based independence relation.");
			semanticCheck = new SemanticIndependenceRelation<>(mServices, mManagedScript, conditional,
					!independenceSettings.useSemiCommutativity());
			break;
		case SYNTACTIC:
			mLogger.info("Petri net LBE is using variable-based independence relation.");
			semanticCheck = null;
			break;
		default:
			throw new AssertionError("unknown value: " + independenceSettings.getIndependenceType());
		}

		final IIndependenceRelation<IPredicate, L> variableCheck = new SyntacticIndependenceRelation<>();
		final IIndependenceRelation<IPredicate, L> unionCheck;
		if (semanticCheck == null) {
			unionCheck = variableCheck;
		} else {
			unionCheck = new UnionIndependenceRelation<>(Arrays.asList(variableCheck, semanticCheck));
		}

		switch (independenceSettings.getConditionality()) {
		case UNCONDITIONAL:
			assert !unionCheck.isConditional();
			return new CachedIndependenceRelation<>(ConditionTransformingIndependenceRelation.unconditional(unionCheck),
					getOrCreateIndependenceCache());
		case CONDITIONAL_CONJUNCTIVE:
			// It is important that this combination of predicates happens below the caching layer: Each call to
			// combinePredicates will return a distinct predicate, even for the same input set. Hence caching results
			// for combined predicates would have little to no effect.
			return new CachedIndependenceRelation<>(new ConditionTransformingIndependenceRelation<>(unionCheck,
					s -> combinePredicates(s, predicateFactory)), getOrCreateIndependenceCache());
		case CONDITIONAL_DISJUNCTIVE:
			return createDisjunctiveConditionalIndependence(unionCheck);
		default:
			throw new IllegalArgumentException(
					"Unsupported conditionality: " + independenceSettings.getConditionality());
		}
	}

	private IIndependenceRelation<Set<IPredicate>, L>
			createDisjunctiveConditionalIndependence(final IIndependenceRelation<IPredicate, L> independence) {
		// For this variant, it makes more sense to cache results for individual conditions rather than a set.
		// This way, queries for different sets can share results.
		final IIndependenceRelation<IPredicate, L> cachedCheck =
				new CachedIndependenceRelation<>(independence, getOrCreateIndependenceCache());

		// We apply here the optimization that eliminates satisfiable but irrelevant conditions. This usage is only
		// sound because we assume individual interpolants are unsatisfiable iff they are literally "false".
		// It is important for performance that this elimination happens outside the caching layer.
		final IIndependenceRelation<IPredicate, L> eliminatedCheck =
				new SemanticConditionEliminator<>(cachedCheck, PetriNetLargeBlockEncoding::isFalseState);

		// Lastly, we eliminate useless conditions (i.e. DebugPredicate or "true"; this is different from the work
		// done by SemanticConditionEliminator above) and then query for each condition separately.
		return new ConditionTransformingIndependenceRelation<>(
				new DisjunctiveConditionalIndependenceRelation<>(eliminatedCheck),
				PetriNetLargeBlockEncoding::eliminateIrrelevantPredicates);
	}

	private <S> IIndependenceCache<S, L> getOrCreateIndependenceCache() {
		if (mIndependenceCache == null) {
			mIndependenceCache = new DefaultIndependenceCache<>();
		}
		return (IIndependenceCache<S, L>) mIndependenceCache;
	}

	public IIndependenceCache<?, L> getIndependenceCache() {
		return mIndependenceCache;
	}

	private static Boolean isFalseState(final IPredicate state) {
		// We assume here that all inconsistent interpolant predicates are syntactically equal to "false".
		return SmtUtils.isFalseLiteral(state.getFormula());
	}

	private static IPredicate combinePredicates(final Set<IPredicate> predicates, final BasicPredicateFactory factory) {
		final Set<IPredicate> relevant = eliminateIrrelevantPredicates(predicates);
		if (relevant.isEmpty()) {
			return null;
		}
		return factory.and(relevant);
	}

	private static Set<IPredicate> eliminateIrrelevantPredicates(final Set<IPredicate> predicates) {
		return predicates.stream()
				.filter(p -> !(p instanceof DebugPredicate) && !SmtUtils.isTrueLiteral(p.getFormula()))
				.collect(Collectors.toSet());
	}

	private String generateTimeoutMessage(final BoundedPetriNet<L, IPredicate> petriNet) {
		return "applying " + getClass().getSimpleName() + " to Petri net that " + petriNet.sizeInformation();
	}

	public BoundedPetriNet<L, IPredicate> getResult() {
		return mResult;
	}

	public PetriNetLargeBlockEncodingBenchmarks getStatistics() {
		return new PetriNetLargeBlockEncodingBenchmarks(mStatistics);
	}
}
