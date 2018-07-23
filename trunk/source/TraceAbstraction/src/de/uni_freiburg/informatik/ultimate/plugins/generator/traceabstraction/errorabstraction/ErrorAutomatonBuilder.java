/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.IPredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.QuantifierEliminationPostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.DefaultTransFormulas;

/**
 * Constructs an error automaton for a given error trace.
 * <p>
 * TODO 2017-06-05 Christian: Should we apply simplifications?
 * <p>
 * TODO 2017-06-09 Christian: The successor 'True' (and 'False', but this does not matter) is never checked by the
 * {@link NondeterministicInterpolantAutomaton}. Is this a problem?
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type in the trace
 */
class ErrorAutomatonBuilder<LETTER extends IIcfgTransition<?>> implements IErrorAutomatonBuilder<LETTER> {
	/**
	 * This is used to avoid 'strange' predicates. Consider the example trace
	 * <p>
	 * {@literal call f(); assume true; return; assume true}
	 * <p>
	 * The WP predicates along this trace starting from 'false' are (from end to front):
	 * <p>
	 * 'false', 'false', 'true', 'true', 'false'
	 * <p>
	 * Thus the PRE sequence would be the negation and hence we would have 'false' as a predicate along a feasible
	 * trace.
	 */
	private static final boolean USE_TRUE_AS_CALL_PREDECESSOR_FOR_WP = true;
	/**
	 * {@code true} iff predicates are unified.
	 */
	private static final boolean UNIFY_PREDICATES = true;
	/**
	 * {@code true} iff formulas are postprocessed (i.e., simplified).
	 */
	private static final boolean APPLY_FORMULA_POSTPROCESSOR = true;
	/**
	 * {@code true} iff SP predicates are used.
	 */
	private static final boolean INTERSECT_WITH_SP_PREDICATES = false;
	/**
	 * {@code true} iff enhancement should be used.
	 */
	private static final boolean USE_ENHANCEMENT = false;

	/**
	 * Predicate transformer types.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private enum PredicateTransformerType {
		/**
		 * Weakest precondition.
		 */
		WP,
		/**
		 * Strongest postcondition.
		 */
		SP
	}

	private final NestedWordAutomaton<LETTER, IPredicate> mResultBeforeEnhancement;
	private final NondeterministicInterpolantAutomaton<LETTER> mResultAfterEnhancement;
	private IPredicate mErrorPrecondition;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param predicateFactory
	 *            predicate factory
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param csToolkit
	 *            SMT toolkit
	 * @param simplificationTechnique
	 *            simplification technique
	 * @param xnfConversionTechnique
	 *            XNF conversion technique
	 * @param symbolTable
	 *            symbol table
	 * @param predicateFactoryErrorAutomaton
	 *            predicate factory for the error automaton
	 * @param abstraction
	 *            alphabet
	 * @param trace
	 *            error trace
	 * @param iteration
	 *            CEGAR loop iteration in which this builder was created
	 * @param enhancementMode
	 *            mode for automaton enhancement
	 */
	@SuppressWarnings("squid:S00107")
	public ErrorAutomatonBuilder(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable,
			final PredicateFactoryForInterpolantAutomata predicateFactoryErrorAutomaton,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction, final NestedWord<LETTER> trace) {
		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final PredicateUnificationMechanism internalPredicateUnifier =
				new PredicateUnificationMechanism(predicateUnifier, UNIFY_PREDICATES);

		mResultBeforeEnhancement = constructStraightLineAutomaton(services, logger, csToolkit, predicateFactory,
				internalPredicateUnifier, simplificationTechnique, xnfConversionTechnique, symbolTable,
				predicateFactoryErrorAutomaton, NestedWordAutomataUtils.getVpAlphabet(abstraction), trace);

		mResultAfterEnhancement =
				USE_ENHANCEMENT
						? constructNondeterministicAutomaton(services, mResultBeforeEnhancement, csToolkit,
								internalPredicateUnifier, predicateFactory)
						: null;
	}

	@Override
	public ErrorAutomatonType getType() {
		return ErrorAutomatonType.ERROR_AUTOMATON;
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResultBeforeEnhancement() {
		return mResultBeforeEnhancement;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getResultAfterEnhancement() {
		return (mResultAfterEnhancement == null) ? mResultBeforeEnhancement : mResultAfterEnhancement;
	}

	@Override
	public IPredicate getErrorPrecondition() {
		assert mErrorPrecondition != null : "Precondition was not computed yet.";
		return mErrorPrecondition;
	}

	@Override
	public InterpolantAutomatonEnhancement getEnhancementMode() {
		return USE_ENHANCEMENT ? InterpolantAutomatonEnhancement.NO_SECOND_CHANCE
				: InterpolantAutomatonEnhancement.NONE;
	}

	@SuppressWarnings("squid:S00107")
	private NestedWordAutomaton<LETTER, IPredicate> constructStraightLineAutomaton(
			final IUltimateServiceProvider services, final ILogger logger, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final PredicateUnificationMechanism predicateUnifier,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final VpAlphabet<LETTER> alphabet, final NestedWord<LETTER> trace) throws AssertionError {
		final IPredicate falsePredicate = predicateUnifier.getFalsePredicate();
		final IPredicate truePredicate = predicateUnifier.getTruePredicate();
		final List<IPredicatePostprocessor> postprocessors;
		if (APPLY_FORMULA_POSTPROCESSOR) {
			final QuantifierEliminationPostprocessor qepp = new QuantifierEliminationPostprocessor(services, logger,
					csToolkit.getManagedScript(), predicateFactory, simplificationTechnique, xnfConversionTechnique);
			postprocessors = Collections.singletonList(qepp);
		} else {
			postprocessors = Collections.emptyList();
		}

		// compute 'wp' sequence from 'false'
		final TracePredicates wpPredicates = getPredicates(services, csToolkit, predicateFactory,
				simplificationTechnique, xnfConversionTechnique, symbolTable, truePredicate, trace, null,
				falsePredicate, postprocessors, PredicateTransformerType.WP);

		// negate 'wp' sequence to get 'pre'
		final List<IPredicate> wpIntermediatePredicates = wpPredicates.getPredicates();
		final List<IPredicate> preIntermediatePredicates = new ArrayList<>(wpIntermediatePredicates.size());
		for (final IPredicate wpPred : wpIntermediatePredicates) {
			preIntermediatePredicates.add(predicateFactory.not(wpPred));
		}
		final IPredicate prePrecondition = predicateFactory.not(wpPredicates.getPrecondition());

		final List<IPredicate> newIntermediatePredicates;
		final IPredicate newPostcondition;
		if (INTERSECT_WITH_SP_PREDICATES) {
			// compute 'sp' sequence from error precondition
			final TracePredicates spPredicates = getPredicates(services, csToolkit, predicateFactory,
					simplificationTechnique, xnfConversionTechnique, symbolTable, truePredicate, trace, prePrecondition,
					null, postprocessors, PredicateTransformerType.SP);
			assert (preIntermediatePredicates.size() == spPredicates.getPredicates().size());
			newIntermediatePredicates = new ArrayList<>(preIntermediatePredicates.size());
			final Iterator<IPredicate> preIt = preIntermediatePredicates.iterator();
			final Iterator<IPredicate> spIt = spPredicates.getPredicates().iterator();
			while (preIt.hasNext()) {
				final IPredicate pred = predicateFactory.and(preIt.next(), spIt.next());
				newIntermediatePredicates.add(predicateUnifier.getOrConstructPredicate(pred));
			}
			newPostcondition = spPredicates.getPostcondition();
		} else {
			newIntermediatePredicates = new ArrayList<>(preIntermediatePredicates.size());
			for (final IPredicate pred : preIntermediatePredicates) {
				newIntermediatePredicates.add(predicateUnifier.getOrConstructPredicate(pred));
			}
			newPostcondition = truePredicate;
		}

		// final predicates (unified)
		mErrorPrecondition = predicateUnifier.getOrConstructPredicate(prePrecondition);
		final TracePredicates newPredicates = new TracePredicates(mErrorPrecondition,
				predicateUnifier.getOrConstructPredicate(newPostcondition), newIntermediatePredicates);

		return new StraightLineInterpolantAutomatonBuilder<>(services, trace, alphabet,
				Collections.singletonList(newPredicates), predicateFactoryInterpolantAutomata,
				StraightLineInterpolantAutomatonBuilder.InitialAndAcceptingStateMode.ALL_INITIAL_ALL_ACCEPTING)
						.getResult();
	}

	private TracePredicates getPredicates(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IIcfgSymbolTable symbolTable,
			final IPredicate truePredicate, final NestedWord<LETTER> trace, final IPredicate precondition,
			final IPredicate postcondition, final List<IPredicatePostprocessor> postprocessors,
			final PredicateTransformerType predicateTransformer) throws AssertionError {
		final DefaultTransFormulas dtf = new DefaultTransFormulas(trace, precondition, postcondition,
				Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);
		final IterativePredicateTransformer ipt = new IterativePredicateTransformer(predicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), services, trace, precondition,
				postcondition, null, truePredicate, simplificationTechnique, xnfConversionTechnique, symbolTable);
		final TracePredicates predicates;
		try {
			switch (predicateTransformer) {
			case WP:
				predicates = ipt.computeWeakestPreconditionSequence(dtf, postprocessors,
						USE_TRUE_AS_CALL_PREDECESSOR_FOR_WP, false);
				break;
			case SP:
				predicates = ipt.computeStrongestPostconditionSequence(dtf, postprocessors);
				break;
			default:
				throw new IllegalArgumentException("Unknown predicate transformer: " + predicateTransformer);
			}
		} catch (final TraceInterpolationException e) {
			// TODO 2017-05-17 Christian: better error handling
			throw new AssertionError();
		}
		return predicates;
	}

	private NondeterministicInterpolantAutomaton<LETTER> constructNondeterministicAutomaton(
			final IUltimateServiceProvider services,
			final NestedWordAutomaton<LETTER, IPredicate> straightLineAutomaton, final CfgSmtToolkit csToolkit,
			final PredicateUnificationMechanism predicateUnifier, final PredicateFactory predicateFactory) {
		assert !containsPredicateState(straightLineAutomaton, predicateUnifier
				.getFalsePredicate()) : "The error trace is feasible; hence the predicate 'False' should not exist.";

		// 'True' state is needed by automaton construction
		if (!containsPredicateState(straightLineAutomaton, predicateUnifier.getTruePredicate())) {
			straightLineAutomaton.addState(true, true, predicateUnifier.getTruePredicate());
		}

		final ManagedScript mgdScript = csToolkit.getManagedScript();
		final MonolithicImplicationChecker mic = new MonolithicImplicationChecker(services, mgdScript);
		final PredicateTransformer<Term, IPredicate, TransFormula> pt =
				new PredicateTransformer<>(mgdScript, new TermDomainOperationProvider(services, mgdScript));
		final IHoareTripleChecker hoareTripleChecker =
				new InclusionInPreChecker(services, null, mic, pt, predicateFactory, csToolkit);
		return new NondeterministicErrorAutomaton<>(services, csToolkit, hoareTripleChecker, straightLineAutomaton,
				predicateUnifier.getPredicateUnifier());
	}

	private boolean containsPredicateState(final NestedWordAutomaton<LETTER, IPredicate> straightLineAutomaton,
			final IPredicate targetPredicate) {
		for (final IPredicate pred : straightLineAutomaton.getStates()) {
			if (pred == targetPredicate) {
				return true;
			}
		}
		return false;
	}
}
