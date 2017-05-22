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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TracePredicates;

/**
 * Constructs an error automaton for a given error trace.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type in the trace
 */
public class ErrorAutomatonBuilder<LETTER extends IIcfgTransition<?>> {
	// TODO 2017-05-17 Christian: Make this a setting?
	private static final boolean USE_NONDET_AUTOMATON_ENHANCEMENT = false;

	private final NestedWordAutomaton<LETTER, IPredicate> mResult;

	public ErrorAutomatonBuilder(final IPredicateUnifier predicateUnifier, final PredicateFactory predicateFactory,
			final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfg<?> icfgContainer,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final VpAlphabet<LETTER> alphabet, final NestedWord<LETTER> trace) {
		final NestedWordAutomaton<LETTER, IPredicate> straightLineAutomaton = constructStraightLineAutomaton(services,
				csToolkit, predicateFactory, predicateUnifier.getFalsePredicate(), simplificationTechnique,
				xnfConversionTechnique, icfgContainer, predicateFactoryInterpolantAutomata, alphabet, trace);

		if (USE_NONDET_AUTOMATON_ENHANCEMENT) {
			mResult = constructNondeterministicAutomaton(services, straightLineAutomaton, csToolkit, predicateUnifier);
		} else {
			mResult = straightLineAutomaton;
		}
	}

	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mResult;
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructStraightLineAutomaton(
			final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final IPredicate falsePredicate,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfg<?> icfgContainer,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final VpAlphabet<LETTER> alphabet, final NestedWord<LETTER> trace) throws AssertionError {
		// compute 'wp' sequence from 'false'
		final IterativePredicateTransformer ipt = new IterativePredicateTransformer(predicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), services, trace, null,
				falsePredicate, null, predicateFactory.not(falsePredicate), simplificationTechnique,
				xnfConversionTechnique, icfgContainer.getCfgSmtToolkit().getSymbolTable());
		final DefaultTransFormulas dtf = new DefaultTransFormulas(trace, null, falsePredicate,
				Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);
		final TracePredicates wpPredicate;
		try {
			wpPredicate = ipt.computeWeakestPreconditionSequence(dtf, Collections.emptyList(), true, false);
		} catch (final TraceInterpolationException e) {
			// TODO 2017-05-17 Christian: better error handling
			throw new AssertionError();
		}

		// negate 'wp' sequence to get 'pre'
		final List<IPredicate> oldIntermediatePredicates = wpPredicate.getPredicates();
		final List<IPredicate> newIntermediatePredicates = new ArrayList<>(oldIntermediatePredicates.size());
		for (final IPredicate pred : oldIntermediatePredicates) {
			newIntermediatePredicates.add(predicateFactory.not(pred));
		}
		final IPredicate newPrecondition = predicateFactory.not(wpPredicate.getPrecondition());
		final IPredicate newPostcondition = predicateFactory.not(wpPredicate.getPostcondition());
		final TracePredicates newPredicates =
				new TracePredicates(newPrecondition, newPostcondition, newIntermediatePredicates);

		// TODO 2017-05-17 Christian: additionally compute 'sp' sequence and intersect

		return new StraightLineInterpolantAutomatonBuilder<>(services, alphabet, predicateFactoryInterpolantAutomata,
				trace, newPredicates).getResult();
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructNondeterministicAutomaton(
			final IUltimateServiceProvider services,
			final INestedWordAutomaton<LETTER, IPredicate> straightLineAutomaton, final CfgSmtToolkit csToolkit,
			final IPredicateUnifier predicateUnifier) {
		// 2017-05-17 Christian: construct right object
		final IHoareTripleChecker hoareTripleChecker = null;
		final boolean conservativeSuccessorCandidateSelection = false;
		final boolean secondChance = false;
		final NondeterministicInterpolantAutomaton<LETTER> result =
				new NondeterministicInterpolantAutomaton<>(services, csToolkit, hoareTripleChecker,
						straightLineAutomaton, predicateUnifier, conservativeSuccessorCandidateSelection, secondChance);
		// TODO 2017-05-17 Christian: How do we get the correct type here? Should the CEGAR class be refactored?
		return null;
	}
}
