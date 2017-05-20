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

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
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
	private static final boolean USE_NONDET_AUTOMATON = false;

	private final NestedWordAutomaton<LETTER, IPredicate> mAutomaton;

	public ErrorAutomatonBuilder(final IPredicateUnifier predicateUnifier, final PredicateFactory predicateFactory,
			final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfg<?> icfgContainer,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final IAutomaton<LETTER, IPredicate> abstraction, final NestedWord<LETTER> trace) {
		if (USE_NONDET_AUTOMATON) {
			mAutomaton = constructNondeterministicAutomaton(predicateUnifier, predicateFactory, csToolkit, services,
					simplificationTechnique, xnfConversionTechnique, icfgContainer, predicateFactoryInterpolantAutomata,
					abstraction, trace);
		} else {
			mAutomaton = constructStraightLineAutomaton(predicateUnifier, predicateFactory, csToolkit, services,
					simplificationTechnique, xnfConversionTechnique, icfgContainer, predicateFactoryInterpolantAutomata,
					abstraction, trace);
		}
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructNondeterministicAutomaton(
			final IPredicateUnifier predicateUnifier, final PredicateFactory predicateFactory,
			final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfg<?> icfgContainer,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final IAutomaton<LETTER, IPredicate> abstraction, final NestedWord<LETTER> trace) {
		final IHoareTripleChecker hoareTripleChecker = null;
		final boolean conservativeSuccessorCandidateSelection = true;
		final boolean secondChance = false;
		final NondeterministicInterpolantAutomaton<LETTER> result =
				new NondeterministicInterpolantAutomaton<>(services, csToolkit, hoareTripleChecker, mAutomaton,
						predicateUnifier, conservativeSuccessorCandidateSelection, secondChance);
		return null;
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructStraightLineAutomaton(
			final IPredicateUnifier predicateUnifier, final PredicateFactory predicateFactory,
			final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfg<?> icfgContainer,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final IAutomaton<LETTER, IPredicate> abstraction, final NestedWord<LETTER> trace) throws AssertionError {
		final IPredicate falsePredicate = predicateUnifier.getFalsePredicate();
		final IterativePredicateTransformer ipt = new IterativePredicateTransformer(predicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), services, trace, null,
				falsePredicate, null, predicateFactory.not(falsePredicate), simplificationTechnique,
				xnfConversionTechnique, icfgContainer.getCfgSmtToolkit().getSymbolTable());
		final DefaultTransFormulas dtf = new DefaultTransFormulas(trace, null, falsePredicate,
				Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);
		final TracePredicates weakestPreconditionSequence;
		try {
			weakestPreconditionSequence =
					ipt.computeWeakestPreconditionSequence(dtf, Collections.emptyList(), true, false);
		} catch (final TraceInterpolationException e) {
			throw new AssertionError();
		}

		return new StraightLineInterpolantAutomatonBuilder<>(services, new VpAlphabet<>(abstraction),
				predicateFactoryInterpolantAutomata, trace, weakestPreconditionSequence).getResult();
	}

	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mAutomaton;
	}

}
