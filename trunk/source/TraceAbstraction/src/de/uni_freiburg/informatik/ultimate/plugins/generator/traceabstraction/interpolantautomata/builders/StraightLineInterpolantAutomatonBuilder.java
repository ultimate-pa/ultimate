/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;

/**
 * Build an interpolant automaton whose shape is a straight line. The input for this construction is a traceCheck that
 * has proven that its trace is infeasible. The result of this construction is a NestedWordAutomaton object that can
 * still be modified by adding additional states or transitions. The result has one initial state which is the
 * precondition of the trace check, the result has one accepting/final state which is the postcondition of the trace
 * check, the result has one state for each interpolant, the result has one transition for each CodeBlock in the trace.
 * The result accepts the word/trace of the trace check. IPredicates may occur several times in the array of
 * interpolants, hence the resulting automaton may also have loops and accept more than a single word.
 *
 * @author Matthias Heizmann
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class StraightLineInterpolantAutomatonBuilder<LETTER extends IAction>
		implements IInterpolantAutomatonBuilder<LETTER, IPredicate> {
	/**
	 * Determines which states become initial and accepting in the automaton.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum InitialAndAcceptingStateMode {
		/**
		 * Only the first state becomes initial and the last state becomes accepting.
		 */
		ONLY_FIRST_INITIAL_LAST_ACCEPTING,
		/**
		 * All states become initial and accepting.
		 */
		ALL_INITIAL_ALL_ACCEPTING
	}

	private final IUltimateServiceProvider mServices;
	private final NestedWordAutomaton<LETTER, IPredicate> mResult;

	/**
	 * Constructor from a general trace and predicate provider.
	 */
	public StraightLineInterpolantAutomatonBuilder(final IUltimateServiceProvider services,
			final VpAlphabet<LETTER> alphabet, final PredicateFactoryForInterpolantAutomata predicateFactory,
			final NestedWord<LETTER> trace, final TracePredicates tracePredicates,
			final InitialAndAcceptingStateMode acceptingStateMode) {
		mServices = services;
		mResult = new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), alphabet, predicateFactory);
		addStatesAndTransitions(trace, tracePredicates, acceptingStateMode);
	}

	/**
	 * Convenience constructor from interpolants.
	 */
	@SuppressWarnings("unchecked")
	public StraightLineInterpolantAutomatonBuilder(final IUltimateServiceProvider services,
			final VpAlphabet<LETTER> alphabet, final IInterpolantGenerator<LETTER> interpolantGenerator,
			final PredicateFactoryForInterpolantAutomata predicateFactory,
			final InitialAndAcceptingStateMode acceptingStateMode) {
		this(services, alphabet, predicateFactory, (NestedWord<LETTER>) interpolantGenerator.getTrace(),
				new TracePredicates(interpolantGenerator), acceptingStateMode);
	}

	private void addStatesAndTransitions(final NestedWord<LETTER> trace, final TracePredicates tracePredicates,
			final InitialAndAcceptingStateMode initAndAcceptStateMode) {
		final boolean isInitial;
		final boolean isAccepting;
		switch (initAndAcceptStateMode) {
		case ONLY_FIRST_INITIAL_LAST_ACCEPTING:
			isInitial = false;
			isAccepting = false;
			break;
		case ALL_INITIAL_ALL_ACCEPTING:
			isInitial = true;
			isAccepting = true;
			break;
		default:
			throw new IllegalArgumentException("Unknown mode: " + initAndAcceptStateMode);
		}
		mResult.addState(true, isAccepting, tracePredicates.getPrecondition());
		if (tracePredicates.getPrecondition() != tracePredicates.getPostcondition()) {
			// only add if not a duplicate
			mResult.addState(isInitial, true, tracePredicates.getPostcondition());
		}
		for (int i = 0; i < trace.length(); i++) {
			final IPredicate pred = tracePredicates.getPredicate(i);
			final IPredicate succ = tracePredicates.getPredicate(i + 1);
			assert mResult.getStates().contains(pred);
			if (!mResult.getStates().contains(succ)) {
				mResult.addState(isInitial, isAccepting, succ);
			}
			if (trace.isCallPosition(i)) {
				mResult.addCallTransition(pred, trace.getSymbol(i), succ);
			} else if (trace.isReturnPosition(i)) {
				assert !trace.isPendingReturn(i);
				final int callPos = trace.getCallPosition(i);
				final IPredicate hierPred = tracePredicates.getPredicate(callPos);
				mResult.addReturnTransition(pred, hierPred, trace.getSymbol(i), succ);
			} else {
				assert trace.isInternalPosition(i);
				mResult.addInternalTransition(pred, trace.getSymbol(i), succ);
			}
		}
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mResult;
	}
}
