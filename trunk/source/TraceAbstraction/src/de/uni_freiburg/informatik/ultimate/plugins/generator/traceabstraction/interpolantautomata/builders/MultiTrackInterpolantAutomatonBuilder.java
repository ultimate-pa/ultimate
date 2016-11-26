/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

/**
 * Interpolant automaton builder for multiple sequences of interpolants.
 * <p>
 * This is a generalization of the {@link TwoTrackInterpolantAutomatonBuilder}.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class MultiTrackInterpolantAutomatonBuilder implements IInterpolantAutomatonBuilder<CodeBlock, IPredicate> {
	private final IUltimateServiceProvider mServices;
	private final NestedWord<CodeBlock> mNestedWord;
	private final List<InterpolantsPreconditionPostcondition> mInterpolantSequences;
	private final IPredicate mPostcondition;
	
	private final NestedWordAutomaton<CodeBlock, IPredicate> mResult;
	
	/**
	 * @param services
	 *            Ultimate services.
	 * @param nestedRun
	 *            nested run
	 * @param interpolantSequences
	 *            list of interpolant sequences
	 * @param abstraction
	 *            old abstraction
	 */
	public MultiTrackInterpolantAutomatonBuilder(final IUltimateServiceProvider services,
			final IRun<CodeBlock, IPredicate, ?> nestedRun,
			final List<InterpolantsPreconditionPostcondition> interpolantSequences,
			final IAutomaton<CodeBlock, IPredicate> abstraction) {
		if (interpolantSequences.isEmpty()) {
			throw new IllegalArgumentException("Empty list of interpolant sequences is not allowed.");
		}
		mServices = services;
		mInterpolantSequences = interpolantSequences;
		mNestedWord = NestedWord.nestedWord(nestedRun.getWord());
		
		// TODO What is the contract? Should all sequences share the same pre- and postcondition?
		mPostcondition = mInterpolantSequences.get(0).getPostcondition();
		
		mResult = constructInterpolantAutomaton(abstraction, abstraction.getStateFactory());
	}
	
	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return mResult;
	}
	
	private NestedWordAutomaton<CodeBlock, IPredicate> constructInterpolantAutomaton(
			final IAutomaton<CodeBlock, IPredicate> abstraction, final IStateFactory<IPredicate> taContentFactory) {
		final Set<CodeBlock> internalAlphabet = abstraction.getAlphabet();
		Set<CodeBlock> callAlphabet = new HashSet<>(0);
		Set<CodeBlock> returnAlphabet = new HashSet<>(0);
		
		if (abstraction instanceof INestedWordAutomatonSimple) {
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> abstractionAsNwa =
					(INestedWordAutomatonSimple<CodeBlock, IPredicate>) abstraction;
			callAlphabet = abstractionAsNwa.getCallAlphabet();
			returnAlphabet = abstractionAsNwa.getReturnAlphabet();
		}
		
		final NestedWordAutomaton<CodeBlock, IPredicate> nwa =
				new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), internalAlphabet,
						callAlphabet, returnAlphabet, taContentFactory);
		
		// add states, which contains the predicates computed via SP, WP.
		addStatesAccordingToPredicates(nwa);
		addBasicTransitions(nwa);
		
		return nwa;
	}
	
	/**
	 * Add a state for each forward predicate and for each backward predicate.
	 * 
	 * @param nwa
	 *            - the automaton to which the states are added
	 */
	private void addStatesAccordingToPredicates(final NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		// add initial state
		nwa.addState(true, false, mInterpolantSequences.get(0).getInterpolant(0));
		
		for (final InterpolantsPreconditionPostcondition interpolantSequence : mInterpolantSequences) {
			for (int i = 1; i < mNestedWord.length() + 1; i++) {
				final IPredicate interpolant = interpolantSequence.getInterpolant(i);
				if (!nwa.getStates().contains(interpolant)) {
					nwa.addState(false, isFalsePredicate(interpolant), interpolant);
				}
			}
		}
	}
	
	/**
	 * TODO: What if the post-condition is not the "False-Predicate".?
	 * 
	 * @param predicate
	 *            predicate
	 * @return {@code true} iff the predicate is {@code false}
	 */
	@SuppressWarnings("squid:S1698")
	private boolean isFalsePredicate(final IPredicate predicate) {
		return predicate == mPostcondition;
	}
	
	/**
	 * Add basic transitions in 3 steps. 1. For each predicate type add a transition from the precondition to the first
	 * predicate. (i.e. add transition (preCondition, st_0, FP_0), add transition (preCondition, st_0, BP_0)) 2. For
	 * each predicate type add a transition from the previous predicate to the current predicate. (i.e. add transition
	 * (FP_i-1, st_i, FP_i), add transition (BP_i-1, st_i, BP_i)) 3. For each predicate type add a transition from the
	 * last predicate to the post-condition. (i.e. add transition (FP_n-1, st_n, postCondition), add transition (BP_n-1,
	 * st_n, postCondition))
	 * 
	 * @param nwa
	 *            - the automaton to which the basic transition are added
	 */
	private void addBasicTransitions(final NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		for (final InterpolantsPreconditionPostcondition interpolantSequence : mInterpolantSequences) {
			for (int i = 0; i < mNestedWord.length(); i++) {
				addTransition(nwa, interpolantSequence, i);
			}
		}
	}
	
	private void addTransition(final NestedWordAutomaton<CodeBlock, IPredicate> nwa,
			final InterpolantsPreconditionPostcondition interpolantSequence, final int symbolPos) {
		final CodeBlock symbol = mNestedWord.getSymbol(symbolPos);
		final IPredicate succ;
		succ = interpolantSequence.getInterpolant(symbolPos + 1);
		if (mNestedWord.isCallPosition(symbolPos)) {
			final IPredicate pred = interpolantSequence.getInterpolant(symbolPos);
			nwa.addCallTransition(pred, symbol, succ);
		} else if (mNestedWord.isReturnPosition(symbolPos)) {
			final IPredicate pred = interpolantSequence.getInterpolant(symbolPos);
			final int callPos = mNestedWord.getCallPosition(symbolPos);
			final IPredicate hier = interpolantSequence.getInterpolant(callPos);
			nwa.addReturnTransition(pred, hier, symbol, succ);
		} else {
			final IPredicate pred = interpolantSequence.getInterpolant(symbolPos);
			nwa.addInternalTransition(pred, symbol, succ);
		}
	}
}
