/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * 
 * @author Betim Musa,
 * @author Matthias Heizmann
 *
 */
public class TwoTrackInterpolantAutomatonBuilder<LETTER> implements IInterpolantAutomatonBuilder<LETTER, IPredicate> {
	private final IUltimateServiceProvider mServices;

	private final NestedWord<LETTER> mNestedWord;
	private final NestedWordAutomaton<LETTER, IPredicate> mTTIA;
	private final CfgSmtToolkit mCsToolkit;
	private final TracePredicates mInterpolantsFP;
	private final TracePredicates mInterpolantsBP;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;

	public enum Sequence {
		FORWARD, BACKWARD
	}

	/**
	 * 
	 * @param nestedRun
	 * @param csToolkit
	 * @param traceCheck
	 * @param abstraction
	 * 
	 */
	public TwoTrackInterpolantAutomatonBuilder(final IUltimateServiceProvider services,
			final IRun<LETTER, IPredicate, ?> nestedRun, final CfgSmtToolkit csToolkit,
			final List<IPredicate> interpolantsFP, final List<IPredicate> interpolantsBP, final IPredicate preCondition,
			final IPredicate postCondition, final IAutomaton<LETTER, IPredicate> abstraction) {
		mServices = services;
		mPrecondition = preCondition;
		mPostcondition = postCondition;

		assert interpolantsFP != null : "interpolantsFP is null";
		assert interpolantsBP != null : "interpolantsBP is null";

		mInterpolantsFP = new TracePredicates(preCondition, postCondition, interpolantsFP);
		mInterpolantsBP = new TracePredicates(preCondition, postCondition, interpolantsBP);

		mNestedWord = NestedWord.nestedWord(nestedRun.getWord());
		mCsToolkit = csToolkit;
		mTTIA = buildTwoTrackInterpolantAutomaton(abstraction, abstraction.getStateFactory());
	}

	private NestedWordAutomaton<LETTER, IPredicate> buildTwoTrackInterpolantAutomaton(
			final IAutomaton<LETTER, IPredicate> abstraction, final IStateFactory<IPredicate> tAContentFactory) {
		final NestedWordAutomaton<LETTER, IPredicate> nwa =
				new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), new VpAlphabet<>(abstraction), tAContentFactory);

		// Add states, which contains the predicates computed via SP, WP.
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
	private void addStatesAccordingToPredicates(final NestedWordAutomaton<LETTER, IPredicate> nwa) {
		// add initial state
		nwa.addState(true, false, mInterpolantsFP.getPredicate(0));

		for (int i = 1; i < mNestedWord.length() + 1; i++) {
			final IPredicate forward = mInterpolantsFP.getPredicate(i);
			final IPredicate backward = mInterpolantsBP.getPredicate(i);
			if (!nwa.getStates().contains(forward)) {
				nwa.addState(false, isFalsePredicate(forward), forward);
			}
			if (!nwa.getStates().contains(backward)) {
				nwa.addState(false, isFalsePredicate(backward), backward);
			}
		}
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
	private void addBasicTransitions(final NestedWordAutomaton<LETTER, IPredicate> nwa) {
		for (int i = 0; i < mNestedWord.length(); i++) {
			addTransition(nwa, i, Sequence.FORWARD);
			addTransition(nwa, i, Sequence.BACKWARD);
		}
	}

	// /**
	// * This is a naive strategy to add transitions between the two interpolant types.
	// * Transitions are added as follows:
	// * 1. For each forwards predicate FP_i:
	// * 2. for each backwards predicate BP_j:
	// * 3. try to add the transition (FP_i, st_j, BP_j)
	// * 4. try to add the transition (BP_j, st_j, FP_i)
	// * @param nwa - the automaton to which the transitions are added.
	// */
	// private void addTotalTransitionsNaively(NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
	// for (int i = 0; i < mNestedWord.length(); i++) {
	// IPredicate fp_i = mInterpolantsFP[i];
	// for (int j = 0; j < mNestedWord.length(); j++) {
	// IPredicate bp_j = mInterpolantsBP[j];
	// if (mNestedWord.isReturnPosition(j)) {
	// int callPos = mNestedWord.getCallPosition(j);
	//
	// if (transitionFromOneStateToTheOppositeStateAllowed(fp_i, j, bp_j,
	// getInterpolantAtPosition(callPos - 1, mInterpolantsFP))) {
	// addTransition(nwa, fp_i, j, bp_j, true);
	// }
	// if (transitionFromOneStateToTheOppositeStateAllowed(bp_j, j, fp_i,
	// getInterpolantAtPosition(callPos-1, mInterpolantsBP))) {
	// addTransition(nwa, bp_j, j, fp_i, false);
	// }
	// } else {
	// if (transitionFromOneStateToTheOppositeStateAllowed(fp_i, j, bp_j, null)) {
	// addTransition(nwa, fp_i, j, bp_j, true);
	// }
	// if (transitionFromOneStateToTheOppositeStateAllowed(bp_j, j, fp_i, null)) {
	// addTransition(nwa, bp_j, j, fp_i, false);
	// }
	// }
	//
	// }
	// }
	// }

	// /**
	// Checks whether we are allowed to add a transition from a state annotated with the predicate p1 computed via
	// * SP (or WP) with the statement obtained by symbolPos to a state annotated with the assertion p2 computed via WP
	// (or SP).
	// * @param symbolPos - represents the corresponding statement
	// * @param callerPred - this predicate may be null if the statement represented by the given argument symbolPos is
	// not interprocedural,
	// * otherwise not
	// */
	// private boolean transitionFromOneStateToTheOppositeStateAllowed(IPredicate p1, int symbolPos, IPredicate p2,
	// IPredicate callerPred) {
	// CodeBlock statement = mNestedWord.getSymbol(symbolPos);
	// if (mNestedWord.isCallPosition(symbolPos)) {
	// return (mCsToolkit.isInductiveCall(p1, (Call) statement, p2) == LBool.UNSAT);
	// } else if (mNestedWord.isReturnPosition(symbolPos)) {
	// assert callerPred != null : "callerPred shouldn't be null for a Return statement.";
	// return (mCsToolkit.isInductiveReturn(p1, callerPred,(Return) statement, p2) == LBool.UNSAT);
	// } else {
	// return (mCsToolkit.isInductive(p1, (IInternalAction) statement, p2) == LBool.UNSAT);
	// }
	// }

	/**
	 * TODO: What if the post-condition is not the "False-Predicate"?
	 * 
	 * @param p
	 * @return
	 */
	private boolean isFalsePredicate(final IPredicate p) {
		if (p == mPostcondition) {
			return true;
		}
		// assert mCsToolkit.getPredicateFactory().isDontCare(p)
		// || !SmtUtils.isFalse(p.getFormula());
		return false;
	}

	private void addTransition(final NestedWordAutomaton<LETTER, IPredicate> nwa, final int symbolPos,
			final Sequence seq) {
		final LETTER symbol = mNestedWord.getSymbol(symbolPos);
		final IPredicate succ;
		if (seq == Sequence.FORWARD) {
			succ = mInterpolantsFP.getPredicate(symbolPos + 1);
		} else {
			succ = mInterpolantsBP.getPredicate(symbolPos + 1);
		}
		if (mNestedWord.isCallPosition(symbolPos)) {
			final IPredicate pred;
			if (seq == Sequence.FORWARD) {
				pred = mInterpolantsFP.getPredicate(symbolPos);
			} else {
				pred = mInterpolantsBP.getPredicate(symbolPos);
			}
			nwa.addCallTransition(pred, symbol, succ);
		} else if (mNestedWord.isReturnPosition(symbolPos)) {
			final IPredicate pred;
			if (seq == Sequence.FORWARD) {
				pred = mInterpolantsFP.getPredicate(symbolPos);
			} else {
				pred = mInterpolantsBP.getPredicate(symbolPos);
			}
			final int callPos = mNestedWord.getCallPosition(symbolPos);
			final IPredicate hier;
			if (seq == Sequence.FORWARD) {
				hier = mInterpolantsFP.getPredicate(callPos);
			} else {
				hier = mInterpolantsBP.getPredicate(callPos);
			}
			nwa.addReturnTransition(pred, hier, symbol, succ);
		} else {
			final IPredicate pred;
			if (seq == Sequence.FORWARD) {
				pred = mInterpolantsFP.getPredicate(symbolPos);
			} else {
				pred = mInterpolantsBP.getPredicate(symbolPos);
			}
			nwa.addInternalTransition(pred, symbol, succ);
		}
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mTTIA;
	}

}
