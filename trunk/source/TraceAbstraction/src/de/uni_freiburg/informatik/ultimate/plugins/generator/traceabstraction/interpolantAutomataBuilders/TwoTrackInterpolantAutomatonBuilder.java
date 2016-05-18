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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

public class TwoTrackInterpolantAutomatonBuilder {
	private final IUltimateServiceProvider m_Services;
	
	
	private final NestedWord<CodeBlock> m_NestedWord;
//	private ArrayList<IPredicate> m_StateSequence;
	NestedWordAutomaton<CodeBlock, IPredicate> m_TTIA;
	private final SmtManager m_SmtManager;

	private final InterpolantsPreconditionPostcondition m_InterpolantsFP;

	private final InterpolantsPreconditionPostcondition m_InterpolantsBP;


	private final IPredicate m_Precondition;


	private final IPredicate m_Postcondition;
	
	private static boolean m_TotalTransitions = false;
	
	public enum Sequence { FORWARD, BACKWARD }
	
	/**
	 * 
	 * @param nestedRun
	 * @param smtManager
	 * @param traceChecker
	 * @param abstraction
	 * @author Betim Musa, Matthias Heizmann
	 */
	public TwoTrackInterpolantAutomatonBuilder(
			IUltimateServiceProvider services, 
			IRun<CodeBlock,IPredicate> nestedRun,
			SmtManager smtManager,
			List<IPredicate> interpolantsFP,
			List<IPredicate> interpolantsBP,
			IPredicate preCondition,
			IPredicate postCondition,
			IAutomaton<CodeBlock, IPredicate> abstraction) {
		m_Services = services;
		m_Precondition = preCondition;
		m_Postcondition = postCondition;
		
		assert interpolantsFP != null : "interpolantsFP is null";
		assert interpolantsBP != null : "interpolantsBP is null";

		m_InterpolantsFP = new InterpolantsPreconditionPostcondition(preCondition, postCondition, interpolantsFP);
		m_InterpolantsBP = new InterpolantsPreconditionPostcondition(preCondition, postCondition, interpolantsBP);
		
		m_NestedWord = NestedWord.nestedWord(nestedRun.getWord());
		m_SmtManager = smtManager;
		m_TTIA = buildTwoTrackInterpolantAutomaton(abstraction, abstraction.getStateFactory());
	}
	
	public NestedWordAutomaton<CodeBlock, IPredicate> 
	buildTwoTrackInterpolantAutomaton(IAutomaton<CodeBlock, IPredicate> abstraction,
			StateFactory<IPredicate> tAContentFactory) {
		Set<CodeBlock> internalAlphabet = abstraction.getAlphabet();
		Set<CodeBlock> callAlphabet = new HashSet<CodeBlock>(0);
		Set<CodeBlock> returnAlphabet = new HashSet<CodeBlock>(0);

		if (abstraction instanceof INestedWordAutomatonSimple) {
			INestedWordAutomatonSimple<CodeBlock, IPredicate> abstractionAsNwa = (INestedWordAutomatonSimple<CodeBlock, IPredicate>) abstraction;
			callAlphabet = abstractionAsNwa.getCallAlphabet();
			returnAlphabet = abstractionAsNwa.getReturnAlphabet();
		}
		
		NestedWordAutomaton<CodeBlock, IPredicate> nwa = new NestedWordAutomaton<CodeBlock, IPredicate>(
				new AutomataLibraryServices(m_Services), internalAlphabet, callAlphabet, returnAlphabet, tAContentFactory);

		// Add states, which contains the predicates computed via SP, WP.
		addStatesAccordingToPredicates(nwa);
		addBasicTransitions(nwa);

//		if (m_TotalTransitions) {
//			addTotalTransitionsNaively(nwa);
//		}
		return nwa;
	}
	
	/**
	 * Add a state for each forward predicate and for each backward predicate.
	 * @param nwa - the automaton to which the states are added
	 */
	private void addStatesAccordingToPredicates(NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		// add initial state
		nwa.addState(true, false, m_InterpolantsFP.getInterpolant(0));
		
		for (int i=1; i < m_NestedWord.length() + 1; i++) {
			IPredicate forward = m_InterpolantsFP.getInterpolant(i);
			IPredicate backward = m_InterpolantsBP.getInterpolant(i);
			if (!nwa.getStates().contains(forward)) {
				nwa.addState(false, isFalsePredicate(forward), forward);
			}
			if (!nwa.getStates().contains(backward)) {
				nwa.addState(false, isFalsePredicate(backward), backward);
			}
		}
	}
	
	/**
	 * Add basic transitions in 3 steps.
	 * 1. For each predicate type add a transition from the precondition to the first predicate.
	 * (i.e. add transition (preCondition, st_0, FP_0), add transition (preCondition, st_0, BP_0))
	 * 2. For each predicate type add a transition from the previous predicate to the current predicate.
	 * (i.e. add transition (FP_i-1, st_i, FP_i), add transition (BP_i-1, st_i, BP_i))
	 * 3. For each predicate type add a transition from the last predicate to the post-condition.
	 * (i.e. add transition (FP_n-1, st_n, postCondition), add transition (BP_n-1, st_n, postCondition))
	 * @param nwa - the automaton to which the basic transition are added
	 */
	private void addBasicTransitions(NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		for (int i=0; i < m_NestedWord.length(); i++) {
			addTransition(nwa, i, Sequence.FORWARD);
			addTransition(nwa, i, Sequence.BACKWARD);
		}
	}
	
	
//	/**
//	 * This is a naive strategy to add transitions between the two interpolant types.
//	 * Transitions are added as follows:
//	 * 1. For each forwards predicate FP_i: 
//	 * 2.     for each backwards predicate BP_j:
//	 * 3.          try to add the transition (FP_i, st_j, BP_j)
//	 * 4.          try to add the transition (BP_j, st_j, FP_i) 
//	 * @param nwa - the automaton to which the transitions are added.
//	 */
//	private void addTotalTransitionsNaively(NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
//		for (int i = 0; i < m_NestedWord.length(); i++) {
//			IPredicate fp_i = m_InterpolantsFP[i];
//			for (int j = 0; j < m_NestedWord.length(); j++) {
//				IPredicate bp_j = m_InterpolantsBP[j];
//				if (m_NestedWord.isReturnPosition(j)) {
//					int callPos = m_NestedWord.getCallPosition(j);
//					
//					if (transitionFromOneStateToTheOppositeStateAllowed(fp_i, j, bp_j, 
//							getInterpolantAtPosition(callPos - 1, m_InterpolantsFP))) {
//						addTransition(nwa, fp_i, j, bp_j, true);
//					}
//					if (transitionFromOneStateToTheOppositeStateAllowed(bp_j, j, fp_i,
//							getInterpolantAtPosition(callPos-1, m_InterpolantsBP))) {
//						addTransition(nwa, bp_j, j, fp_i, false);
//					}
//				} else {
//					if (transitionFromOneStateToTheOppositeStateAllowed(fp_i, j, bp_j, null)) {
//						addTransition(nwa, fp_i, j, bp_j, true);
//					}
//					if (transitionFromOneStateToTheOppositeStateAllowed(bp_j, j, fp_i, null)) {
//						addTransition(nwa, bp_j, j, fp_i, false);
//					}
//				}
//				
//			}
//		}
//	}
	
	/**
	 Checks whether we are allowed to add a transition from a state annotated with the predicate p1 computed via
	 * SP (or WP)  with the statement obtained by symbolPos to a state annotated with the assertion p2 computed via WP (or SP).
	 * @param symbolPos - represents the corresponding statement
	 * @param callerPred - this predicate may be null if the statement represented by the given argument symbolPos is not interprocedural,
	 *               otherwise not
	 */
	private boolean transitionFromOneStateToTheOppositeStateAllowed(IPredicate p1, int symbolPos, IPredicate p2, IPredicate callerPred) {
		CodeBlock statement = m_NestedWord.getSymbol(symbolPos);
		if (m_NestedWord.isCallPosition(symbolPos)) {
			return (m_SmtManager.isInductiveCall(p1, (Call) statement, p2) == LBool.UNSAT);
		} else if (m_NestedWord.isReturnPosition(symbolPos)) {
			assert callerPred != null : "callerPred shouldn't be null for a Return statement.";
			return (m_SmtManager.isInductiveReturn(p1, callerPred,(Return) statement, p2) == LBool.UNSAT);
		} else {
			return (m_SmtManager.isInductive(p1, (IInternalAction) statement, p2) == LBool.UNSAT);
		}
	}
	
	
	/**
	 * TODO: What if the post-condition is not the "False-Predicate"?
	 * @param p
	 * @return
	 */
	private boolean isFalsePredicate(IPredicate p) {
		if (p == m_Postcondition) {
			return true;
		} else {
			assert m_SmtManager.getPredicateFactory().isDontCare(p) || p.getFormula() != m_SmtManager.getScript().term("false");
			return false;
		}
	}
	
	
	private void addTransition(NestedWordAutomaton<CodeBlock, IPredicate> nwa,
			int symbolPos, Sequence seq) {
		CodeBlock symbol = m_NestedWord.getSymbol(symbolPos);
		final IPredicate succ;
		if (seq == Sequence.FORWARD) {
			succ = m_InterpolantsFP.getInterpolant(symbolPos + 1);
		} else {
			succ = m_InterpolantsBP.getInterpolant(symbolPos + 1);
		}
		if (m_NestedWord.isCallPosition(symbolPos)) {
			final IPredicate pred;
			if (seq == Sequence.FORWARD) {
				pred = m_InterpolantsFP.getInterpolant(symbolPos);
			} else {
				pred = m_InterpolantsBP.getInterpolant(symbolPos);
			}
			nwa.addCallTransition(pred, symbol, succ);
		} else if (m_NestedWord.isReturnPosition(symbolPos)) {
			final IPredicate pred;
			if (seq == Sequence.FORWARD) { 
				pred = m_InterpolantsFP.getInterpolant(symbolPos);
			} else {
				pred = m_InterpolantsBP.getInterpolant(symbolPos);
			}
			int callPos = m_NestedWord.getCallPosition(symbolPos);
			final IPredicate hier;
			if (seq == Sequence.FORWARD) {
				hier = m_InterpolantsFP.getInterpolant(callPos);
			} else {
				hier = m_InterpolantsBP.getInterpolant(callPos);
			}
			nwa.addReturnTransition(pred, hier, symbol, succ);
		} else {
			final IPredicate pred;
			if (seq == Sequence.FORWARD) { 
				pred = m_InterpolantsFP.getInterpolant(symbolPos);
			} else {
				pred = m_InterpolantsBP.getInterpolant(symbolPos);
			}
			nwa.addInternalTransition(pred, symbol,  succ);
		}
	}
	
	
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return m_TTIA;
	}

}
