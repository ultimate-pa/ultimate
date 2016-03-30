/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.DivisibilityPredicateGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * Deterministic interpolant automaton with on-demand construction.
 * The successor state for a given state ψ and a CodeBlock cb are is 
 * constructed as follows.
 * First we construct a set S of successors very similar to the construction
 * in {@see NondeterministicInterpolantAutomaton}. However, since this automaton
 * is deterministic, we do not have several successors. Instead, we take
 * as successor the conjunction of all IPredicates in S.
 * If the IPredicate that represents this conjunction is not yet a state of
 * this automaton, we add this state.
 * @author Matthias Heizmann
 *
 */
public class DeterministicInterpolantAutomaton extends BasicAbstractInterpolantAutomaton {
	
	private final Map<Set<IPredicate>, IPredicate> m_InputPreds2ResultPreds = 
			new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> m_ResPred2InputPreds = 
			new HashRelation<IPredicate, IPredicate>();


	protected final Set<IPredicate> m_NonTrivialPredicates;
	
	/**
	 * Split up predicates in their conjuncts. 
	 * First experiments on few examples showed that this is decreasing the
	 * performance.
	 */
	private final boolean m_Cannibalize;
	private final boolean m_SplitNumericEqualities = true;
	private final boolean m_DivisibilityPredicates = false;
	private final boolean m_ConservativeSuccessorCandidateSelection;
	

	

	public DeterministicInterpolantAutomaton(IUltimateServiceProvider services, 
			SmtManager smtManager, ModifiableGlobalVariableManager modglobvarman, IHoareTripleChecker hoareTripleChecker,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction, 
			NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton, 
			PredicateUnifier predicateUnifier, Logger logger, 
			boolean conservativeSuccessorCandidateSelection,
			boolean cannibalize) {
		super(services, smtManager, hoareTripleChecker, true, abstraction, 
				predicateUnifier, 
				interpolantAutomaton, logger);
		m_Cannibalize = cannibalize;
		m_ConservativeSuccessorCandidateSelection = conservativeSuccessorCandidateSelection;
		if (m_ConservativeSuccessorCandidateSelection && m_Cannibalize) {
			throw new IllegalArgumentException("ConservativeSuccessorCandidateSelection and Cannibalize are incompatible");
		}
		Collection<IPredicate> allPredicates;
		if (m_Cannibalize ) {
			allPredicates = m_PredicateUnifier.cannibalizeAll(m_SplitNumericEqualities, interpolantAutomaton.getStates().toArray(new IPredicate[0]));
			for (IPredicate pred : allPredicates) {
				if (!interpolantAutomaton.getStates().contains(pred)) {
					interpolantAutomaton.addState(false, false, pred);
				}
			}
		} else {
			allPredicates = interpolantAutomaton.getStates(); 
		}
		if (m_DivisibilityPredicates) {
			allPredicates = new ArrayList<IPredicate>(allPredicates);
			DivisibilityPredicateGenerator dpg = new DivisibilityPredicateGenerator(m_SmtManager, m_PredicateUnifier);
			Collection<IPredicate> divPreds = dpg.divisibilityPredicates(allPredicates);
			allPredicates.addAll(divPreds);
			for (IPredicate pred : divPreds) {
				if (!interpolantAutomaton.getStates().contains(pred)) {
					interpolantAutomaton.addState(false, false, pred);
				}
			}
		}
		
		assert m_IaTrueState.getFormula().toString().equals("true");
		assert allPredicates.contains(m_IaTrueState);
		m_AlreadyConstrucedAutomaton.addState(true, false, m_IaTrueState);
		m_ResPred2InputPreds.addPair(m_IaTrueState, m_IaTrueState);
		assert m_IaFalseState.getFormula().toString().equals("false");
		assert allPredicates.contains(m_IaFalseState);
		m_AlreadyConstrucedAutomaton.addState(false, true, m_IaFalseState);
		m_ResPred2InputPreds.addPair(m_IaFalseState, m_IaFalseState);

		m_NonTrivialPredicates = new HashSet<IPredicate>();
		for (IPredicate state : allPredicates) {
			if (state != m_IaTrueState && state != m_IaFalseState) {
				processResPredInputPredsMapping(state);
				m_NonTrivialPredicates.add(state);
			}
		}

		mLogger.info(startMessage());
	}

	/**
	 * Add add input states that are 
	 * 1. implied by resPred
	 * 2. contained in m_InterpolantAutomaton
	 * 3. different from "true"
	 * to the  m_ResPred2InputPreds Map
	 */
	private void processResPredInputPredsMapping(IPredicate resPred) {
		Set<IPredicate> impliedPredicates = 
				m_PredicateUnifier.getCoverageRelation().getCoveringPredicates(resPred);
		for (IPredicate impliedPredicate : impliedPredicates) {
			if (impliedPredicate != m_IaTrueState && m_InputInterpolantAutomaton.getStates().contains(impliedPredicate)) {
				m_ResPred2InputPreds.addPair(resPred, impliedPredicate);
			}
		}
	}
	
	@Override
	protected String startMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Constructing interpolant automaton ");
		sb.append("starting with ");
		sb.append(m_NonTrivialPredicates.size() + 2);
		sb.append(" interpolants.");
		return sb.toString();
	}
	
	@Override
	protected String switchToReadonlyMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Switched to read-only mode: deterministic interpolant automaton has ");
		sb.append(m_AlreadyConstrucedAutomaton.size()).append(" states. ");
		return sb.toString();
	}
	
	@Override
	protected String switchToOnTheFlyConstructionMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Switched to On-DemandConstruction mode: deterministic interpolant automaton has ");
		sb.append(m_AlreadyConstrucedAutomaton.size()).append(" states. ");
		return sb.toString();
	}


	@Override
	protected void addOtherSuccessors(IPredicate resPred, IPredicate resHier,
			CodeBlock letter, SuccessorComputationHelper sch,
			final Set<IPredicate> inputSuccs) {
		for (IPredicate succCand : selectSuccessorCandidates(resPred, resHier)) {
			if (!inputSuccs.contains(succCand)) {
				Validity sat = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
				if (sat == Validity.VALID) {
					inputSuccs.add(succCand);
				}
			}
		}
	}
	
	private Set<IPredicate> selectSuccessorCandidates(IPredicate resPred, IPredicate resHier) {
		if (m_ConservativeSuccessorCandidateSelection ) {
			return selectSuccessorCandidates_TryConservative(resPred, resHier);
		} else {
			return selectSuccessorCandidates_TryAll();
		}
	}
	
	private Set<IPredicate> selectSuccessorCandidates_TryConservative(IPredicate resPred, IPredicate resHier) {
		Set<IPredicate> succCands;
		if (resHier != null) {
			succCands = new HashSet<IPredicate>();
			succCands.addAll(m_ResPred2InputPreds.getImage(resPred));
			succCands.addAll(m_ResPred2InputPreds.getImage(resHier));
		} else {
			succCands = m_ResPred2InputPreds.getImage(resPred);
		}
		return succCands;
	}
	
	private Set<IPredicate> selectSuccessorCandidates_TryAll() {
		return m_NonTrivialPredicates;		
	}


	/**
	 * Add all successors of resPred, resHier, and letter in automaton.
	 * If resPred and resHier were constructed as a conjunction of 
	 * inputPredicates, we also take the conjuncts.
	 * @param inputSuccs 
	 */
	protected void addInputAutomatonSuccs(
			IPredicate resPred, IPredicate resHier, CodeBlock letter,
			SuccessorComputationHelper sch, Set<IPredicate> inputSuccs) {
		Set<IPredicate> resPredConjuncts = m_ResPred2InputPreds.getImage(resPred);
		assert m_Cannibalize || resPredConjuncts != null;
		if (resPredConjuncts == null) {
			resPredConjuncts = Collections.emptySet();
		}
		final IterableWithAdditionalElement<IPredicate> resPredConjunctsWithTrue = 
				new IterableWithAdditionalElement<IPredicate>(resPredConjuncts, m_IaTrueState);
		final IterableWithAdditionalElement<IPredicate> resHierConjunctsWithTrue;
		if (resHier == null) {
			resHierConjunctsWithTrue = null;
		} else {
			Set<IPredicate> resHierConjuncts;
			resHierConjuncts = m_ResPred2InputPreds.getImage(resHier);
			resHierConjunctsWithTrue = new IterableWithAdditionalElement<IPredicate>(resHierConjuncts, m_IaTrueState);
		}
		for (IPredicate inputPred : resPredConjunctsWithTrue) {
			if (resHier == null) {
				inputSuccs.addAll(sch.getSuccsInterpolantAutomaton(inputPred, null, letter));
			} else {
				for (IPredicate inputHier : resHierConjunctsWithTrue) {
					inputSuccs.addAll(sch.getSuccsInterpolantAutomaton(inputPred, inputHier, letter));
				}
			}
		}
	}

	




	private IPredicate getOrConstructPredicate(Set<IPredicate> succs) {
//		assert m_InterpolantAutomaton.getStates().containsAll(succs);
		final IPredicate result;
		if (succs.isEmpty()) {
			result = m_IaTrueState;
		} else if (succs.size() == 1) {
			result = succs.iterator().next();
			if (!m_AlreadyConstrucedAutomaton.contains(result)) {
				m_AlreadyConstrucedAutomaton.addState(false, false, result);
			}
		} else {
			IPredicate resSucc = m_InputPreds2ResultPreds.get(succs);
			if (resSucc == null) {
				resSucc = m_PredicateUnifier.getOrConstructPredicateForConjunction(succs);
				m_InputPreds2ResultPreds.put(succs, resSucc);
				for (IPredicate succ : succs) {
					assert m_AlreadyConstrucedAutomaton.contains(succ) || 
						m_InputInterpolantAutomaton.getStates().contains(succ) : "unknown state " + succ; 
					if (m_NonTrivialPredicates.contains(succ)) {
						m_ResPred2InputPreds.addPair(resSucc, succ);
					}
				}
				if (!m_AlreadyConstrucedAutomaton.contains(resSucc)) {
					processResPredInputPredsMapping(resSucc);
					m_AlreadyConstrucedAutomaton.addState(false, false, resSucc);
				}
			} 
			result = resSucc;
		}
		return result;
	}

	@Override
	protected void constructSuccessorsAndTransitions(IPredicate resPred,
			IPredicate resHier, CodeBlock letter, 
			SuccessorComputationHelper sch, Set<IPredicate> inputSuccs) {
		IPredicate resSucc = getOrConstructPredicate(inputSuccs);
		sch.addTransition(resPred, resHier, letter, resSucc);
		sch.reportSuccsComputed(resPred, resHier, letter);
	}
	
	
}
