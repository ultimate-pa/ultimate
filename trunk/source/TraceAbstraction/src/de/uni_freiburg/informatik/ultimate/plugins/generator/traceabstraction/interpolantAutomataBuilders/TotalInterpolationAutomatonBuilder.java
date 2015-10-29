/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.Transitionlet;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkData;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkDataProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerPathInvariantsWithFallback;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

public class TotalInterpolationAutomatonBuilder {

	private ArrayList<IPredicate> m_StateSequence;
	// private final IPredicate[] m_Interpolants;
	private final NestedWordAutomaton<CodeBlock, IPredicate> m_IA;
	private final PredicateUnifier m_PredicateUnifier;
	// private final TraceChecker m_TraceChecker;
	private final INestedWordAutomaton<CodeBlock, IPredicate> m_Abstraction;

	private final SmtManager m_SmtManager;

	private final ArrayDeque<IPredicate> m_Worklist = new ArrayDeque<IPredicate>();
	private final Set<IPredicate> m_Annotated = new HashSet<IPredicate>();

	// private final IPredicate m_TruePredicate;
	// private final IPredicate m_FalsePredicate;
	private final AutomatonEpimorphism<IPredicate> m_Epimorphism;
	private final IHoareTripleChecker m_Htc;
	private final ModifiableGlobalVariableManager m_ModifiedGlobals;
	private final INTERPOLATION m_Interpolation;

	private final TotalInterpolationBenchmarkGenerator m_BenchmarkGenerator = new TotalInterpolationBenchmarkGenerator();
	private final IUltimateServiceProvider mServices;

	public TotalInterpolationAutomatonBuilder(INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			ArrayList<IPredicate> stateSequence, IInterpolantGenerator interpolantGenerator, SmtManager smtManager,
			PredicateFactory predicateFactory, ModifiableGlobalVariableManager modifiableGlobals,
			INTERPOLATION interpolation, IUltimateServiceProvider services, HoareTripleChecks hoareTripleChecks) throws OperationCanceledException {
		super();
		mServices = services;
		m_StateSequence = stateSequence;
		// m_TraceChecker = traceChecker;
		m_SmtManager = smtManager;
		// m_Interpolants = traceChecker.getInterpolants();
		m_PredicateUnifier = interpolantGenerator.getPredicateUnifier();
		m_Abstraction = abstraction;
		InCaReAlphabet<CodeBlock> alphabet = new InCaReAlphabet<CodeBlock>(abstraction);
		m_IA = (new StraightLineInterpolantAutomatonBuilder(mServices, alphabet, interpolantGenerator, predicateFactory)).getResult();
		m_ModifiedGlobals = modifiableGlobals;
		m_Interpolation = interpolation;
		m_Epimorphism = new AutomatonEpimorphism<IPredicate>(mServices);
		{
			IPredicate firstAutomatonState = m_StateSequence.get(0);
			m_Epimorphism.insert(firstAutomatonState, interpolantGenerator.getPrecondition());
			m_Annotated.add(firstAutomatonState);
			m_Worklist.add(firstAutomatonState);
		}
		addInterpolants(m_StateSequence, interpolantGenerator.getInterpolants());
		{
			IPredicate lastAutomatonState = m_StateSequence.get(m_StateSequence.size() - 1);
			m_Epimorphism.insert(lastAutomatonState, interpolantGenerator.getPostcondition());
			m_Annotated.add(lastAutomatonState);
			m_Worklist.add(lastAutomatonState);
		}
		m_Htc = BasicCegarLoop.getEfficientHoareTripleChecker(HoareTripleChecks.MONOLITHIC, 
				m_SmtManager, m_ModifiedGlobals, m_PredicateUnifier);
		for (IPredicate state : stateSequence) {
			m_Worklist.add(state);
			m_Annotated.add(state);
		}
		while (!m_Worklist.isEmpty()) {
			IPredicate p = m_Worklist.removeFirst();
			doThings(p);
		}
		m_BenchmarkGenerator.addEdgeCheckerData(m_Htc.getEdgeCheckerBenchmark());
	}

	private void doThings(IPredicate p) throws OperationCanceledException {
		for (OutgoingInternalTransition<CodeBlock, IPredicate> transition : m_Abstraction.internalSuccessors(p)) {
			continueCheckForOutgoingPath(p, transition, transition.getSucc());
		}
		for (OutgoingCallTransition<CodeBlock, IPredicate> transition : m_Abstraction.callSuccessors(p)) {
			continueCheckForOutgoingPath(p, transition, transition.getSucc());
		}
		for (OutgoingReturnTransition<CodeBlock, IPredicate> transition : m_Abstraction.returnSuccessors(p)) {
			if (m_Annotated.contains(transition.getHierPred())) {
				continueCheckForOutgoingPath(p, transition, transition.getSucc());
			}
		}

	}

	private void continueCheckForOutgoingPath(IPredicate p, Transitionlet<CodeBlock, IPredicate> transition,
			IPredicate succ) throws OperationCanceledException {
		if (m_Annotated.contains(succ)) {
			IPredicate predItp = m_Epimorphism.getMapping(p);
			IPredicate succItp = m_Epimorphism.getMapping(succ);
			// this is a one-step path, no need to call TraceChecker
			if (interpolantAutomatonContainsTransition(predItp, transition, succItp)) {
				// do nothing, transition is already contained
			} else {
				m_BenchmarkGenerator.incrementPathLenght1();
				checkRunOfLenthOne(predItp, transition, succItp);
			}
		} else {
			m_BenchmarkGenerator.incrementRunSearches();
			NestedRun<CodeBlock, IPredicate> runStartingInSucc = findRun(succ, m_Annotated);
			if (runStartingInSucc != null) {
				NestedRun<CodeBlock, IPredicate> firstStep = constructRunOfLengthOne(p, transition);
				NestedRun<CodeBlock, IPredicate> completeRun = firstStep.concatenate(runStartingInSucc);
				checkRun(completeRun);
			}
		}

	}

	private boolean interpolantAutomatonContainsTransition(IPredicate predItp,
			Transitionlet<CodeBlock, IPredicate> transition, IPredicate succItp) {
		if (transition instanceof OutgoingInternalTransition) {
			OutgoingInternalTransition<CodeBlock, IPredicate> internalTrans = (OutgoingInternalTransition<CodeBlock, IPredicate>) transition;
			return m_IA.succInternal(predItp, internalTrans.getLetter()).contains(succItp);
		} else if (transition instanceof OutgoingCallTransition) {
			OutgoingCallTransition<CodeBlock, IPredicate> callTrans = (OutgoingCallTransition<CodeBlock, IPredicate>) transition;
			return m_IA.succCall(predItp, callTrans.getLetter()).contains(succItp);
		} else if (transition instanceof OutgoingReturnTransition) {
			OutgoingReturnTransition<CodeBlock, IPredicate> returnTrans = (OutgoingReturnTransition<CodeBlock, IPredicate>) transition;
			IPredicate hierPredItp = m_Epimorphism.getMapping(returnTrans.getHierPred());
			return m_IA.succReturn(predItp, hierPredItp, returnTrans.getLetter()).contains(succItp);
		} else if (transition instanceof SummaryReturnTransition) {
			SummaryReturnTransition<CodeBlock, IPredicate> summaryTrans = (SummaryReturnTransition<CodeBlock, IPredicate>) transition;
			IPredicate linPredItp = m_Epimorphism.getMapping(summaryTrans.getLinPred());
			return m_IA.succReturn(linPredItp, predItp, summaryTrans.getLetter()).contains(succItp);
		} else {
			throw new AssertionError("unsupported" + transition.getClass());
		}
	}

	private NestedRun<CodeBlock, IPredicate> constructRunOfLengthOne(IPredicate p,
			Transitionlet<CodeBlock, IPredicate> transition) {
		if (transition instanceof OutgoingInternalTransition) {
			OutgoingInternalTransition<CodeBlock, IPredicate> internalTrans = (OutgoingInternalTransition<CodeBlock, IPredicate>) transition;
			return new NestedRun<>(p, internalTrans.getLetter(), NestedWord.INTERNAL_POSITION, internalTrans.getSucc());
		} else if (transition instanceof OutgoingCallTransition) {
			OutgoingCallTransition<CodeBlock, IPredicate> callTrans = (OutgoingCallTransition<CodeBlock, IPredicate>) transition;
			return new NestedRun<>(p, callTrans.getLetter(), NestedWord.PLUS_INFINITY, callTrans.getSucc());
		} else if (transition instanceof OutgoingReturnTransition) {
			OutgoingReturnTransition<CodeBlock, IPredicate> returnTrans = (OutgoingReturnTransition<CodeBlock, IPredicate>) transition;
			return new NestedRun<>(p, returnTrans.getLetter(), NestedWord.MINUS_INFINITY, returnTrans.getSucc());
		} else if (transition instanceof SummaryReturnTransition) {
			SummaryReturnTransition<CodeBlock, IPredicate> summaryTrans = (SummaryReturnTransition<CodeBlock, IPredicate>) transition;
			return new NestedRun<>(summaryTrans.getLinPred(), summaryTrans.getLetter(), NestedWord.MINUS_INFINITY,
					summaryTrans.getSucc());
		} else {
			throw new AssertionError("unsupported" + transition.getClass());
		}

	}

	private void checkRunOfLenthOne(IPredicate predItp, Transitionlet<CodeBlock, IPredicate> transition,
			IPredicate succItp) {
		if (transition instanceof OutgoingInternalTransition) {
			OutgoingInternalTransition<CodeBlock, IPredicate> internalTrans = (OutgoingInternalTransition<CodeBlock, IPredicate>) transition;
			Validity validity = m_Htc.checkInternal(predItp, transition.getLetter(), succItp);
			if (validity == Validity.VALID) {
				m_IA.addInternalTransition(predItp, internalTrans.getLetter(), succItp);
			}
		} else if (transition instanceof OutgoingCallTransition) {
			OutgoingCallTransition<CodeBlock, IPredicate> callTrans = (OutgoingCallTransition<CodeBlock, IPredicate>) transition;
			Validity validity = m_Htc.checkCall(predItp, callTrans.getLetter(), succItp);
			if (validity == Validity.VALID) {
				m_IA.addCallTransition(predItp, callTrans.getLetter(), succItp);
			}
		} else if (transition instanceof OutgoingReturnTransition) {
			OutgoingReturnTransition<CodeBlock, IPredicate> returnTrans = (OutgoingReturnTransition<CodeBlock, IPredicate>) transition;
			IPredicate hierPredItp = m_Epimorphism.getMapping(returnTrans.getHierPred());
			Validity validity = m_Htc.checkReturn(predItp, hierPredItp, returnTrans.getLetter(), succItp);
			if (validity == Validity.VALID) {
				m_IA.addReturnTransition(predItp, hierPredItp, returnTrans.getLetter(), succItp);
			}
		} else if (transition instanceof SummaryReturnTransition) {
			SummaryReturnTransition<CodeBlock, IPredicate> summaryTrans = (SummaryReturnTransition<CodeBlock, IPredicate>) transition;
			IPredicate linPredItp = m_Epimorphism.getMapping(summaryTrans.getLinPred());
			Validity validity = m_Htc.checkReturn(linPredItp, predItp, summaryTrans.getLetter(), succItp);
			if (validity == Validity.VALID) {
				m_IA.addReturnTransition(linPredItp, predItp, summaryTrans.getLetter(), succItp);
			}
		} else {
			throw new AssertionError("unsupported" + transition.getClass());
		}
	}

	private void caseDistinction(IPredicate p, Transitionlet<CodeBlock, IPredicate> transition, IPredicate succ) {
		if (transition instanceof OutgoingInternalTransition) {
			OutgoingInternalTransition<CodeBlock, IPredicate> internalTrans = (OutgoingInternalTransition<CodeBlock, IPredicate>) transition;
		} else if (transition instanceof OutgoingCallTransition) {
			OutgoingCallTransition<CodeBlock, IPredicate> callTrans = (OutgoingCallTransition<CodeBlock, IPredicate>) transition;
		} else if (transition instanceof OutgoingReturnTransition) {
			OutgoingReturnTransition<CodeBlock, IPredicate> returnTrans = (OutgoingReturnTransition<CodeBlock, IPredicate>) transition;
		} else if (transition instanceof SummaryReturnTransition) {
			SummaryReturnTransition<CodeBlock, IPredicate> summaryTrans = (SummaryReturnTransition<CodeBlock, IPredicate>) transition;
		} else {
			throw new AssertionError("unsupported" + transition.getClass());
		}

	}

	private void checkRun(NestedRun<CodeBlock, IPredicate> run) {
		IPredicate first = run.getStateAtPosition(0);
		IPredicate last = run.getStateAtPosition(run.getLength() - 1);
		IPredicate precondition = m_Epimorphism.getMapping(first);
		IPredicate postcondition = m_Epimorphism.getMapping(last);
		SortedMap<Integer, IPredicate> pendingContexts = computePendingContexts(run);
		// SortedMap<Integer, IPredicate> pendingContexts = new TreeMap<>();
		
		InterpolatingTraceChecker tc;
		switch (m_Interpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			tc = new InterpolatingTraceCheckerCraig(precondition, postcondition,
					pendingContexts, run.getWord(),
					m_SmtManager, m_ModifiedGlobals, AssertCodeBlockOrder.NOT_INCREMENTALLY,
					mServices, true, m_PredicateUnifier, m_Interpolation);
			break;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
			tc = new TraceCheckerSpWp(precondition, postcondition, pendingContexts,
					run.getWord(), m_SmtManager, m_ModifiedGlobals, 
					AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true,
					mServices, true, m_PredicateUnifier, m_Interpolation, m_SmtManager);
			
			break;
		case PathInvariants:
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		m_BenchmarkGenerator.addTraceCheckerData(tc.getTraceCheckerBenchmark());
		if (tc.getToolchainCancelledExpection() != null) {
			throw tc.getToolchainCancelledExpection();
		}
		if (tc.isCorrect() == LBool.UNSAT) {
			m_BenchmarkGenerator.incrementUsefullRunGeq2();
			int additionalInterpolants = addInterpolants(run.getStateSequence(), tc.getInterpolants());
			m_BenchmarkGenerator.reportAdditionalInterpolants(additionalInterpolants);
			addTransitions(run.getStateSequence(), tc);
		} else {
			m_BenchmarkGenerator.incrementUselessRunGeq2();
		}
	}

	private SortedMap<Integer, IPredicate> computePendingContexts(NestedRun<CodeBlock, IPredicate> run) {
		SortedMap<Integer, IPredicate> result = new TreeMap<>();
		for (int pendingReturnPos : run.getWord().getPendingReturns().keySet()) {
			IPredicate linPred = run.getStateAtPosition(pendingReturnPos);
			Iterable<IPredicate> hierPreds = m_Abstraction.hierPred(linPred, run.getSymbol(pendingReturnPos));
			IPredicate hierPred = getSomeAnnotatedState(hierPreds);
			if (hierPred == null) {
				throw new AssertionError("found nothing");
			} else {
				result.put(pendingReturnPos, m_Epimorphism.getMapping(hierPred));
			}
		}
		return result;
	}

	private IPredicate getSomeAnnotatedState(Iterable<IPredicate> states) {
		for (IPredicate state : states) {
			if (m_Annotated.contains(state)) {
				return state;
			}
		}
		return null;
	}

	private void addTransitions(ArrayList<IPredicate> stateSequence, InterpolatingTraceChecker tc) {
		InterpolantsPreconditionPostcondition ipp = new InterpolantsPreconditionPostcondition(tc);
		NestedWord<CodeBlock> nw = NestedWord.nestedWord(tc.getTrace());
		for (int i = 0; i < nw.length(); i++) {
			if (nw.isInternalPosition(i)) {
				m_IA.addInternalTransition(ipp.getInterpolant(i), nw.getSymbol(i), ipp.getInterpolant(i + 1));
			} else if (nw.isCallPosition(i)) {
				m_IA.addCallTransition(ipp.getInterpolant(i), nw.getSymbol(i), ipp.getInterpolant(i + 1));
			} else if (nw.isReturnPosition(i)) {
				IPredicate hierPred;
				if (nw.isPendingReturn(i)) {
					hierPred = tc.getPendingContexts().get(i);
				} else {
					int callPredPos = nw.getCallPosition(i);
					hierPred = ipp.getInterpolant(callPredPos);
				}
				m_IA.addReturnTransition(ipp.getInterpolant(i), hierPred, nw.getSymbol(i), ipp.getInterpolant(i + 1));
			} else {
				throw new AssertionError();
			}
		}
	}

	/**
	 * Add a sequence of interpolants itp_1,...,itp_{n-1} for a sequence of
	 * states s_0,...,s_n. For each i add itp_i to the interpolant automaton if
	 * not already contained add s_i to the worklist add s_i to the annotated
	 * states add (s_i, itp_i) to the epimorphism Return the number of
	 * (different) interpolants that have been in the automaton before.
	 */
	private int addInterpolants(ArrayList<IPredicate> stateSequence, IPredicate[] interpolants) {
		int numberOfNewPredicates = 0;
		for (int i = 0; i < interpolants.length; i++) {
			IPredicate state = stateSequence.get(i + 1);
			IPredicate interpolant = interpolants[i];
			if (!m_IA.getStates().contains(interpolant)) {
				m_IA.addState(false, false, interpolant);
				numberOfNewPredicates++;
			}
			m_Annotated.add(state);
			m_Epimorphism.insert(state, interpolant);
			m_Worklist.add(state);
		}
		return numberOfNewPredicates;
	}

	private NestedRun<CodeBlock, IPredicate> findRun(IPredicate p, Set<IPredicate> annotated)
			throws OperationCanceledException {
		return (new IsEmpty<CodeBlock, IPredicate>(mServices, m_Abstraction, Collections.singleton(p), m_Annotated))
				.getNestedRun();
	}

	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return m_IA;
	}

	// private void startDfs(IPredicate state,
	// OutgoingInternalTransition<CodeBlock, IPredicate> transition) {
	// new GraphDfs(null, state, transition);
	// }
	//
	//
	// private class GraphDfs {
	// private final Set<IPredicate> m_Goal;
	// private final Set<IPredicate> m_Visited = new HashSet<IPredicate>();
	// private final Stack<Iterator<?>> m_IteratorStack = new
	// Stack<Iterator<?>>();
	// private final Stack<Transitionlet<CodeBlock, IPredicate>>
	// m_TransitionStack = new Stack<Transitionlet<CodeBlock, IPredicate>>();
	// private final Stack<IPredicate> m_StateStack = new Stack<IPredicate>();
	// private final Stack<IPredicate> m_CallPredecessors = new
	// Stack<IPredicate>();
	//
	// IPredicate m_CurrentPred;
	// IPredicate m_CurrentSucc;
	// Iterator<Transitionlet<CodeBlock, IPredicate>> m_CurrentIterator;
	// Transitionlet<CodeBlock, IPredicate> m_CurrentTransition;
	//
	//
	//
	// public GraphDfs(Set<IPredicate> goal, IPredicate currentPred,
	// Transitionlet<CodeBlock, IPredicate> initialTransition) {
	// super();
	// m_Goal = goal;
	// m_CurrentPred = currentPred;
	// m_CurrentTransition = initialTransition;
	// m_CurrentIterator = null;
	// m_CurrentSucc = getSuccessor(initialTransition);
	// }
	//
	// private IPredicate getSuccessor(Transitionlet<CodeBlock, IPredicate>
	// transition) {
	// IPredicate result;
	// if (transition instanceof OutgoingInternalTransition) {
	// result = ((OutgoingInternalTransition<CodeBlock, IPredicate>)
	// transition).getSucc();
	// } else if (transition instanceof OutgoingCallTransition) {
	// result = ((OutgoingCallTransition<CodeBlock, IPredicate>)
	// transition).getSucc();
	// } else if (transition instanceof OutgoingReturnTransition) {
	// result = ((OutgoingReturnTransition<CodeBlock, IPredicate>)
	// transition).getSucc();
	// } else {
	// throw new AssertionError("unsupported" + transition.getClass());
	// }
	// return result;
	// }
	//
	// public void searchGoal() {
	// while (!m_Goal.contains(m_CurrentSucc)) {
	// m_Visited.add(m_CurrentSucc);
	// push();
	// getNextTransition();
	// while(m_CurrentTransition == null) {
	// if (getStackHeight() == 1) {
	// // we never iterate over the initial Iterator.
	// return;
	// }
	// pop();
	// getNextTransition();
	// }
	// m_CurrentSucc = getSuccessor(m_CurrentTransition);
	// }
	// }
	//
	// private int getStackHeight() {
	// assert allStacksHaveSameHeight();
	// return m_StateStack.size();
	// }
	//
	// private boolean allStacksHaveSameHeight() {
	// boolean result = (m_StateStack.size() == m_IteratorStack.size());
	// result &= (m_StateStack.size() == m_TransitionStack.size());
	// return result;
	// }
	//
	// private void push() {
	// assert allStacksHaveSameHeight();
	// m_TransitionStack.push(m_CurrentTransition);
	// m_IteratorStack.push(m_CurrentIterator);
	// m_StateStack.push(m_CurrentPred);
	// if (m_CurrentTransition instanceof OutgoingCallTransition) {
	// m_CallPredecessors.add(m_CurrentPred);
	// }
	// m_CurrentPred = m_CurrentSucc;
	// m_CurrentTransition = null;
	// m_CurrentIterator = null;
	// m_CurrentSucc = null;
	// }
	//
	// private void pop() {
	// assert allStacksHaveSameHeight();
	// m_CurrentSucc = m_CurrentPred;
	// m_CurrentPred = m_StateStack.pop();
	// if (m_CurrentTransition instanceof OutgoingCallTransition) {
	// IPredicate callPred = m_CallPredecessors.pop();
	// assert callPred == m_CurrentPred;
	// }
	// m_CurrentIterator = (Iterator<Transitionlet<CodeBlock, IPredicate>>)
	// m_IteratorStack.pop();
	// m_CurrentTransition = m_TransitionStack.pop();
	// }
	//
	// public void getNextTransition() {
	// if (m_CurrentIterator.hasNext()) {
	// m_CurrentTransition = m_CurrentIterator.next();
	// } else {
	// if (m_CurrentTransition instanceof OutgoingInternalTransition) {
	// switchIteratorInternalToCall();
	// //TODO: implement
	// }
	// }
	// if (m_CurrentTransition instanceof OutgoingInternalTransition) {
	// m_CurrentTransition = getNextInternalTransition();
	// if (m_CurrentTransition == null) {
	//
	// }
	// }
	//
	// }
	//
	// public void switchIteratorInternalToCall() {
	// assert !m_IteratorStack.peek().hasNext();
	// m_IteratorStack.pop();
	// IPredicate top = m_StateStack.peek();
	// Iterator<OutgoingCallTransition<CodeBlock, IPredicate>> it =
	// m_Abstraction.callSuccessors(top).iterator();
	// m_IteratorStack.push(it);
	// }
	//
	// public void switchIteratorCallToReturn() {
	// assert !m_IteratorStack.peek().hasNext();
	// m_IteratorStack.pop();
	// IPredicate top = m_StateStack.peek();
	// Iterator<OutgoingReturnTransition<CodeBlock, IPredicate>> it =
	// m_Abstraction.returnSuccessors(top).iterator();
	// m_IteratorStack.push(it);
	// }
	//
	// public OutgoingInternalTransition<CodeBlock, IPredicate>
	// getNextInternalTransition() {
	// if (m_IteratorStack.peek().hasNext()) {
	// return (OutgoingInternalTransition<CodeBlock, IPredicate>)
	// m_IteratorStack.peek().next();
	// } else {
	// return null;
	// }
	// }
	// }
	//

	public TotalInterpolationBenchmarkGenerator getTotalInterpolationBenchmark() {
		return m_BenchmarkGenerator;
	}

	public static class TotalInterpolationBenchmarkType implements IBenchmarkType {

		private static TotalInterpolationBenchmarkType s_Instance = new TotalInterpolationBenchmarkType();
		public final static String s_AdditionalInterpolants = "AdditionalInterpolants";
		public final static String s_PathLenght1 = "RunLenght1";
		public final static String s_RunSearches = "RunSearches";
		public final static String s_UsefullRunGeq2 = "UsefullRunGeq2";
		public final static String s_UselessRunGeq2 = "UselessRunGeq2";
		public final static String s_TraceCheckerBenchmarks = "TraceCheckerBenchmarks";
		public final static String s_EdgeCheckerBenchmarks = "EdgeCheckerBenchmarks";

		public static TotalInterpolationBenchmarkType getInstance() {
			return s_Instance;
		}

		@Override
		public Collection<String> getKeys() {
			return Arrays.asList(new String[] { s_AdditionalInterpolants, s_PathLenght1, s_RunSearches,
					s_UsefullRunGeq2, s_UselessRunGeq2, s_TraceCheckerBenchmarks, s_EdgeCheckerBenchmarks });
		}

		@Override
		public Object aggregate(String key, Object value1, Object value2) {
			switch (key) {
			case s_AdditionalInterpolants:
			case s_PathLenght1:
			case s_RunSearches:
			case s_UsefullRunGeq2:
			case s_UselessRunGeq2:
				return (int) value1 + (int) value2;
			case s_TraceCheckerBenchmarks:
			case s_EdgeCheckerBenchmarks:
				BenchmarkData bmData1 = (BenchmarkData) value1;
				BenchmarkData bmData2 = (BenchmarkData) value2;
				bmData1.aggregateBenchmarkData(bmData2);
				return bmData1;
			default:
				throw new AssertionError("unknown key");
			}
		}

		@Override
		public String prettyprintBenchmarkData(IBenchmarkDataProvider benchmarkData) {
			StringBuilder sb = new StringBuilder();

			for (String id : new String[] { s_AdditionalInterpolants, s_PathLenght1, s_RunSearches, s_UsefullRunGeq2,
					s_UselessRunGeq2 }) {
				int value = (int) benchmarkData.getValue(id);
				sb.append(id);
				sb.append(": ");
				sb.append(value);
				sb.append("  ");
			}

			sb.append(s_TraceCheckerBenchmarks);
			sb.append(": ");
			BenchmarkData ecData = (BenchmarkData) benchmarkData.getValue(s_TraceCheckerBenchmarks);
			sb.append(ecData);
			sb.append("  ");

			sb.append(s_EdgeCheckerBenchmarks);
			sb.append(": ");
			BenchmarkData tcData = (BenchmarkData) benchmarkData.getValue(s_EdgeCheckerBenchmarks);
			sb.append(tcData);
			return sb.toString();
		}

	}

	public static class TotalInterpolationBenchmarkGenerator implements IBenchmarkDataProvider {

		private int m_AdditionalInterpolants = 0;
		private int m_PathLenght1 = 0;
		private int m_RunSearches = 0;
		private int m_UsefullRunGeq2 = 0;
		private int m_UselessRunGeq2 = 0;
		private final BenchmarkData m_EcData = new BenchmarkData();
		private final BenchmarkData m_TcData = new BenchmarkData();

		public TotalInterpolationBenchmarkGenerator() {
		}

		@Override
		public Collection<String> getKeys() {
			return TotalInterpolationBenchmarkType.getInstance().getKeys();
		}

		public void reportAdditionalInterpolants(int additionalInterpolants) {
			m_AdditionalInterpolants += additionalInterpolants;
		}

		public void incrementPathLenght1() {
			m_PathLenght1++;
		}

		public void incrementRunSearches() {
			m_RunSearches++;
		}

		public void incrementUsefullRunGeq2() {
			m_UsefullRunGeq2++;
		}

		public void incrementUselessRunGeq2() {
			m_UselessRunGeq2++;
		}

		public void addEdgeCheckerData(IBenchmarkDataProvider ecbd) {
			m_EcData.aggregateBenchmarkData(ecbd);
		}

		public void addTraceCheckerData(IBenchmarkDataProvider tcbd) {
			m_TcData.aggregateBenchmarkData(tcbd);
		}

		public Object getValue(String key) {
			switch (key) {
			case TotalInterpolationBenchmarkType.s_AdditionalInterpolants:
				return m_AdditionalInterpolants;
			case TotalInterpolationBenchmarkType.s_PathLenght1:
				return m_PathLenght1;
			case TotalInterpolationBenchmarkType.s_RunSearches:
				return m_RunSearches;
			case TotalInterpolationBenchmarkType.s_UsefullRunGeq2:
				return m_UsefullRunGeq2;
			case TotalInterpolationBenchmarkType.s_UselessRunGeq2:
				return m_UselessRunGeq2;
			case TotalInterpolationBenchmarkType.s_TraceCheckerBenchmarks:
				return m_TcData;
			case TotalInterpolationBenchmarkType.s_EdgeCheckerBenchmarks:
				return m_EcData;
			default:
				throw new AssertionError("unknown key");
			}
		}

		@Override
		public IBenchmarkType getBenchmarkType() {
			return TotalInterpolationBenchmarkType.getInstance();
		}

	}

}
