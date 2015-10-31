/*
 * Copyright (C) 2015 Betim Musa (musab@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkGeneratorWithStopwatches;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkDataProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.IBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkGeneratorWithStopwatches.StopwatchStillRunningException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.HoareTripleCheckerBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker.AllIntegers;

/**
 * Interpolant Consolidation works as follows:
 * Requirements: 
 * 		(1) A path automaton for the given trace m_Trace.
 * 		(2) An interpolant automaton (finite automaton) for the given predicate annotation of the given trace m_Trace.
 * Procedure:
 * 		1. Compute the difference between the path automaton and the interpolant automaton.
 * 		2. If the difference is empty, then consolidate the interpolants as follows:
 * 		2.1 Compute a homomorphism for the states of the difference automaton.
 * 		2.2 Compute the annotation for a state p = {q_1, ..., q_k} where q_1 ... q_k are homomorphous to each other as follows:
 * 				Annot(p) = Annot(q_1) OR Annot(q_2) OR ... OR Annot(q_k)
 * 		3. If the difference is not empty, then... (TODO). This case is not yet implemented!
 * 
 * 
 * @author musab@informatik.uni-freiburg.de
 */
public class InterpolantConsolidation implements IInterpolantGenerator {
	private InterpolatingTraceChecker m_InterpolatingTraceChecker;
	private final IPredicate m_Precondition;
	private final IPredicate m_Postcondition;
	private final SortedMap<Integer, IPredicate> m_PendingContexts;
	private IPredicate[] m_ConsolidatedInterpolants;
	private TAPreferences m_TaPrefs;
	private final NestedWord<CodeBlock> m_Trace;
	private final IUltimateServiceProvider m_Services;
	private final SmtManager m_SmtManager;
	private final ModifiableGlobalVariableManager m_ModifiedGlobals;
	private final PredicateUnifier m_PredicateUnifier;
	private final Logger m_Logger;

	protected final InterpolantConsolidationBenchmarkGenerator m_InterpolantConsolidationBenchmarkGenerator;
	private boolean m_printDebugInformation = false;
	private boolean m_printAutomataOfDifference = false;
	private boolean m_InterpolantsConsolidationSuccessful = false;
	private boolean useConsolidationInNonEmptyCase = false;
	
	public InterpolantConsolidation(IPredicate precondition,
			IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			NestedWord<CodeBlock> trace, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals,
			IUltimateServiceProvider services,
			Logger logger, 
			PredicateUnifier predicateUnifier,
			InterpolatingTraceChecker tc,
			TAPreferences taPrefs) throws OperationCanceledException {
		m_Precondition = precondition;
		m_Postcondition = postcondition;
		m_PendingContexts = pendingContexts;
		m_Trace = trace;
		m_SmtManager = smtManager;
		m_ModifiedGlobals = modifiedGlobals;
		m_Services = services;
		m_Logger = logger;
		m_PredicateUnifier = predicateUnifier;
		m_InterpolatingTraceChecker = tc;
		m_ConsolidatedInterpolants = new IPredicate[m_Trace.length() - 1];
		m_TaPrefs = taPrefs;
		m_InterpolantConsolidationBenchmarkGenerator = new InterpolantConsolidationBenchmarkGenerator();

		if (m_InterpolatingTraceChecker.isCorrect() == LBool.UNSAT) {
			computeInterpolants(new AllIntegers());
		}
	}

	protected void computeInterpolants(Set<Integer> interpolatedPositions) throws OperationCanceledException {
		// Start the stopwatch to measure the time we need for interpolant consolidation
		m_InterpolantConsolidationBenchmarkGenerator.start(InterpolantConsolidationBenchmarkType.s_TimeOfConsolidation);
		
		// 1. Build the path automaton for the given trace m_Trace
		PathProgramAutomatonConstructor ppc = new PathProgramAutomatonConstructor();
		INestedWordAutomaton<CodeBlock, IPredicate> pathprogramautomaton = ppc.constructAutomatonFromGivenPath(m_Trace, m_Services, m_SmtManager, m_TaPrefs);
		
		
		IHoareTripleChecker htc = BasicCegarLoop.getEfficientHoareTripleChecker(TraceAbstractionPreferenceInitializer.HoareTripleChecks.INCREMENTAL, 
				m_SmtManager, m_ModifiedGlobals, m_PredicateUnifier);
		
		
		// 2. Build the finite automaton (former interpolant path automaton) for the given Floyd-Hoare annotation
		NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton = constructInterpolantAutomaton(m_Trace, m_SmtManager, m_TaPrefs, m_Services, m_InterpolatingTraceChecker); 
		// 3. Determinize the finite automaton from step 2.
		DeterministicInterpolantAutomaton interpolantAutomatonDeterminized = new DeterministicInterpolantAutomaton(
				m_Services, m_SmtManager, m_ModifiedGlobals, htc, pathprogramautomaton, interpolantAutomaton,
				m_PredicateUnifier, m_Logger, false ,// PREDICATE_ABSTRACTION_CONSERVATIVE = false (default) 
				false //PREDICATE_ABSTRACTION_CANNIBALIZE = false  (default) 
				); 
		
		 
		PredicateFactoryForInterpolantConsolidation pfconsol = new PredicateFactoryForInterpolantConsolidation(m_SmtManager, m_TaPrefs);
		
		PredicateFactory predicateFactoryInterpolantAutomata = new PredicateFactory(m_SmtManager, m_TaPrefs);
		
		PowersetDeterminizer<CodeBlock, IPredicate> psd2 = new PowersetDeterminizer<CodeBlock, IPredicate>(
				interpolantAutomatonDeterminized, true, predicateFactoryInterpolantAutomata);
		

		try {
			// 4. Compute the difference between the path automaton and the determinized
			//    finite automaton (from step 3)
			Difference<CodeBlock, IPredicate> diff = new Difference<CodeBlock, IPredicate>(m_Services,
					(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) pathprogramautomaton,
					interpolantAutomatonDeterminized, psd2,
					pfconsol /* PredicateFactory for Refinement */, false /*explointSigmaStarConcatOfIA*/ );
			if (m_printAutomataOfDifference) {
				AutomatonDefinitionPrinter<CodeBlock, IPredicate> pathAutomatonPrinter = new AutomatonDefinitionPrinter<>(m_Services, "PathAutomaton", Format.ATS, pathprogramautomaton);
				AutomatonDefinitionPrinter<CodeBlock, IPredicate> interpolantAutomatonPrinter = new AutomatonDefinitionPrinter<>(m_Services, "InterpolantAutomatonNonDet", Format.ATS, interpolantAutomaton);
				AutomatonDefinitionPrinter<CodeBlock, IPredicate> interpolantAutomatonPrinterDet = new AutomatonDefinitionPrinter<>(m_Services, "InterpolantAutomatonDet", Format.ATS, interpolantAutomatonDeterminized);
				INestedWordAutomatonOldApi<CodeBlock, IPredicate> diffAutomaton = diff.getResult();
				AutomatonDefinitionPrinter<CodeBlock, IPredicate> diffAutomatonPrinter = new AutomatonDefinitionPrinter<>(m_Services, "DifferenceAutomaton", Format.ATS, diffAutomaton);
				m_Logger.debug(pathAutomatonPrinter.getDefinitionAsString());
				m_Logger.debug(interpolantAutomatonPrinter.getDefinitionAsString());
				m_Logger.debug(interpolantAutomatonPrinterDet.getDefinitionAsString());
				m_Logger.debug(diffAutomatonPrinter.getDefinitionAsString());
			}
			htc.releaseLock();
			// 5. Check if difference is empty
			IsEmpty<CodeBlock, IPredicate> empty = new IsEmpty<CodeBlock, IPredicate>(m_Services, diff.getResult());
			if (!empty.getResult()) {

				Set<IPredicate> badStates = getDiffAutomatonBadStates(diff.getResult());
				pfconsol.removeBadPredicates(badStates);
				if (!useConsolidationInNonEmptyCase) {
					m_ConsolidatedInterpolants = m_InterpolatingTraceChecker.getInterpolants();
					// Stop the time for interpolant consolidation
					m_InterpolantConsolidationBenchmarkGenerator.stop(InterpolantConsolidationBenchmarkType.s_TimeOfConsolidation);
					return;
				}
				
			}
			
		} catch (AutomataLibraryException e) {
			if (e instanceof OperationCanceledException) {
				m_Logger.info("Timeout while computing interpolants");
			}
			throw ((OperationCanceledException)e);
		}

		// 6. Interpolant Consolidation step
		List<IPredicate> pathPositionsToLocations = ppc.getPositionsToStates();
		Map<IPredicate, Set<IPredicate>> locationsToSetOfPredicates = pfconsol.getLocationsToSetOfPredicates();
		
		Set<IPredicate> interpolantsBeforeConsolidation = interpolantAutomaton.getStates();
		Set<IPredicate> interpolantsAfterConsolidation = new HashSet<IPredicate>();

		m_InterpolantConsolidationBenchmarkGenerator.incrementDiffAutomatonEmpty_Counter();
		
		m_ConsolidatedInterpolants = new IPredicate[m_Trace.length() - 1];
		
		computeConsolidatedInterpolants(pathPositionsToLocations, locationsToSetOfPredicates, interpolantsBeforeConsolidation, 
				interpolantsAfterConsolidation, htc);
		
		assert TraceCheckerUtils.checkInterpolantsInductivityForward(m_ConsolidatedInterpolants, 
				m_Trace, m_Precondition, m_Postcondition, m_PendingContexts, "CP", 
				m_SmtManager, m_ModifiedGlobals, m_Logger) : "invalid Hoare triple in consolidated interpolants";
		m_InterpolantsConsolidationSuccessful = true;
		
		if (m_printDebugInformation ) {
			m_Logger.debug("Interpolants before consolidation:");
			printArray(interpolantAutomaton.getStates().toArray(new IPredicate[interpolantAutomaton.getStates().size()]));
			m_Logger.debug("Interpolants after consolidation:");
			printArray(interpolantsAfterConsolidation.toArray(new IPredicate[interpolantsAfterConsolidation.size()]));
		}
	
	}
	
	
	private Set<IPredicate> getDiffAutomatonBadStates(INestedWordAutomaton<CodeBlock, IPredicate> diffAutomaton) {
		LinkedList<IPredicate> successors = new LinkedList<IPredicate>();
		Set<IPredicate> badStates = new HashSet<IPredicate>();
		Set<IPredicate> allSuccessors = new HashSet<IPredicate>();
		successors.addAll(diffAutomaton.getFinalStates());
		allSuccessors.addAll(diffAutomaton.getFinalStates());
		badStates.addAll(diffAutomaton.getFinalStates());
		
		while(!successors.isEmpty()) {
			IPredicate currentState = successors.removeFirst();
			Set<IPredicate> predecessors = getPredecessorsOfState(diffAutomaton, currentState);
			for (IPredicate p : predecessors) {
				if (!diffAutomaton.isInitial(p) && !p.equals(currentState)) {
					Set<IPredicate> successorsOfP = getSuccessors(diffAutomaton, p);
					if (allSuccessors.containsAll(successorsOfP)) {
						badStates.add(p);
						successors.addLast(p);
						allSuccessors.add(p);
					}
				}
			}
		}
		return badStates;
	}
	
	private Set<IPredicate> getSuccessors(INestedWordAutomaton<CodeBlock, IPredicate> diffAutomaton, IPredicate p) {
		Set<IPredicate> successors = new HashSet<IPredicate>();
		for (OutgoingInternalTransition<CodeBlock, IPredicate> it: diffAutomaton.internalSuccessors(p)) {
			successors.add(it.getSucc());
		}
		
		for (OutgoingCallTransition<CodeBlock, IPredicate> ict: diffAutomaton.callSuccessors(p)) {
			successors.add(ict.getSucc());
		}
		
		for (OutgoingReturnTransition<CodeBlock, IPredicate> irt: diffAutomaton.returnSuccessors(p)) {
			successors.add(irt.getSucc());
		}
		return successors;
	}

	private Set<IPredicate> getPredecessorsOfState(INestedWordAutomaton<CodeBlock, IPredicate> diffAutomaton,
			IPredicate currentState) {
		Set<IPredicate> preds = new HashSet<IPredicate>();
		for (IncomingInternalTransition<CodeBlock, IPredicate> it: diffAutomaton.internalPredecessors(currentState)) {
			preds.add(it.getPred());
		}
		for (IncomingCallTransition<CodeBlock, IPredicate> ict: diffAutomaton.callPredecessors(currentState)) {
			preds.add(ict.getPred());
		}
		for (IncomingReturnTransition<CodeBlock, IPredicate> irt: diffAutomaton.returnPredecessors(currentState)) {
			preds.add(irt.getLinPred());
		}
		return preds;
	}

	private void computeConsolidatedInterpolants(List<IPredicate> pathPositionsToLocations, 
			Map<IPredicate, Set<IPredicate>> locationsToSetOfPredicates, Set<IPredicate> interpolantsBeforeConsolidation, 
			Set<IPredicate> interpolantsAfterConsolidation, IHoareTripleChecker htc) {
		Map<IPredicate, IPredicate> locationsToConsolidatedInterpolants = new HashMap<>();
		
		int disjunctionsGreaterOneCounter = 0;
		int newlyCreatedInterpolants = 0;
		// Init it with max. number of interpolants and decrement it every time you encounter an interpolant that
		// has existed before consolidation.
		int interpolantsDropped = m_Trace.length() - 1; 
		for (int i = 0; i < m_ConsolidatedInterpolants.length; i++) {
			IPredicate loc = pathPositionsToLocations.get(i+1);
			if (!locationsToConsolidatedInterpolants.containsKey(loc)) {
				// Compute the disjunction of the predicates for location i
				Set<IPredicate> predicatesForThisLocation = locationsToSetOfPredicates.get(loc);
				
				
				assert (predicatesForThisLocation != null) : "The set of predicates for the current location is null!";
				
				IPredicate[] predicatesForThisLocationAsArray = predicatesForThisLocation.toArray(new IPredicate[predicatesForThisLocation.size()]);

				if (predicatesForThisLocation.size() > 1) {
					
					// Case: consolidation is successful. We have at least 2 predicates which are connected by disjunction.
					// Update benchmarks
					disjunctionsGreaterOneCounter++;
					
					TermVarsProc predicatesForThisLocationConsolidated = m_SmtManager.or(predicatesForThisLocationAsArray);
					// Store the consolidated (the disjunction of the predicates for the current location)
					m_ConsolidatedInterpolants[i] = m_PredicateUnifier.getOrConstructPredicate(predicatesForThisLocationConsolidated);
					
					if (!interpolantsBeforeConsolidation.contains(m_ConsolidatedInterpolants[i])) {
						
						// If the consolidated interpolant is not contained in the interpolants before consolidation, then
						// the consolidated interpolant is new.
						newlyCreatedInterpolants++;
					}
					
				} else {
					m_ConsolidatedInterpolants[i] = predicatesForThisLocationAsArray[0];
				}
				if (interpolantsBeforeConsolidation.contains(m_ConsolidatedInterpolants[i]))  {
					// If current interpolant is contained in the interpolants before consolidation, then the number of
					// interpolants dropped decreases.
					interpolantsDropped--;
				}
				interpolantsAfterConsolidation.add(m_ConsolidatedInterpolants[i]);
				locationsToConsolidatedInterpolants.put(loc, m_ConsolidatedInterpolants[i]);
			} else {
				m_ConsolidatedInterpolants[i] = locationsToConsolidatedInterpolants.get(loc);
			}
			
		}
		int differenceOfInterpolantsBeforeAfter = interpolantsBeforeConsolidation.size() - interpolantsAfterConsolidation.size();
		m_InterpolantConsolidationBenchmarkGenerator.setInterpolantConsolidationData(disjunctionsGreaterOneCounter, newlyCreatedInterpolants, interpolantsDropped, differenceOfInterpolantsBeforeAfter,
				 htc.getEdgeCheckerBenchmark());
		// Stop the time for interpolant consolidation
		m_InterpolantConsolidationBenchmarkGenerator.stop(InterpolantConsolidationBenchmarkType.s_TimeOfConsolidation);
	}
	
	private void printArray(IPredicate[] interpolants) {
		for (int i = 0; i < interpolants.length; i++) {
			m_Logger.debug(Integer.toString(i) + ". " + interpolants[i].toString());
		}
		
	}

	public IPredicate[] getInterpolantsOfType_I() {
		if (m_InterpolatingTraceChecker instanceof TraceCheckerSpWp) {
			TraceCheckerSpWp tcspwp = (TraceCheckerSpWp) m_InterpolatingTraceChecker;
			if (tcspwp.forwardsPredicatesComputed()) {
				return tcspwp.getForwardPredicates();
			} else {
				return tcspwp.getInterpolants();
			}
		} else {
			return m_InterpolatingTraceChecker.getInterpolants();
		}
	}
	
	public IPredicate[] getInterpolantsOfType_II() {
		if (m_InterpolatingTraceChecker instanceof TraceCheckerSpWp) {
			TraceCheckerSpWp tcspwp = (TraceCheckerSpWp) m_InterpolatingTraceChecker;
			if (tcspwp.backwardsPredicatesComputed()) {
				return tcspwp.getBackwardPredicates();
			} else {
				return tcspwp.getInterpolants();
			}
		} else {
			return m_InterpolatingTraceChecker.getInterpolants();
		}
	}
	
	public boolean consolidationSuccessful() {
		return m_InterpolantsConsolidationSuccessful;
	}
	
	/**
	 * Construct a finite automaton for the given Floyd-Hoare annotation.
	 * @param trace - the trace from which the automaton is constructed.
	 * @param traceChecker - contains the Floyd-Hoare annotation (the interpolants) for which the automaton is constructed.
	 * @return
	 */
	private NestedWordAutomaton<CodeBlock, IPredicate> constructInterpolantAutomaton(NestedWord<CodeBlock> trace, SmtManager smtManager, TAPreferences taPrefs, 
			IUltimateServiceProvider services, InterpolatingTraceChecker traceChecker) {
		// Set the alphabet
		Set<CodeBlock> internalAlphabet = new HashSet<CodeBlock>();
		Set<CodeBlock> callAlphabet = new HashSet<CodeBlock>();
		Set<CodeBlock> returnAlphabet = new HashSet<CodeBlock>();
		for (int i = 0; i < trace.length(); i++) {
			if (trace.isInternalPosition(i)) {
				internalAlphabet.add(trace.getSymbol(i));
			} else if (trace.isCallPosition(i)) {
				callAlphabet.add(trace.getSymbol(i));
			} else if (trace.isReturnPosition(i)) {
				returnAlphabet.add(trace.getSymbol(i));
			} else {
				throw new UnsupportedOperationException("Symbol at position " + i + " is neither internal, call, nor return symbol!");
			}
		}
		
		
		
		StateFactory<IPredicate> predicateFactory = new PredicateFactory(smtManager, taPrefs);
		
		NestedWordAutomaton<CodeBlock, IPredicate> nwa  = new NestedWordAutomaton<CodeBlock, IPredicate>(   services, 
																											internalAlphabet,
																											callAlphabet,
																											returnAlphabet,
																											predicateFactory);
		// Set the initial and the final state of the automaton
		nwa.addState(true, false, traceChecker.getPrecondition());
		nwa.addState(false, true, traceChecker.getPostcondition());
		boolean nwaStatesAndTransitionsAdded = false;
		
		if (traceChecker instanceof TraceCheckerSpWp) {
			TraceCheckerSpWp tcSpWp = (TraceCheckerSpWp) traceChecker;
			if (tcSpWp.forwardsPredicatesComputed() && tcSpWp.backwardsPredicatesComputed()) {
				nwaStatesAndTransitionsAdded = true;
				// Add states and transitions corresponding to forwards predicates
				addStatesAndCorrespondingTransitionsFromGivenInterpolants(nwa, traceChecker.getPrecondition(), 
						traceChecker.getPostcondition(), tcSpWp.getForwardPredicates(), trace);
				// Add states and transitions corresponding to backwards predicates
				addStatesAndCorrespondingTransitionsFromGivenInterpolants(nwa, traceChecker.getPrecondition(), 
						traceChecker.getPostcondition(), tcSpWp.getBackwardPredicates(), trace);
			}
		}
		
		if (!nwaStatesAndTransitionsAdded) {
			addStatesAndCorrespondingTransitionsFromGivenInterpolants(nwa, traceChecker.getPrecondition(), 
					traceChecker.getPostcondition(), traceChecker.getInterpolants(), trace);
		}
		return nwa;
	}
	
	public IPredicate getInterpolantAtPosition(int i, IPredicate precondition, IPredicate postcondition, IPredicate[] interpolants) {
		if (i < 0) {
			throw new AssertionError("index beyond precondition");
		} else if (i == 0) {
			return precondition;
		} else if (i <= interpolants.length) {
			return interpolants[i-1];
		} else if (i == interpolants.length+1) {
			return postcondition;
		} else {
			throw new AssertionError("index beyond postcondition");
		}
	}

	private void addStatesAndCorrespondingTransitionsFromGivenInterpolants(
			NestedWordAutomaton<CodeBlock, IPredicate> nwa,
			IPredicate precondition, IPredicate postcondition,
			IPredicate[] interpolants, NestedWord<CodeBlock> trace) {
		for (int i=0; i<trace.length(); i++) {
			IPredicate pred = getInterpolantAtPosition(i, precondition, postcondition, interpolants);
			IPredicate succ = getInterpolantAtPosition(i+1, precondition, postcondition, interpolants);
			
			assert nwa.getStates().contains(pred);
			if (!nwa.getStates().contains(succ)) {
				nwa.addState(false, false, succ);
			}
			if (trace.isCallPosition(i)) {
				nwa.addCallTransition(pred, trace.getSymbol(i), succ);
			} else if (trace.isReturnPosition(i)) {
				assert !trace.isPendingReturn(i);
				int callPos = trace.getCallPosition(i);
				IPredicate hierPred = getInterpolantAtPosition(callPos, precondition, postcondition, interpolants);
				nwa.addReturnTransition(pred, hierPred, trace.getSymbol(i), succ);
			} else {
				assert trace.isInternalPosition(i);
				nwa.addInternalTransition(pred, trace.getSymbol(i), succ);
			}
		}
	}

	@Override
	public IPredicate[] getInterpolants() {
		return m_ConsolidatedInterpolants;
	}

	@Override
	public Word<CodeBlock> getTrace() {
		return m_Trace;
	}

	@Override
	public IPredicate getPrecondition() {
		return m_Precondition;
	}

	@Override
	public IPredicate getPostcondition() {
		return m_Postcondition;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return m_PendingContexts;
	}
	
	public InterpolatingTraceChecker getInterpolatingTraceChecker() {
		return m_InterpolatingTraceChecker;
	}
	
	@Override
	public PredicateUnifier getPredicateUnifier() {
		return m_PredicateUnifier;
	}

	public InterpolantConsolidationBenchmarkGenerator getInterpolantConsolidationBenchmarks() {
		return m_InterpolantConsolidationBenchmarkGenerator;
	}
	
	// Benchmarks Section
	public static class InterpolantConsolidationBenchmarkType implements IBenchmarkType {
		private static InterpolantConsolidationBenchmarkType s_Instance = new InterpolantConsolidationBenchmarkType();

	
		
		/* Keys */
		// Counts how often the difference automaton has been empty
		protected final static String s_DifferenceAutomatonEmptyCounter = "DifferenceAutomatonEmptyCounter";
//		protected final static String s_SumOfPredicatesConsolidated = "SumOfPredicatesConsolidated";
		
		protected final static String s_DisjunctionsGreaterOneCounter = "DisjunctionsGreaterOneCounter";
		
//		protected final static String s_SumOfInterpolantsBefore = "SumOfInterpolantsBefore";
//		protected final static String s_SumOfInterpolantsAfterConsoli = "SumOfInterpolantsAfterConsoli";
		protected final static String s_NewlyCreatedInterpolants = "NewlyCreatedInterpolants";
		
		protected final static String s_InterpolantsDropped = "InterpolantsDropped";
		
		protected final static String s_DifferenceBeforeAfter = "DifferenceOfInterpolantsBeforeAfter";
		
		protected final static String s_NumberOfHoareTripleChecks = "NumOfHoareTripleChecks";
		
		protected final static String s_TimeOfConsolidation = "TimeOfConsolidation";
		
		
		public static InterpolantConsolidationBenchmarkType getInstance() {
			return s_Instance;
		}
		
		@Override
		public Collection<String> getKeys() {
			ArrayList<String> result = new ArrayList<String>();
			result.add(s_DisjunctionsGreaterOneCounter);
			result.add(s_DifferenceBeforeAfter);
			result.add(s_NumberOfHoareTripleChecks);
			result.add(s_TimeOfConsolidation);
			result.add(s_NewlyCreatedInterpolants);
			result.add(s_InterpolantsDropped);
			result.add(s_DifferenceAutomatonEmptyCounter);
			return result;
		}

		@Override
		public Object aggregate(String key, Object value1, Object value2) {
			switch(key) {
			case s_NewlyCreatedInterpolants:
			case s_InterpolantsDropped:
			case s_DifferenceBeforeAfter:
			case s_DifferenceAutomatonEmptyCounter:
			case s_DisjunctionsGreaterOneCounter: {
				int result = ((int) value1) + ((int) value2);
				return result;
			}
			case s_TimeOfConsolidation:
			{
				long result = ((long) value1) + ((long) value2);
				return result;
			}
			case s_NumberOfHoareTripleChecks:
				InCaReCounter counter1 = (InCaReCounter) value1;
				counter1.add((InCaReCounter) value2);
				return counter1;
			default:
				throw new AssertionError("unknown key");
			}
		}

		@Override
		public String prettyprintBenchmarkData(
				IBenchmarkDataProvider benchmarkData) {
			StringBuilder sb = new StringBuilder();
			
			sb.append("\t").append(s_DifferenceAutomatonEmptyCounter).append(": ");
			sb.append((int)benchmarkData.getValue(s_DifferenceAutomatonEmptyCounter));
			
			sb.append("\t").append(s_DisjunctionsGreaterOneCounter).append(": ");
			sb.append((int) benchmarkData.getValue(s_DisjunctionsGreaterOneCounter));
			
			sb.append("\t").append(s_NumberOfHoareTripleChecks).append(": ");
			sb.append((InCaReCounter)benchmarkData.getValue(s_NumberOfHoareTripleChecks));
			
			sb.append("\t").append(s_InterpolantsDropped).append(": ");
			sb.append((int) benchmarkData.getValue(s_InterpolantsDropped));
			
			sb.append("\t").append(s_NewlyCreatedInterpolants).append(": ");
			sb.append((int) benchmarkData.getValue(s_NewlyCreatedInterpolants));
			
			sb.append("\t").append(s_DifferenceBeforeAfter).append(": ");
			sb.append((int) benchmarkData.getValue(s_DifferenceBeforeAfter));
			
			sb.append("\t").append(s_TimeOfConsolidation).append(": ");
			Long timeOfInterpolantConsolidation =  (Long) benchmarkData.getValue(s_TimeOfConsolidation);
			sb.append(CegarLoopBenchmarkType.prettyprintNanoseconds(timeOfInterpolantConsolidation));
			return sb.toString();
		}
		
	}
	
	public class InterpolantConsolidationBenchmarkGenerator extends BenchmarkGeneratorWithStopwatches implements 	IBenchmarkDataProvider {
		private int m_DisjunctionsGreaterOneCounter = 0;
		private int m_DifferenceBeforeAfter = 0;
		private int m_NewlyCreatedInterpolants = 0;
		private int m_InterpolantsDropped = 0;
		// Contains the number of hoare triple checks (i.e. num of sats + num of unsats + num of unknowns)
		// that are made by the interpolant consolidation
		private InCaReCounter m_NumOfHoareTripleChecks = new InCaReCounter();
		private int m_DiffAutomatonEmpty_Counter = 0;
		
		
		
		public void setInterpolantConsolidationData(int disjunctionsGreaterOneCounter, int newlyCreatedInterpolants, int interpolantsDropped,
				int differenceOfNumOfInterpolantsBeforeAfter,
				HoareTripleCheckerBenchmarkGenerator htcbg) {
			m_DisjunctionsGreaterOneCounter  = disjunctionsGreaterOneCounter;
			m_DifferenceBeforeAfter = differenceOfNumOfInterpolantsBeforeAfter;
			m_NumOfHoareTripleChecks = htcbg.getSolverCounterSat();
			m_NumOfHoareTripleChecks.add(htcbg.getSolverCounterUnsat());
			m_NumOfHoareTripleChecks.add(htcbg.getSolverCounterUnknown());
			m_NewlyCreatedInterpolants = newlyCreatedInterpolants;
			m_InterpolantsDropped = interpolantsDropped;
		}
		
		public void incrementDiffAutomatonEmpty_Counter() {
			m_DiffAutomatonEmpty_Counter ++;
		}

		@Override
		public Collection<String> getKeys() {
			return InterpolantConsolidationBenchmarkType.getInstance().getKeys();
		}

		@Override
		public Object getValue(String key) {
			switch (key) {
			case InterpolantConsolidationBenchmarkType.s_NewlyCreatedInterpolants:
				return m_NewlyCreatedInterpolants;
			case InterpolantConsolidationBenchmarkType.s_InterpolantsDropped:
				return m_InterpolantsDropped;
			case InterpolantConsolidationBenchmarkType.s_DisjunctionsGreaterOneCounter:
				return m_DisjunctionsGreaterOneCounter;
			case InterpolantConsolidationBenchmarkType.s_DifferenceBeforeAfter:
				return m_DifferenceBeforeAfter;
			case InterpolantConsolidationBenchmarkType.s_NumberOfHoareTripleChecks:
				return m_NumOfHoareTripleChecks;
			case InterpolantConsolidationBenchmarkType.s_TimeOfConsolidation:
				try {
					return getElapsedTime(key);
				} catch (StopwatchStillRunningException e) {
					throw new AssertionError("clock still running: " + key);
				}
			case InterpolantConsolidationBenchmarkType.s_DifferenceAutomatonEmptyCounter:
				return m_DiffAutomatonEmpty_Counter;
			default:
				throw new AssertionError("unknown data");
			}
		}

		@Override
		public IBenchmarkType getBenchmarkType() {
			return InterpolantConsolidationBenchmarkType.getInstance();
		}
		

		@Override
		public String[] getStopwatches() {
			return new String[] {InterpolantConsolidationBenchmarkType.s_TimeOfConsolidation};
		}
	}
}
