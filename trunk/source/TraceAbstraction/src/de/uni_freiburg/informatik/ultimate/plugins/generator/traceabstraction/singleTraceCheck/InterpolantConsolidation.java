package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker.AllIntegers;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * TODO: Desc
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
	
	public InterpolantConsolidation(IPredicate precondition,
			IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			NestedWord<CodeBlock> trace, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals,
			IUltimateServiceProvider services,
			Logger logger, 
			PredicateUnifier predicateUnifier,
			InterpolatingTraceChecker tc,
			TAPreferences taPrefs) {
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
		if (m_InterpolatingTraceChecker.isCorrect() == LBool.UNSAT) {
			computeInterpolants(new AllIntegers());
		}
	}

	protected void computeInterpolants(Set<Integer> interpolatedPositions) {
		// 1. Build the path automaton for the given trace m_Trace
		PathProgramAutomatonConstructor ppc = new PathProgramAutomatonConstructor();
		INestedWordAutomaton<CodeBlock, IPredicate> pathprogramautomaton = ppc.constructAutomatonFromGivenPath(m_Trace, m_Services, m_SmtManager, m_TaPrefs);
		
		
		IHoareTripleChecker htc = BasicCegarLoop.getEfficientHoareTripleChecker(TraceAbstractionPreferenceInitializer.HoareTripleChecks.INCREMENTAL, 
				m_SmtManager, m_ModifiedGlobals, m_PredicateUnifier);
		
		// 2. Build the finite automaton (former interpolant path automaton) for the given Floyd-Hoare annotation
		NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton = constructInterpolantAutomaton(m_Trace, m_SmtManager, m_TaPrefs, m_Services, m_InterpolatingTraceChecker); // siehe BasicCegarLoop
//		boolean conservativeSuccessorCandidateSelection = (mPref.interpolantAutomatonEnhancement() == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE);
		// 3. Determinize the finite automaton from step 2. 
		DeterministicInterpolantAutomaton interpolantAutomatonDeterminized = new DeterministicInterpolantAutomaton(
				m_Services, m_SmtManager, m_ModifiedGlobals, htc, pathprogramautomaton, interpolantAutomaton,
				m_PredicateUnifier, m_Logger, false); // PREDICATE_ABSTRACTION_CONSERVATIVE = false (default)
		
		 
		PredicateFactoryForInterpolantConsolidation pfconsol = new PredicateFactoryForInterpolantConsolidation(m_SmtManager, m_TaPrefs); // TODO: Dummy params, to be refined
		
		PredicateFactory predicateFactoryInterpolantAutomata = new PredicateFactory(m_SmtManager, m_TaPrefs);
		
		PowersetDeterminizer<CodeBlock, IPredicate> psd2 = new PowersetDeterminizer<CodeBlock, IPredicate>(
				interpolantAutomatonDeterminized, true, predicateFactoryInterpolantAutomata);
		

		// TODO: Timeout exception!, weiterwerfen!
		try {
			// 4. Compute the difference between the path automaton and the determinized
			//    finite automaton (from step 3)
			Difference<CodeBlock, IPredicate> diff = new Difference<CodeBlock, IPredicate>(m_Services,
					(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) pathprogramautomaton,
					interpolantAutomatonDeterminized, psd2,
					pfconsol /* PredicateFactory for Refinement */, false /*explointSigmaStarConcatOfIA*/ );
			htc.releaseLock();
			
		} catch (AutomataLibraryException e) {
//			if ()
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		// 5. Interpolant Consolidation step
		List<IPredicate> pathPositionsToLocations = ppc.getPositionsToStates();
		HashRelation<IPredicate, IPredicate> locationsToSetOfPredicates = pfconsol.getLocationsToSetOfPredicates();
		m_ConsolidatedInterpolants = new IPredicate[m_Trace.length() - 1];
		for (int i = 0; i < m_ConsolidatedInterpolants.length; i++) {
			IPredicate loc = pathPositionsToLocations.get(i+1);
			// Compute the disjunction of the predicates for location i
			Set<IPredicate> predicatesForThisLocation = locationsToSetOfPredicates.getImage(loc);
			IPredicate[] predicatesForThisLocationAsArray = predicatesForThisLocation.toArray(new IPredicate[predicatesForThisLocation.size()]);
			TermVarsProc predicatesForThisLocationConsolidated = m_SmtManager.or(predicatesForThisLocationAsArray);
			// Store the consolidated (the disjunction of the predicates for the current location)
			m_ConsolidatedInterpolants[i] = m_PredicateUnifier.getOrConstructPredicate(predicatesForThisLocationConsolidated); 
		}
		assert TraceCheckerUtils.checkInterpolantsInductivityForward(m_ConsolidatedInterpolants, 
				m_Trace, m_Precondition, m_Postcondition, m_PendingContexts, "CP", 
				m_SmtManager, m_ModifiedGlobals, m_Logger) : "invalid Hoare triple in consolidated interpolants";
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
		
		
		InterpolantsPreconditionPostcondition ipp = 
				new InterpolantsPreconditionPostcondition(traceChecker);
		StateFactory<IPredicate> predicateFactory = new PredicateFactory(smtManager, taPrefs);
		
		NestedWordAutomaton<CodeBlock, IPredicate> nwa  = new NestedWordAutomaton<CodeBlock, IPredicate>(   services, 
																											internalAlphabet,
																											callAlphabet,
																											returnAlphabet,
																											predicateFactory);
		// Set the initial and the final state of the automaton
		nwa.addState(true, false, traceChecker.getPrecondition());
		nwa.addState(false, true, traceChecker.getPostcondition());
		// Add other states and corresponding transitions
		for (int i=0; i<trace.length(); i++) {
			IPredicate pred = ipp.getInterpolant(i);
			IPredicate succ = ipp.getInterpolant(i+1);
			assert nwa.getStates().contains(pred);
			if (!nwa.getStates().contains(succ)) {
				nwa.addState(false, false, succ);
			}
			if (trace.isCallPosition(i)) {
				nwa.addCallTransition(pred, trace.getSymbol(i), succ);
			} else if (trace.isReturnPosition(i)) {
				assert !trace.isPendingReturn(i);
				int callPos = trace.getCallPosition(i);
				IPredicate hierPred = ipp.getInterpolant(callPos);
				nwa.addReturnTransition(pred, hierPred, trace.getSymbol(i), succ);
			} else {
				assert trace.isInternalPosition(i);
				nwa.addInternalTransition(pred, trace.getSymbol(i), succ);
			}
		}
		
		return nwa;
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

	@Override
	public PredicateUnifier getPredicateUnifier() {
		return m_PredicateUnifier;
	}


	
}
