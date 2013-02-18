package local.stalin.plugins.generator.traceabstraction;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.operations.DeterminizedState;
import local.stalin.automata.nwalibrary.operations.IStateDeterminizer;
import local.stalin.plugins.generator.rcfgbuilder.CallAnnot;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.ReturnAnnot;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;

public class BestApproximationDeterminizer 
		implements IStateDeterminizer<TransAnnot, IProgramState> {
	
	SmtManager m_SmtManager;
	ContentFactory<IProgramState> m_TAContentFactory;
	INestedWordAutomaton<TransAnnot, IProgramState> m_Nwa;
	int m_AnswerInternalSolver = 0;
	int m_AnswerInternalAutomaton = 0;
	int m_AnswerInternalCache = 0;
	int m_AnswerCallSolver = 0;
	int m_AnswerCallAutomaton = 0;
	int m_AnswerCallCache = 0;
	int m_AnswerReturnSolver = 0;
	int m_AnswerReturnAutomaton = 0;
	int m_AnswerReturnCache = 0;


	Map<IState,Map<TransAnnot,Set<IState>>>	m_InductiveSuccsCache = 
		new HashMap<IState,Map<TransAnnot,Set<IState>>>();
	
	Map<IState,Map<TransAnnot,Set<IState>>>	m_InductiveCallSuccsCache = 
		new HashMap<IState,Map<TransAnnot,Set<IState>>>();
	
	Map<IState,Map<IState,Map<TransAnnot,Set<IState>>>> m_InductiveReturnSuccsCache = 
		new HashMap<IState,Map<IState,Map<TransAnnot,Set<IState>>>>();
	

	public BestApproximationDeterminizer(SmtManager mSmtManager,
			ContentFactory<IProgramState> mTAContentFactory,
			INestedWordAutomaton<TransAnnot, IProgramState> mNwa) {
		super();
		m_SmtManager = mSmtManager;
		m_TAContentFactory = mTAContentFactory;
		m_Nwa = mNwa;
	}

	@Override
	public DeterminizedState<TransAnnot, IProgramState>  internalSuccessor(
			DeterminizedState<TransAnnot, IProgramState>  detState,
			TransAnnot symbol) {
		
		DeterminizedState<TransAnnot, IProgramState>  succDetState = 
			new DeterminizedState<TransAnnot, IProgramState> (m_TAContentFactory);
		for (IState<TransAnnot, IProgramState>  downState : 
												detState.getCallerStates()) {
			for (IState<TransAnnot, IProgramState>  upState : 
										detState.getPresentStates(downState)) {
				for (IState<TransAnnot, IProgramState>  upSucc : 
											getInternalSuccs(upState,symbol)) {
					succDetState.addPair(downState,upSucc);
				}
			}
		}
//		assert(m_SmtManager.checkInductivity(detState.getContent(), symbol, 
//				succDetState.getContent()) == SMTInterface.SMT_UNSAT);
		return succDetState;	
	}
	
	@Override
	public DeterminizedState<TransAnnot, IProgramState>  callSuccessor(
			DeterminizedState<TransAnnot, IProgramState>  detState, 
			TransAnnot symbol) {
		
		DeterminizedState<TransAnnot, IProgramState>  succDetState = 
				new DeterminizedState<TransAnnot, IProgramState> (m_TAContentFactory);
		for (IState<TransAnnot, IProgramState>  downState : 
												detState.getCallerStates()) {
			for (IState<TransAnnot, IProgramState>  upState : 
										detState.getPresentStates(downState)) {
				for (IState<TransAnnot, IProgramState>  upSucc : 
									getCallSuccs(upState,(CallAnnot) symbol)) {
					succDetState.addPair(upState,upSucc);
				}
			}
		}
		assert(m_SmtManager.isInductiveCall(detState.getContent(), 
				(CallAnnot) symbol, 
				succDetState.getContent()) == SMTInterface.SMT_UNSAT);
		return succDetState;	
	}

	@Override
	public DeterminizedState<TransAnnot, IProgramState>  returnSuccessor(
			DeterminizedState<TransAnnot, IProgramState>  detState,
			DeterminizedState<TransAnnot, IProgramState>  detLinPred,
			TransAnnot symbol) {
		
		DeterminizedState<TransAnnot, IProgramState>  succDetState = 
				new DeterminizedState<TransAnnot, IProgramState> (m_TAContentFactory);
		
		for (IState<TransAnnot, IProgramState>  downLinPred : 
												detLinPred.getCallerStates()) {
			for (IState<TransAnnot, IProgramState>  upLinPred : 
									detLinPred.getPresentStates(downLinPred)) {
				Set<IState<TransAnnot, IProgramState> > upStates = 
										detState.getPresentStates(upLinPred);
				if (upStates == null) continue;
				for (IState<TransAnnot, IProgramState>  upState : upStates) {
					ReturnAnnot returnSymbol = (ReturnAnnot) symbol;
					for (IState<TransAnnot, IProgramState>  upSucc : 
							getReturnSuccs(upState,upLinPred, returnSymbol)) {
						succDetState.addPair(downLinPred, upSucc);
					}
				}
			}
		}
		
		assert(m_SmtManager.isInductiveReturn(detState.getContent(),
				detLinPred.getContent(),
				(ReturnAnnot) symbol, 
				succDetState.getContent()) == SMTInterface.SMT_UNSAT);

		return succDetState;	
	}
	
	
	
	
	
	/**
	 * Return all states succ such that (state, symbol, succ) is inductive.
	 */
	private Set<IState> getInternalSuccs(
			IState<TransAnnot, IProgramState> state,
			TransAnnot symbol) {
		Set<IState> succs = getInternalSuccsCache(state, symbol);
		if (succs == null) {
			succs = new HashSet<IState>();
			for (IState succCandidate : m_Nwa.getAllStates()) {
				if (isInductiveInternalSuccessor(state, symbol, succCandidate))
					succs.add(succCandidate);
			}
			putInternalSuccsCache(state, symbol, succs);
		}
		else {
			m_AnswerInternalCache++;
		}
		return succs;
	}

	/**
	 * Store in the cache that succs is the set of all states succ such that
	 * (state, symbol, succ) is inductive.
	 */
	private void putInternalSuccsCache(
			IState<TransAnnot, IProgramState> state,
			TransAnnot symbol,
			Set<IState> succs) {
		Map<TransAnnot, Set<IState>> symbol2succs = 
			m_InductiveSuccsCache.get(state);
		if (symbol2succs == null) {
			symbol2succs = new HashMap<TransAnnot, Set<IState>>();
			m_InductiveSuccsCache.put(state, symbol2succs);
		}
		symbol2succs.put(symbol, succs);
	}

	/**
	 * Let succs be the set of all states succ such that (state, symbol, succ)
	 * is inductive. If the cache knows this result succs is returned, otherwise
	 * null is returned.
	 */
	private Set<IState> getInternalSuccsCache(
			IState<TransAnnot, IProgramState> state,
			TransAnnot symbol) {
		Map<TransAnnot, Set<IState>> symbol2succs = 
			m_InductiveSuccsCache.get(state);
		if (symbol2succs == null) {
			return null;
		}
		Set<IState> succs = symbol2succs.get(symbol);
		if (succs == null) {
			return null;
		}
		return succs;
	}
	
	
	
	
	
	/**
	 * Return all states succ such that (state, symbol, succ) is inductive.
	 */
	private Set<IState> getCallSuccs(
			IState<TransAnnot, IProgramState> state,
			CallAnnot symbol) {
		Set<IState> succs = getCallSuccsCache(state, symbol);
		if (succs == null) {
			succs = new HashSet<IState>();
			for (IState succCandidate : m_Nwa.getAllStates()) {
				if (inductiveCallSuccessor(state, symbol, succCandidate))
					succs.add(succCandidate);
			}
			putCallSuccsCache(state, symbol, succs);
		}
		else {
			m_AnswerCallCache++;
		}
		return succs;
	}

	
	/**
	 * Store in the cache that succs is the set of all states succ such that
	 * (state, symbol, succ) is inductive.
	 */
	private void putCallSuccsCache(
			IState<TransAnnot, IProgramState> state,
			TransAnnot symbol,
			Set<IState> succs) {
		Map<TransAnnot, Set<IState>> symbol2succs = 
			m_InductiveCallSuccsCache.get(state);
		if (symbol2succs == null) {
			symbol2succs = new HashMap<TransAnnot, Set<IState>>();
			m_InductiveCallSuccsCache.put(state, symbol2succs);
		}
		symbol2succs.put(symbol, succs);
	}

	/**
	 * Let succs be the set of all states succ such that (state, symbol, succ)
	 * is inductive. If the cache knows this result succs is returned, otherwise
	 * null is returned.
	 */
	private Set<IState> getCallSuccsCache(
			IState<TransAnnot, IProgramState> state,
			TransAnnot symbol) {
		Map<TransAnnot, Set<IState>> symbol2succs = 
			m_InductiveCallSuccsCache.get(state);
		if (symbol2succs == null) {
			return null;
		}
		Set<IState> succs = symbol2succs.get(symbol);
		if (succs == null) {
			return null;
		}
		return succs;
	}
	
	/**
	 * Returns true iff (state,symbol,succ) is inductive. Fist the interpolant
	 * automaton is queried for a yes-answer, afterwards the solver is
	 * queried for a yes/no/unknown-answer. We querying the interpolant
	 * automaton for two reasons:
	 * <ul>
	 * <li> a query to the solver is expensive
	 * <li> if we do not compute interpolants for every location we have 
	 * unknown-labeled states for which the solver can not give a yes/no-answer.
	 * </ul> 
	 */
	private boolean isInductiveInternalSuccessor(
			IState<TransAnnot, IProgramState>  state,
			TransAnnot symbol,
			IState<TransAnnot, IProgramState>  succ) {
		
		if (state.getInternalSucc(symbol).contains(succ)) {
			m_AnswerInternalAutomaton++;
			return true;
		}
		IProgramState presentPs = state.getContent();
		IProgramState succPs = succ.getContent();
		int sat = m_SmtManager.checkInductivity(presentPs, symbol, succPs);
		m_AnswerInternalSolver++;
		if (sat == SMTInterface.SMT_UNSAT) {
			m_Nwa.addInternalTransition(state, symbol, succ);
			return true;
		}
		else {
			return false;	
		}
	}
	
	/**
	 * Returns true iff (state,symbol,succ) is inductive. Fist the interpolant
	 * automaton is queried for a yes-answer, afterwards the solver is
	 * queried for a yes/no/unknown-answer. We querying the interpolant
	 * automaton for two reasons:
	 * <ul>
	 * <li> a query to the solver is expensive
	 * <li> if we do not compute interpolants for every location we have 
	 * unknown-labeled states for which the solver can not give a yes/no-answer.
	 * </ul> 
	 */
	private boolean inductiveCallSuccessor(
			IState<TransAnnot, IProgramState>  state,
			CallAnnot symbol,
			IState<TransAnnot, IProgramState>  succ) {
		if (state.getCallSucc(symbol).contains(succ)) {
			m_AnswerCallAutomaton++;
			return true;
		}
		IProgramState presentPs = state.getContent();
		IProgramState succPs = succ.getContent();
		int sat = m_SmtManager.isInductiveCall(presentPs, symbol, succPs);
		m_AnswerCallSolver++;
		if (sat == SMTInterface.SMT_UNSAT) {
			return true;
		}
		return false;
	}
	
	
	
	
	/**
	 * Return all states succ such that (state, linPred, symbol, succ) is
	 * inductive.
	 */
	private Set<IState> getReturnSuccs(
			IState<TransAnnot, IProgramState> state,
			IState<TransAnnot, IProgramState> linPred, 
			ReturnAnnot symbol) {
		Set<IState> succs = getReturnSuccsCache(state, linPred, symbol);
		if (succs == null) {
			succs = new HashSet<IState>();
			for (IState succCandidate : m_Nwa.getAllStates()) {
				if (isInductiveReturnSuccessor(state, linPred, symbol, succCandidate))
					succs.add(succCandidate);
			}
			putReturnSuccsCache(state, linPred, symbol, succs);
		}
		else {
			m_AnswerReturnCache++;
		}
		return succs;
	}
	
	/**
	 * Store in the cache that succs is the set of all states succ such that
	 * (state, linPred, symbol, succ) is inductive.
	 */
	private void putReturnSuccsCache(
			IState<TransAnnot, IProgramState> state,
			IState<TransAnnot, IProgramState> linPred, 
			TransAnnot symbol,
			Set<IState> succs) {
		Map<IState, Map<TransAnnot, Set<IState>>> linPred2symbol2succs = 
			m_InductiveReturnSuccsCache.get(state);
		if (linPred2symbol2succs == null) {
			linPred2symbol2succs = 
				new HashMap<IState, Map<TransAnnot, Set<IState>>>();
			m_InductiveReturnSuccsCache.put(state, linPred2symbol2succs);	
		}
		Map<TransAnnot, Set<IState>> symbol2succs = 
			linPred2symbol2succs.get(linPred);
		if (symbol2succs == null) {
			symbol2succs = new HashMap<TransAnnot, Set<IState>>();
			linPred2symbol2succs.put(linPred, symbol2succs);
		}
		symbol2succs.put(symbol, succs);
	}

	/**
	 * Let succs be the set of all states succ such that 
	 * (state, linPred, symbol, succ) is inductive. If the cache knows this 
	 * result succs is returned, otherwise
	 * null is returned.
	 */
	private Set<IState> getReturnSuccsCache(
			IState<TransAnnot, IProgramState> state,
			IState<TransAnnot, IProgramState> linPred, 
			TransAnnot symbol) {
		Map<IState, Map<TransAnnot, Set<IState>>> linPred2symbol2succs = 
			m_InductiveReturnSuccsCache.get(state);
		if (linPred2symbol2succs == null) {
			return null;
		}
		Map<TransAnnot, Set<IState>> symbol2succs = 
			linPred2symbol2succs.get(linPred);
		if (symbol2succs == null) {
			return null;
		}
		Set<IState> succs = symbol2succs.get(symbol);
		if (succs == null) {
			return null;
		}
		return succs;
	}
	
	
	/**
	 * Returns true iff (state,callerState,symbol,succ) is inductive.
	 * Fist the interpolant automaton is queried for a yes-answer, afterwards 
	 * the solver is queried for a yes/no/unknown-answer. We querying the 
	 * interpolant automaton for two reasons:
	 * <ul>
	 * <li> a query to the solver is expensive
	 * <li> if we do not compute interpolants for every location we have 
	 * unknown-labeled states for which the solver can not give a yes/no-answer.
	 * </ul> 
	 */
	private boolean isInductiveReturnSuccessor(
			IState<TransAnnot, IProgramState>  state,
			IState<TransAnnot, IProgramState>  callerState,
			ReturnAnnot symbol,
			IState<TransAnnot, IProgramState>  succ) {
		if (state.getReturnSucc(callerState, symbol).contains(succ)) {
			m_AnswerReturnAutomaton++;
			return true;
		}
		IProgramState presentPs = state.getContent();
		IProgramState callerPs = callerState.getContent();
		IProgramState succPs = succ.getContent();
		int sat = 
			m_SmtManager.isInductiveReturn(presentPs, callerPs, symbol, succPs);
		m_AnswerReturnSolver++;
		if (sat == SMTInterface.SMT_UNSAT) {
			return true;
		}
		return false;
	}
	


	








}
