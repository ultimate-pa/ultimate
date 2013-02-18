package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

//TODO: Add cache for rejected queries.
//TODO: Implement another variant, LazyStrongestPost. Get most information from
//  powerset determinizer, theorem prover only for selfloops
/**
 * Determinizes an Interpolant Automaton. The result accepts a superset of the
 * interpolant automatons language.
 * 
 * Idea: Given a determinized State { I_1, ..., I_n }, the successor under
 * symbol is the determinized state 
 * { I' \in Interpolants  | (I_1/\ ... /\ I_n, symbol, I') is inductive }  
 * 
 * For nested word automaton we can represent a determinized state by a set of
 * interpolants (opposed to a set of pairs of interpolants which is necessary
 * using the powerset construction). This is sufficient because we only need
 * that the transitions are inductive.
 *
 */
public class StrongestPostDeterminizer 
					implements IStateDeterminizer<CodeBlock, IPredicate> {

	private final SmtManager m_SmtManager;
	private final SmtManager.EdgeChecker m_EdgeChecker;
	private StateFactory<IPredicate> m_ConFac;
	private INestedWordAutomaton<CodeBlock, IPredicate> m_Ia;
	private final IPredicate m_IaFalseState;
	private final IPredicate m_IaTrueState;
	
	private CodeBlock m_AssertedCodeBlock;
	private IPredicate m_AssertedState;
	private IPredicate m_AssertedHier;
	
	DeterminizedState<CodeBlock, IPredicate> m_ResultFinalState;

	public StrongestPostDeterminizer(SmtManager mSmtManager,
			TAPreferences taPreferences,
			INestedWordAutomaton<CodeBlock, IPredicate> mNwa) {
		super();
		m_SmtManager = mSmtManager;
		m_EdgeChecker = m_SmtManager.new EdgeChecker();
		m_ConFac = mNwa.getStateFactory();
		m_Ia = mNwa;
		
		assert m_Ia.getInitialStates().size() == 1 : "Interpolant Automaton" +
				" must have one inital state";
		m_IaTrueState = m_Ia.getInitialStates().iterator().next();
		
		assert m_Ia.getInitialStates().size() == 1 : "Interpolant Automaton" +
			" must have one final state";
		m_IaFalseState = m_Ia.getFinalStates().iterator().next();
		
		m_ResultFinalState = 
			new DeterminizedState<CodeBlock, IPredicate>(m_Ia);
		m_ResultFinalState.addPair(m_Ia.getEmptyStackState(), m_IaFalseState, m_Ia);
	}


	@Override
	public DeterminizedState<CodeBlock, IPredicate> initialState() {
		DeterminizedState<CodeBlock, IPredicate> detState = 
			new DeterminizedState<CodeBlock, IPredicate>(m_Ia);
		detState.addPair(m_Ia.getEmptyStackState(), m_IaTrueState, m_Ia);
		return detState;
	}

	@Override
	public DeterminizedState<CodeBlock, IPredicate> internalSuccessor(
			DeterminizedState<CodeBlock, IPredicate> detState,
			CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			return m_ResultFinalState;
		}
		//Construct Successsor Determinized state.
		DeterminizedState<CodeBlock, IPredicate> detSucc = 
			new DeterminizedState<CodeBlock, IPredicate>(m_Ia);
		//Add true state, since this will always be contained
		detSucc.addPair(m_Ia.getEmptyStackState(), m_IaTrueState, m_Ia);
		//All our successors will use the empty stack state as down state
		Set<IPredicate> succs = 
							detSucc.getUpStates(m_Ia.getEmptyStackState());
		//Add states that we may add because the automaton says so
		for (IPredicate state :detState.getUpStates(
								m_Ia.getEmptyStackState())) {
			succs.addAll(m_Ia.succInternal(state, symbol));
		}
		//If final state is contained, we are done
		if (succs.contains(m_IaFalseState)) {
			clearAssertionStack();
			return m_ResultFinalState;
		}
		//Get formula which describes current state
		IPredicate detStateConjunction = detState.getContent(m_ConFac);
		//Check if edge to final is already inductive
		LBool leadsToFinal = inductiveInternal(detStateConjunction, symbol, m_IaFalseState);
//		assert leadsToFinal == m_SmtManager.isInductive(detStateConjunction, 
//					symbol, m_IaFalseState);
		
//		LBool leadsToFinal = m_SmtManager.isInductive(detStateConjunction, 
//				symbol, m_IaFalseState);
		if (leadsToFinal == Script.LBool.UNSAT) {
			clearAssertionStack();
			return m_ResultFinalState;
		}
		

		//Check for remaining states if we may add them.
		String targetProc = ((ProgramPoint) symbol.getTarget()).getProcedure();
		for (IPredicate succCand : m_Ia.getStates()) {
			if (succs.contains(succCand) || 
				succCand == m_IaFalseState ||
				succCand == m_IaTrueState) {
				continue;
			}
			String succCandProc = getProcedure(succCand);
			if (succCandProc == null || succCandProc.equals(targetProc)) {
				LBool isInductive = inductiveInternal(detStateConjunction, symbol, succCand);
				//			assert isInductive == m_SmtManager.isInductive(detStateConjunction, 
				//					symbol, succCand);
				//			LBool isInductive = m_SmtManager.isInductive(detStateConjunction, 
				//					symbol, succCand);
				if (isInductive == Script.LBool.UNSAT) {
					succs.add(succCand);
				}
			}
		}
		clearAssertionStack();
		return detSucc;
	}
	
	

	
	
	
	@Override
	public DeterminizedState<CodeBlock, IPredicate> callSuccessor(
			DeterminizedState<CodeBlock, IPredicate> detState,
			CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			return m_ResultFinalState;
		}
		//Construct Successsor Determinized state.
		DeterminizedState<CodeBlock, IPredicate> detSucc = 
			new DeterminizedState<CodeBlock, IPredicate>(m_Ia);
		//Add true state, since this will always be contained
		detSucc.addPair(m_Ia.getEmptyStackState(), m_IaTrueState, m_Ia);
		//All our successors will use the empty stack state as down state
		Set<IPredicate> succs = 
						detSucc.getUpStates(m_Ia.getEmptyStackState());
		//Add states that we may add because the automaton says so
		for (IPredicate state :detState.getUpStates(
								m_Ia.getEmptyStackState())) {
			succs.addAll(m_Ia.succCall(state, symbol));
		}
		//If final state is contained, we are done
		if (succs.contains(m_IaFalseState)) {
			clearAssertionStack();
			return m_ResultFinalState;
		}
		//Get formula which describes current state
		IPredicate detStateConjunction = detState.getContent(m_ConFac);
		//Check if edge to final is already inductive
		LBool leadsToFinal = inductiveCall(detStateConjunction, 
					(Call) symbol, m_IaFalseState);
		if (leadsToFinal == Script.LBool.UNSAT) {
			clearAssertionStack();
			return m_ResultFinalState;
		}
		//Check for remaining states if we may add them.
		String targetProc = ((ProgramPoint) symbol.getTarget()).getProcedure();
		for (IPredicate succCand : m_Ia.getStates()) {
			if (succs.contains(succCand) || 
				succCand == m_IaFalseState ||
				succCand == m_IaTrueState) {
				continue;
			}
			String succCandProc = getProcedure(succCand);
			if (succCandProc == null || succCandProc.equals(targetProc)) {
				LBool isInductive = inductiveCall(detStateConjunction, 
						(Call) symbol, succCand);
				if (isInductive == Script.LBool.UNSAT) {
					succs.add(succCand);
				}
			}
		}
		clearAssertionStack();
		return detSucc;
	}
	
	

	@Override
	public DeterminizedState<CodeBlock, IPredicate> returnSuccessor(
			DeterminizedState<CodeBlock, IPredicate> detState,
			DeterminizedState<CodeBlock, IPredicate> detHier,
			CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			return m_ResultFinalState;
		}
		
		Set<IPredicate> hierStates = 
							detHier.getUpStates(m_Ia.getEmptyStackState());
		
		//Construct Successsor Determinized state.
		DeterminizedState<CodeBlock, IPredicate> detSucc = 
			new DeterminizedState<CodeBlock, IPredicate>(m_Ia);
		//Add true state, since this will always be contained
		detSucc.addPair(m_Ia.getEmptyStackState(), m_IaTrueState, m_Ia);
		//All our successors will use the empty stack state as down state
		Set<IPredicate> succs = 
							detSucc.getUpStates(m_Ia.getEmptyStackState());
		//Add states that we may add because the automaton says so
		for (IPredicate state :detState.getUpStates(
								m_Ia.getEmptyStackState())) {
			for (IPredicate hier : m_Ia.hierPred(state, symbol)) {
				if (hierStates.contains(hier)) {
					succs.addAll(m_Ia.succReturn(state,hier,symbol));
				}
			}
		}
		//If final state is contained, we are done
		if (succs.contains(m_IaFalseState)) {
			clearAssertionStack();
			return m_ResultFinalState;
		}
		//Get formula which describes current state
		IPredicate detStateConjunction = detState.getContent(m_ConFac);
		//Get formula which describes current hierarchical successor
		IPredicate detHierConjunction = detHier.getContent(m_ConFac);
		//Check if edge to final is already inductive
		LBool leadsToFinal = inductiveReturn(detStateConjunction,
				detHierConjunction,	(Return) symbol, 
				m_IaFalseState);
		if (leadsToFinal == Script.LBool.UNSAT) {
			clearAssertionStack();
			return m_ResultFinalState;
		}
		//Check for remaining states if we may add them.
		String targetProc = ((ProgramPoint) symbol.getTarget()).getProcedure();
		for (IPredicate succCand : m_Ia.getStates()) {
			if (succs.contains(succCand) || 
				succCand == m_IaFalseState ||
				succCand == m_IaTrueState) {
				continue;
			}
			String succCandProc = getProcedure(succCand);
			if (succCandProc == null || succCandProc.equals(targetProc)) {
				LBool isInductive = inductiveReturn(detStateConjunction,
						detHierConjunction,	(Return) symbol, 
						succCand);
				if (isInductive == Script.LBool.UNSAT) {
					succs.add(succCand);
				}
			}
		}
		clearAssertionStack();
		return detSucc;
	}


	@Override
	public int getMaxDegreeOfNondeterminism() {
		// TODO Auto-generated method stub
		return 0;
	}


	
	
	private LBool inductiveInternal(IPredicate state, CodeBlock cb, IPredicate succ) {
		LBool result = null;
		if (succ == m_IaFalseState) {
			result = m_EdgeChecker.sdecInternalToFalse(state, cb);
			if (result != null) {
				assert reviewInductiveInternal(state, cb, succ, result);
				return result;
			}
		} 
		result = m_EdgeChecker.sdecInteral(state, cb, succ);
		if (result != null) {
			assert reviewInductiveInternal(state, cb, succ, result);
			return result;
		}
		if (m_AssertedCodeBlock == null) {
			m_EdgeChecker.assertCodeBlock(cb);
			m_AssertedCodeBlock = cb;
		}
		if (m_AssertedState != null && m_AssertedState != state) {
			m_EdgeChecker.unAssertPrecondition();
		}
		if (m_AssertedState != state) {
			m_EdgeChecker.assertPrecondition(state);
			m_AssertedState = state;
		}
		result = m_EdgeChecker.postInternalImplies(succ);
		assert reviewInductiveInternal(state, cb, succ, result);
		return result;		
	}
	
	
	private LBool inductiveCall(IPredicate state, Call cb, IPredicate succ) {
		LBool result = null;
		result = m_EdgeChecker.sdecCall(state, cb, succ);
		if (result != null) {
			return result;
		}
		if (m_AssertedCodeBlock == null) {
			m_EdgeChecker.assertCodeBlock(cb);
			m_AssertedCodeBlock = cb;
		}
		if (m_AssertedState != null && m_AssertedState != state) {
			m_EdgeChecker.unAssertPrecondition();
		}
		if (m_AssertedState != state) {
			m_EdgeChecker.assertPrecondition(state);
			m_AssertedState = state;
		}
		result = m_EdgeChecker.postCallImplies(succ);
		return result;		
	}
	
	
	private LBool inductiveReturn(IPredicate state, IPredicate hier, Return cb, 
			IPredicate succ) {
		LBool result = null;
		result = m_EdgeChecker.sdecReturn(state, hier, cb, succ);
		if (result != null) {
			return result;
		}
		if (m_AssertedCodeBlock == null) {
			m_EdgeChecker.assertCodeBlock(cb);
			m_AssertedCodeBlock = cb;
		}
		if (m_AssertedHier != null && m_AssertedHier != hier) {
			m_EdgeChecker.unAssertPrecondition();
			m_AssertedState = null;
			m_EdgeChecker.unAssertHierPred();
		}
		if (m_AssertedHier != hier) {
			m_EdgeChecker.assertHierPred(hier);
			m_AssertedHier = hier;
		}
		if (m_AssertedState != null && m_AssertedState != state) {
			m_EdgeChecker.unAssertPrecondition();
		}
		if (m_AssertedState != state) {
			m_EdgeChecker.assertPrecondition(state);
			m_AssertedState = state;
		}
		result = m_EdgeChecker.postReturnImplies(succ);
		return result;	
	}
	
	
	
	
	private void clearAssertionStack() {
		if (m_AssertedState != null) {
			m_EdgeChecker.unAssertPrecondition();
			m_AssertedState = null;
		}
		if (m_AssertedHier != null) {
			m_EdgeChecker.unAssertHierPred();
			m_AssertedHier = null;
		}
		if (m_AssertedCodeBlock != null) {
			m_EdgeChecker.unAssertCodeBlock();
			m_AssertedCodeBlock = null;
		}
	}
	
	private String getProcedure(IPredicate p) {
		assert p.getProcedures().length < 2;
		if (p.getProcedures().length == 0) {
			return null;
		} else {
			return p.getProcedures()[0];
		}
	}
	
	
	private boolean reviewInductiveInternal(IPredicate state, CodeBlock cb, IPredicate succ, LBool result) {
		clearAssertionStack();
		LBool reviewResult = m_SmtManager.isInductive(state, cb, succ);
		if (satCompatible(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "Review result: " + reviewResult);
		}
	}
	
	private boolean reviewInductiveCall(IPredicate state, Call cb, IPredicate succ, LBool result) {
		clearAssertionStack();
		LBool reviewResult = m_SmtManager.isInductiveCall(state, cb, succ);
		if (satCompatible(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "Review result: " + reviewResult);
		}

	}
	
	private boolean reviewInductiveReturn(IPredicate state, Call cb, IPredicate succ, LBool result) {
		clearAssertionStack();
		LBool reviewResult = m_SmtManager.isInductiveCall(state, cb, succ);
		if (satCompatible(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "Review result: " + reviewResult);
		}
	}
	
	
	/**
	 * Return true if both inputs are UNSAT or both inputs are in {SAT,UNKNOWN}.
	 */
	private boolean satCompatible(LBool sat1, LBool sat2) {
		switch (sat1) {
		case UNSAT:
			return sat2 == LBool.UNSAT;
		case SAT:
			if (sat2 == LBool.SAT || sat2 == LBool.UNKNOWN) {
				return true;
			} else {
				return false;
			}
		case UNKNOWN:
			if (sat2 == LBool.SAT || sat2 == LBool.UNKNOWN) {
				return true;
			} else {
				return false;
			}
		default:
			throw new UnsupportedOperationException();
		}
	}
	

}
