package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class PostDeterminizerNoFrills implements
		IStateDeterminizer<CodeBlock, IPredicate> {
	private final EdgeChecker m_EdgeChecker;
	private final boolean m_UseDoubleDecker;
	private final NestedWordAutomaton<CodeBlock, IPredicate> m_Ia;
	private final NestedWordAutomatonCache<CodeBlock, IPredicate> m_RejectionCache;
	
	private CodeBlock m_AssertedCodeBlock;
	private IPredicate m_AssertedState;
	private IPredicate m_AssertedHier;
	
	
	

	public PostDeterminizerNoFrills(EdgeChecker edgeChecker,
			boolean useDoubleDecker,
			NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		super();
		m_EdgeChecker = edgeChecker;
		m_UseDoubleDecker = useDoubleDecker;
		m_Ia = nwa;
		m_RejectionCache = new NestedWordAutomatonCache<CodeBlock, IPredicate>(
				m_Ia.getInternalAlphabet(), 
				m_Ia.getCallAlphabet(), 
				m_Ia.getReturnAlphabet(), 
				m_Ia.getStateFactory());
		for (IPredicate state : m_Ia.getStates()) {
			m_RejectionCache.addState(m_Ia.isInitial(state), m_Ia.isFinal(state), state);
		}
	}

	@Override
	public DeterminizedState<CodeBlock, IPredicate> initialState() {
		DeterminizedState<CodeBlock, IPredicate> detState = 
			new DeterminizedState<CodeBlock, IPredicate>(m_Ia);
		for (IPredicate initialState : m_Ia.getInitialStates()) {
			detState.addPair(m_Ia.getEmptyStackState(), initialState, m_Ia);
		}
		return detState;
	}

	@Override
	public DeterminizedState<CodeBlock, IPredicate> internalSuccessor(
			DeterminizedState<CodeBlock, IPredicate> detState, CodeBlock symbol) {
		DeterminizedState<CodeBlock, IPredicate> result = new DeterminizedState<CodeBlock, IPredicate>(m_Ia);
		for (IPredicate down : detState.getDownStates()) {
			assert m_UseDoubleDecker || down == m_Ia.getEmptyStackState();
			for (IPredicate up : detState.getUpStates(down)) {
				if (m_RejectionCache.succInternal(up, symbol) == null) {
					computeSuccInternal(up, symbol);
					assert m_RejectionCache.succInternal(up, symbol) != null;
				}
				for (OutgoingInternalTransition<CodeBlock, IPredicate> trans : 
					m_Ia.internalSuccessors(up)) {
					result.addPair(down, trans.getSucc(), m_Ia);
				}
			}
		}
		clearAssertionStack();
		return result;
	}



	@Override
	public DeterminizedState<CodeBlock, IPredicate> callSuccessor(
			DeterminizedState<CodeBlock, IPredicate> detState, CodeBlock symbol) {
		DeterminizedState<CodeBlock, IPredicate> result = new DeterminizedState<CodeBlock, IPredicate>(m_Ia);
		for (IPredicate down : detState.getDownStates()) {
			assert m_UseDoubleDecker || down == m_Ia.getEmptyStackState();
			for (IPredicate up : detState.getUpStates(down)) {
				if (m_RejectionCache.succCall(up, symbol) == null) {
					computeSuccCall(up, symbol);
					assert m_RejectionCache.succCall(up, symbol) != null;
				}
				for (OutgoingCallTransition<CodeBlock, IPredicate> trans : 
					m_Ia.callSuccessors(up)) {
					if (m_UseDoubleDecker) {
						result.addPair(up, trans.getSucc(), m_Ia);
					} else {
						result.addPair(m_Ia.getEmptyStackState(), trans.getSucc(), m_Ia);
					}
				}
			}
		}
		clearAssertionStack();
		return result;
	}

	@Override
	public DeterminizedState<CodeBlock, IPredicate> returnSuccessor(
			DeterminizedState<CodeBlock, IPredicate> detState,
			DeterminizedState<CodeBlock, IPredicate> detHier, CodeBlock symbol) {
		DeterminizedState<CodeBlock, IPredicate> result = new DeterminizedState<CodeBlock, IPredicate>(m_Ia);
		for (IPredicate hierDown : detHier.getDownStates()) {
			assert m_UseDoubleDecker || hierDown == m_Ia.getEmptyStackState();
			for (IPredicate hierUp : detHier.getUpStates(hierDown)) {
				if (m_UseDoubleDecker) {
					assert detState.getDownStates().contains(hierUp);
					for (IPredicate up : detState.getUpStates(hierUp)) {
						addReturnSuccessorsGivenHier(up, hierUp, symbol, result, hierDown);
					}
				} else {
					for (IPredicate down : detState.getDownStates()) {
						assert down == m_Ia.getEmptyStackState();
						for (IPredicate up : detState.getUpStates(down)) {
							addReturnSuccessorsGivenHier(up, hierUp, symbol, result, hierDown);
						}
					}
					
				}
			}
		}
		clearAssertionStack();
		return result;
	}

	private void addReturnSuccessorsGivenHier(IPredicate up, IPredicate hier,
			CodeBlock symbol, DeterminizedState<CodeBlock, IPredicate> result, IPredicate hierDown) {
		if (m_RejectionCache.succReturn(up, hier, symbol) == null) {
			computeSuccReturn(up, hier, (Return) symbol);
			assert m_RejectionCache.succReturn(up, hier, symbol) != null;
		}
		for (OutgoingReturnTransition<CodeBlock, IPredicate> trans : 
			m_Ia.returnSucccessors(up, hier, symbol)) {
			result.addPair(hierDown, trans.getSucc(), m_Ia);
		}
		
	}

	@Override
	public int getMaxDegreeOfNondeterminism() {
		// TODO Auto-generated method stub
		return 0;
	}
	
	
	private void computeSuccInternal(IPredicate state, CodeBlock symbol) {
		for (IPredicate succCand : m_Ia.getStates()) {
			LBool sat;
			if (succCand == state) {
				sat = m_EdgeChecker.sdecInternalSelfloop(state, symbol);
			} else {
				sat = m_EdgeChecker.sdLazyEcInteral(state, symbol, succCand);
			}
			if (sat == null) {
				sat = computeSuccInternalSolver(state, symbol, succCand);
			}
			if (sat == LBool.UNSAT) {
				m_Ia.addInternalTransition(state, symbol, succCand);
			} else {
				m_RejectionCache.addInternalTransition(state, symbol, succCand);
			}
		}
		
	}
	
	private LBool computeSuccInternalSolver(IPredicate state, CodeBlock symbol, IPredicate succCand) {
		if (m_AssertedState != state || m_AssertedCodeBlock != symbol) {
			if (m_AssertedState != null) {
				m_EdgeChecker.unAssertPrecondition();
			}
			if (m_AssertedCodeBlock != symbol) {
				if (m_AssertedCodeBlock != null) {
					m_EdgeChecker.unAssertCodeBlock();
				}
				m_EdgeChecker.assertCodeBlock(symbol);
				m_AssertedCodeBlock = symbol;
			}
			m_EdgeChecker.assertPrecondition(state);
			m_AssertedState = state;
		}
		assert m_AssertedState == state && m_AssertedCodeBlock == symbol;
		LBool result = m_EdgeChecker.postInternalImplies(succCand);
		return result;
	}
	
	
	private void computeSuccCall(IPredicate state, CodeBlock symbol) {
		for (IPredicate succCand : m_Ia.getStates()) {
			LBool sat;
			if (succCand == state) {
				sat = m_EdgeChecker.sdecCallSelfloop(state, symbol);
			} else {
				sat = m_EdgeChecker.sdLazyEcCall(state, (Call) symbol, succCand);
			}
			if (sat == null) {
				sat = computeSuccCallSolver(state, symbol, succCand);
			}
			if (sat == LBool.UNSAT) {
				m_Ia.addCallTransition(state, symbol, succCand);
			} else {
				m_RejectionCache.addCallTransition(state, symbol, succCand);
			}
		}
		
	}
	
	private LBool computeSuccCallSolver(IPredicate state, CodeBlock symbol, IPredicate succCand) {
		if (m_AssertedState != state || m_AssertedCodeBlock != symbol) {
			if (m_AssertedState != null) {
				m_EdgeChecker.unAssertPrecondition();
			}
			if (m_AssertedCodeBlock != symbol) {
				if (m_AssertedCodeBlock != null) {
					m_EdgeChecker.unAssertCodeBlock();
				}
				m_EdgeChecker.assertCodeBlock(symbol);
				m_AssertedCodeBlock = symbol;
			}
			m_EdgeChecker.assertPrecondition(state);
			m_AssertedState = state;
		}
		assert m_AssertedState == state && m_AssertedCodeBlock == symbol;
		LBool result = m_EdgeChecker.postCallImplies(succCand);
		return result;
	}
	
	
	
	private void computeSuccReturn(IPredicate state, IPredicate hier, Return symbol) {
		for (IPredicate succCand : m_Ia.getStates()) {
			LBool sat = null;
			if (succCand == state || succCand == hier) {
				if (succCand == state) {
					sat = m_EdgeChecker.sdecReturnSelfloopPre(state, symbol);
				}
				if (succCand == hier && sat == null) {
					sat = m_EdgeChecker.sdecReturnSelfloopHier(hier, symbol);
				}
			} else {
				sat = m_EdgeChecker.sdLazyEcReturn(state, hier, symbol, succCand);
			}
			if (sat == null) {
				sat = computeSuccReturnSolver(state, hier, symbol, succCand);
			}
			if (sat == LBool.UNSAT) {
				m_Ia.addReturnTransition(state, hier, symbol, succCand);
			} else {
				m_RejectionCache.addReturnTransition(state, hier, symbol, succCand);
			}
		}
		
	}
	
	private LBool computeSuccReturnSolver(IPredicate state, IPredicate hier, CodeBlock symbol, IPredicate succCand) {
		if (m_AssertedHier != hier || m_AssertedState != state || m_AssertedCodeBlock != symbol) {
			if (m_AssertedHier != null) {
				m_EdgeChecker.unAssertHierPred();
			}
			if (m_AssertedState != state || m_AssertedCodeBlock != symbol) {
				if (m_AssertedState != null) {
					m_EdgeChecker.unAssertPrecondition();
				}
				if (m_AssertedCodeBlock != symbol) {
					if (m_AssertedCodeBlock != null) {
						m_EdgeChecker.unAssertCodeBlock();
					}
					m_EdgeChecker.assertCodeBlock(symbol);
					m_AssertedCodeBlock = symbol;
				}
				m_EdgeChecker.assertPrecondition(state);
				m_AssertedState = state;
			}
			m_EdgeChecker.assertHierPred(hier);
			m_AssertedHier = hier;
		}
		assert m_AssertedState == state && m_AssertedHier == hier && m_AssertedCodeBlock == symbol;
		LBool result = m_EdgeChecker.postReturnImplies(succCand);
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

}
