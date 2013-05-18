package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.osgi.framework.internal.core.Msg;

import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class PostDeterminizer 
		implements IStateDeterminizer<CodeBlock, IPredicate> {
	
	protected final SmtManager m_SmtManager;
	private final TAPreferences m_TaPreferences;
	protected final NestedWordAutomaton<CodeBlock, IPredicate> m_Ia;
	private final StateFactory<IPredicate> m_StateFactory;
	private final boolean m_Eager;
	public int m_AnswerInternalSolver = 0;
	public int m_AnswerInternalAutomaton = 0;
	public int m_AnswerInternalCache = 0;
	public int m_AnswerCallSolver = 0;
	public int m_AnswerCallAutomaton = 0;
	public int m_AnswerCallCache = 0;
	public int m_AnswerReturnSolver = 0;
	public int m_AnswerReturnAutomaton = 0;
	public int m_AnswerReturnCache = 0;

	protected final NestedWordAutomaton<CodeBlock, IPredicate> m_RejectionCache;

	private IPredicate m_IaTrueState;
	private IPredicate m_IaFalseState;
	private DeterminizedState<CodeBlock, IPredicate> m_ResultFinalState;
	private final boolean m_UseDoubleDeckers = false;
	
	private CodeBlock m_AssertedCodeBlock;
	private IPredicate m_AssertedState;
	private IPredicate m_AssertedHier;
	
	protected final SmtManager.EdgeChecker m_EdgeChecker;
	

	public PostDeterminizer(SmtManager mSmtManager,
			TAPreferences taPreferences,
			NestedWordAutomaton<CodeBlock, IPredicate> mNwa,
			boolean eager) {
		super();
		m_SmtManager = mSmtManager;
		m_EdgeChecker = mSmtManager.new EdgeChecker();
		m_TaPreferences = taPreferences;
		m_Ia = mNwa;
		m_StateFactory = mNwa.getStateFactory();
		m_Eager = eager;
		
		
		for (IPredicate state : 
			m_Ia.getInitialStates()) {
			if (m_IaTrueState == null) {
				m_IaTrueState = state;
			}
			else {
				throw new IllegalArgumentException("Interpolant Automaton" +
				" must have one inital state");
			}
		}
		
		for (IPredicate state : 
			m_Ia.getFinalStates()) {
			if (m_IaFalseState == null) {
				m_IaFalseState = state;
			}
			else {
				throw new IllegalArgumentException("Interpolant Automaton" +
				" must have one final state");
			}
		}
		
		m_ResultFinalState = 
			new DeterminizedState<CodeBlock, IPredicate>(m_Ia);
		m_ResultFinalState.addPair(m_Ia.getEmptyStackState(), m_IaFalseState, m_Ia);
		
		
		m_RejectionCache = new NestedWordAutomaton<CodeBlock, IPredicate>(
				mNwa.getInternalAlphabet(), 
				mNwa.getCallAlphabet(),
				mNwa.getReturnAlphabet(),
				m_StateFactory);
		for (IPredicate state : m_Ia.getStates()) {
			m_RejectionCache.addState(false, false, state);
		}
		
	}
	
	
	
	
	public NestedWordAutomaton<CodeBlock, IPredicate> getRejectionCache() {
		return m_RejectionCache;
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
	public DeterminizedState<CodeBlock, IPredicate>  internalSuccessor(
			DeterminizedState<CodeBlock, IPredicate>  detState,
			CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			return m_ResultFinalState;
		}
		DeterminizedState<CodeBlock, IPredicate>  detSucc = 
			new DeterminizedState<CodeBlock, IPredicate> (m_Ia);
		
		for (IPredicate  downState : detState.getDownStates()) {
			Set<IPredicate> upStates = detState.getUpStates(downState);
			for (IPredicate  upState : upStates) {
				//Add states that we may add because the automaton says so
				Iterable<IPredicate> internalSuccs = m_Ia.succInternal(upState,symbol);
				for (IPredicate  upSucc : internalSuccs) {
					detSucc.addPair(downState,upSucc, m_Ia);
				}
				
				//We may always add the true state
				detSucc.addPair(downState, m_IaTrueState, m_Ia);
				
				Set<IPredicate> knownUpSuccs = detSucc.getUpStates(downState);
				if (knownUpSuccs.contains(m_IaFalseState)) {
					clearAssertionStack();
					return m_ResultFinalState;
				}
				
				//Add selfloop if automaton says "no successors!" and upState
				// is not "true"
				if (!internalSuccs.iterator().hasNext() && upState != m_IaTrueState) {
					if (inductiveInternal(upState,symbol,upState)) {
						detSucc.addPair(downState, upState, m_Ia);
					}
				}
				
				// Check Edge to False
				if (inductiveInternalTargetFalse(upState, symbol)) {
					clearAssertionStack();
					return m_ResultFinalState;
				}
				
				//Add remaining states
				if (m_Eager) {
					for (IPredicate  upSucc : moreInternalSuccs(upState,symbol,knownUpSuccs)) {
						detSucc.addPair(downState,upSucc, m_Ia);
					}
				}
				
				//If falseState is contained we return the unique accepting
				//state of the result, (exploiting concat sigma star closure)
				if (knownUpSuccs.contains(m_IaFalseState)) {
					clearAssertionStack();
					return m_ResultFinalState;
				}
			}
		}

		clearAssertionStack();
		if (m_TaPreferences.computeHoareAnnotation()) {
			assert(m_SmtManager.isInductive(detState.getContent(m_StateFactory), 
						symbol, 
						detSucc.getContent(m_StateFactory)) == Script.LBool.UNSAT ||
					m_SmtManager.isInductive(detState.getContent(m_StateFactory), 
						symbol, 
						detSucc.getContent(m_StateFactory)) == Script.LBool.UNKNOWN);
		}
		assert detSucc.getDownStates().size() < 2;
		return detSucc;	
	}
	
	@Override
	public DeterminizedState<CodeBlock, IPredicate>  callSuccessor(
			DeterminizedState<CodeBlock, IPredicate>  detState, 
			CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			return m_ResultFinalState;
		}
		DeterminizedState<CodeBlock, IPredicate>  detSucc = 
			new DeterminizedState<CodeBlock, IPredicate> (m_Ia);
		
		for (IPredicate  downState : detState.getDownStates()) {
			Set<IPredicate> upStates = detState.getUpStates(downState);
			for (IPredicate  upState : upStates) {
				Iterable<IPredicate> callSuccs = m_Ia.succCall(upState,symbol);
				//Add states that we may add because the automaton says so
				for (IPredicate  upSucc : callSuccs) {
					if (m_UseDoubleDeckers) {
						detSucc.addPair(upState,upSucc, m_Ia);
					} else {
						detSucc.addPair(m_Ia.getEmptyStackState(),upSucc, m_Ia);
					}
				}

				//Add selfloop if automaton says "no successors!" and upState
				// is not "true"
				if (!callSuccs.iterator().hasNext() && upState != m_IaTrueState) {
					if (inductiveCall(upState,(Call) symbol,upState)) {
						if (m_UseDoubleDeckers) {
							detSucc.addPair(upState,upState, m_Ia);
						} else {
							detSucc.addPair(m_Ia.getEmptyStackState(),upState, m_Ia);
						}
					}
				}
				
				//We may always add the true state
				if (m_UseDoubleDeckers) {
					detSucc.addPair(upState,m_IaTrueState, m_Ia);
				} else {
					detSucc.addPair(m_Ia.getEmptyStackState(),m_IaTrueState, m_Ia);
				}
				
				Set<IPredicate> knownUpSuccs;
				if (m_UseDoubleDeckers) {
					knownUpSuccs = detSucc.getUpStates(upState);
				} else {
					knownUpSuccs = detSucc.getUpStates(m_Ia.getEmptyStackState());
				}
				
				
				//Add remaining states
				if (m_Eager) {
					for (IPredicate  upSucc : moreCallSuccs(upState,(Call) symbol,knownUpSuccs)) {
						if (m_UseDoubleDeckers) {
							detSucc.addPair(upState,upSucc, m_Ia);
						} else {
							detSucc.addPair(m_Ia.getEmptyStackState(),upSucc, m_Ia);
						}
					}
				}
				
				//If falseState is contained we return the unique accepting
				//state of the result, (exploiting concat sigma star closure)
				if (knownUpSuccs.contains(m_IaFalseState)) {
					return m_ResultFinalState;
				}
//				//For better performance we remove the true predicate if this is
//				//not the only predicate
//				Set<Predicate> succUpStates = detSucc.getUpStates(upState);
//				if (succUpStates.size() > 1) {
//					succUpStates.remove(m_IaTrueState);
//				}
			}

		}
		clearAssertionStack();
		if (m_TaPreferences.computeHoareAnnotation()) {
			assert(m_SmtManager.isInductiveCall(detState.getContent(m_StateFactory), 
						(Call) symbol, 
						detSucc.getContent(m_StateFactory)) == Script.LBool.UNSAT ||
					m_SmtManager.isInductiveCall(detState.getContent(m_StateFactory), 
						(Call) symbol, 
						detSucc.getContent(m_StateFactory)) == Script.LBool.UNKNOWN);
		}
		assert detSucc.getDownStates().size() < 2;
		return detSucc;	
	}

	@Override
	public DeterminizedState<CodeBlock, IPredicate>  returnSuccessor(
			DeterminizedState<CodeBlock, IPredicate>  detState,
			DeterminizedState<CodeBlock, IPredicate>  detHier,
			CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			return m_ResultFinalState;
		}
		if (detHier == m_ResultFinalState) {
			return m_ResultFinalState;
		}
		
		DeterminizedState<CodeBlock, IPredicate>  detSucc = 
			new DeterminizedState<CodeBlock, IPredicate> (m_Ia);
		
		for (IPredicate  downLinPred : detHier.getDownStates()) {
			for (IPredicate  upLinPred : detHier.getUpStates(downLinPred)) {
		
				Set<IPredicate > upStates;
				if (m_UseDoubleDeckers) {
					upStates = detState.getUpStates(upLinPred);
				} else {
					upStates = detState.getUpStates(m_Ia.getEmptyStackState());
				}
				
				if (upStates == null) continue;
				for (IPredicate  upState : upStates) {
					//Add states that we may add because the automaton says so
					Iterable<IPredicate> returnSuccs = m_Ia.succReturn(upState,upLinPred,symbol);
					for (IPredicate  upSucc : returnSuccs) {
						detSucc.addPair(downLinPred,upSucc, m_Ia);
					}

					//Add selfloop at hier if automaton says 
					// "no successors!" and upState and hier ist not "true"
					if (!returnSuccs.iterator().hasNext() && upLinPred != m_IaTrueState) {
						if (inductiveReturn(upState, upLinPred, (Return) symbol, upLinPred)) {
							detSucc.addPair(downLinPred, upLinPred, m_Ia);
						}
					}

					//Add selfloop at upState if automaton says
					// "no successors!" and upState is not "true"
					if (!returnSuccs.iterator().hasNext() && upState != m_IaTrueState) {
						if (inductiveReturn(upState, upLinPred, (Return) symbol, upState)) {
							detSucc.addPair(downLinPred, upState, m_Ia);
						}
					}

					//We may always add the true state
					detSucc.addPair(downLinPred, m_IaTrueState, m_Ia);

					Set<IPredicate> knownUpSuccs = detSucc.getUpStates(downLinPred);

					//Add remaining states
					if (m_Eager) {
						for (IPredicate  upSucc : moreReturnSuccs(upState, upLinPred, (Return) symbol, knownUpSuccs)) {
							detSucc.addPair(downLinPred,upSucc, m_Ia);
						}
					}

					//If falseState is contained we return the unique accepting
					//state of the result, (exploiting concat sigma star closure)
					if (knownUpSuccs.contains(m_IaFalseState)) {
						clearAssertionStack();
						return m_ResultFinalState;
					}
				}
				//For better performance we remove the true predicate if this is
				//not the only predicate
//				Set<Predicate> succUpStates = detSucc.getUpStates(downLinPred);
//				if (succUpStates.size() > 1) {
//					succUpStates.remove(m_IaTrueState);
//				}
			}
		}
		clearAssertionStack();
		if (m_TaPreferences.computeHoareAnnotation()) {
			assert(m_SmtManager.isInductiveReturn(detState.getContent(m_StateFactory),
					detHier.getContent(m_StateFactory),
					(Return) symbol, 
					detSucc.getContent(m_StateFactory)) == Script.LBool.UNSAT ||
					m_SmtManager.isInductiveReturn(detState.getContent(m_StateFactory),
						detHier.getContent(m_StateFactory),
						(Return) symbol, 
						detSucc.getContent(m_StateFactory)) == Script.LBool.UNKNOWN);
		}
		assert detSucc.getDownStates().size() < 2;
		return detSucc;	
	}
	
	
	
	
	
	/**
	 * Return all states succ such that (state, symbol, succ) is inductive, but
	 * succ is not contained in knownSuccStates.
	 */
	private Collection<IPredicate> moreInternalSuccs(
			IPredicate state,
			CodeBlock symbol,
			Set<IPredicate> knownSuccStates) {
		ArrayList<IPredicate> succs = new ArrayList<IPredicate>();
		for (IPredicate succCandidate : m_Ia.getStates()) {
			if (succCandidate == m_IaTrueState || 
					succCandidate == m_IaFalseState
//			|| succCandidate == state
					) {
				//these cases have already been checked
				continue;
			}
			
			if (knownSuccStates.contains(succCandidate)) {
				m_AnswerInternalAutomaton++;
			}
			else {
				if (inductiveInternal(state, symbol, succCandidate)) {
					succs.add(succCandidate);
				}
			}
		}
		return succs;
	}
	
	
	
	/**
	 * Return all states succ such that (state, symbol, succ) is inductive, but
	 * succ is not contained in knownSuccStates.
	 */
	private Collection<IPredicate> moreCallSuccs(
			IPredicate state,
			Call symbol,
			Set<IPredicate> knownSuccStates) {
		ArrayList<IPredicate> succs = new ArrayList<IPredicate>();
		for (IPredicate succCandidate : m_Ia.getStates()) {
			if (succCandidate == m_IaTrueState || 
					succCandidate == m_IaFalseState) {
				//these states have already been added
				continue;
			}
			if (knownSuccStates.contains(succCandidate)) {
				m_AnswerCallAutomaton++;
			}
			else {
				if (inductiveCall(state, symbol, succCandidate)) {
					succs.add(succCandidate);
				}
			}
		}
		return succs;
	}
	
	
	/**
	 * Return all states succ such that (state, hier, symbol, succ) is
	 * inductive, but succ is not contained in knownSuccStates.
	 */
	private Collection<IPredicate> moreReturnSuccs(
			IPredicate state,
			IPredicate hier,
			Return symbol,
			Set<IPredicate> knownSuccStates) {
		ArrayList<IPredicate> succs = new ArrayList<IPredicate>();
		for (IPredicate succCandidate : m_Ia.getStates()) {
			if (succCandidate == m_IaTrueState || 
					succCandidate == m_IaFalseState) {
				//these states have already been added
				continue;
			}
			if (knownSuccStates.contains(succCandidate)) {
				m_AnswerReturnAutomaton++;
			}
			else {
				if (inductiveReturn(state, hier, symbol, succCandidate)) {
					succs.add(succCandidate);
				}
			}
		}
		return succs;
	}
	


	
	/**
	 * Returns true iff (state,symbol,succ) is inductive. Fist the rejection
	 * cache is queried if there was already a non-yes answer before, if we have
	 * a cache miss the solver is queried for a yes/no/unknown-answer. 
	 */
	protected boolean inductiveInternal(
			IPredicate  state,
			CodeBlock symbol,
			IPredicate  succ) {
		if (m_RejectionCache.containsInternalTransition(state, symbol, succ)) {
			m_AnswerInternalCache++;
			return false;
		}
		LBool sat = null;
		if (state == succ) {
			sat = m_EdgeChecker.sdecInternalSelfloop(state, symbol);
		}
		if (sat == null) {
			sat = m_EdgeChecker.sdLazyEcInteral(state, symbol, succ);
		}		
		if (sat == null) {
			//		LBool sat = m_SmtManager.isInductive(state, symbol, succ);
			if (m_AssertedCodeBlock == null) {
				m_EdgeChecker.assertCodeBlock(symbol);
				m_AssertedCodeBlock = symbol;
			}
			if (m_AssertedState != null && m_AssertedState != state) {
				m_EdgeChecker.unAssertPrecondition();
			}
			if (m_AssertedState != state) {
				m_EdgeChecker.assertPrecondition(state);
				m_AssertedState = state;
			}
			sat = m_EdgeChecker.postInternalImplies(succ);
		}
		
		m_AnswerInternalSolver++;
		if (sat == Script.LBool.UNSAT) {
			m_Ia.addInternalTransition(state, symbol, succ);
			return true;
		}
		else {
			assert symbol.getTransitionFormula().isInfeasible() != Infeasibility.INFEASIBLE;
			m_RejectionCache.addInternalTransition(state, symbol, succ);
			return false;	
		}
	}
	
	private boolean inductiveInternalTargetFalse(
			IPredicate  state,
			CodeBlock symbol) {
		LBool sat = m_EdgeChecker.sdecInternalToFalse(state, symbol);
		if (sat == null) {
			return inductiveInternal(state, symbol, m_IaFalseState);
		} else {
			return sat == LBool.UNSAT;
		}
	}
	
//	private boolean inductiveInternalSelfloop(
//			Predicate  state,
//			CodeBlock symbol) {
//		LBool sat = m_EdgeChecker.sdecInternalSelfloop(state, symbol);
//		if (sat == null) {
//			return inductiveInternal(state, symbol, m_IaFalseState);
//		} else {
//			return sat == LBool.UNSAT;
//		}
//	}
	
	


	/**
	 * Returns true iff (state,symbol,succ) is inductive. Fist the rejection
	 * cache is queried if there was already a non-yes answer before, if we have
	 * a cache miss the solver is queried for a yes/no/unknown-answer. 
	 */
	private boolean inductiveCall(
			IPredicate  state,
			Call symbol,
			IPredicate  succ) {
		if (m_RejectionCache.containsCallTransition(state, symbol, succ)) {
			m_AnswerCallCache++;
			return false;
		}
		LBool sat = null;
		if (state == succ) {
			sat = m_EdgeChecker.sdecCallSelfloop(state, symbol);
		}
		if (state == null) {
			sat = m_EdgeChecker.sdLazyEcCall(state, symbol, succ);
		}
		if (sat == null) {
			// sat = m_SmtManager.isInductiveCall(state, symbol, succ);
			if (m_AssertedCodeBlock == null) {
				m_EdgeChecker.assertCodeBlock(symbol);
				m_AssertedCodeBlock = symbol;
			}
			if (m_AssertedState != null && m_AssertedState != state) {
				m_EdgeChecker.unAssertPrecondition();
			}
			if (m_AssertedState != state) {
				m_EdgeChecker.assertPrecondition(state);
				m_AssertedState = state;
			}
			sat = m_EdgeChecker.postCallImplies(succ);
		}
		m_AnswerCallSolver++;
		if (sat == Script.LBool.UNSAT) {
			m_Ia.addCallTransition(state, symbol, succ);
			return true;
		}
		else {
			m_RejectionCache.addCallTransition(state, symbol, succ);
			return false;	
		}
	}

	
	/**
	 * Returns true iff (state,symbol,succ) is inductive. Fist the rejection
	 * cache is queried if there was already a non-yes answer before, if we have
	 * a cache miss the solver is queried for a yes/no/unknown-answer. 
	 */
	private boolean inductiveReturn(
			IPredicate  state,
			IPredicate hier,
			Return symbol,
			IPredicate  succ) {
		if (m_RejectionCache.containsReturnTransition(state, hier, symbol, succ)) {
			m_AnswerReturnCache++;
			return false;
		}
		LBool sat = null;
		if (state == succ) {
			sat = m_EdgeChecker.sdecReturnSelfloopPre(state, symbol);
		}
		if (sat == null && hier == succ) {
			sat = m_EdgeChecker.sdecReturnSelfloopHier(hier, symbol);
		}
		if (sat == null) {
			sat = m_EdgeChecker.sdLazyEcReturn(state, hier, symbol, succ);
		}
		if (sat == null) {
//			sat = m_SmtManager.isInductiveReturn(state, hier, symbol, succ);
			if (m_AssertedCodeBlock == null) {
				m_EdgeChecker.assertCodeBlock(symbol);
				m_AssertedCodeBlock = symbol;
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
			sat = m_EdgeChecker.postReturnImplies(succ);
		} 
		m_AnswerReturnSolver++;
		if (sat == Script.LBool.UNSAT) {
			m_Ia.addReturnTransition(state, hier, symbol, succ);
			return true;
		}
		else {
			m_RejectionCache.addReturnTransition(state, hier, symbol, succ);
			return false;	
		}
	}
	
	

	
	
	
	
	
	@Override
	public int getMaxDegreeOfNondeterminism() {
		// TODO Auto-generated method stub
		return 0;
	}


	/**
	 * Returns true iff the variables occuring in state are disjoint from the
	 * inVars of CodeBlock letter.
	 * @param state
	 * @param symbol
	 * @return
	 */
	private boolean varsDisjoinedFormInVars(IPredicate state, CodeBlock letter) {
		for (BoogieVar bv : state.getVars()) {
			if (letter.getTransitionFormula().getInVars().containsKey(bv)) {
				return false;
			}
		}
		return true;
	}








}
