package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class EagerInterpolantAutomaton implements
		INestedWordAutomatonSimple<CodeBlock, IPredicate> {
	private final EdgeChecker m_EdgeChecker;
	private final NestedWordAutomaton<CodeBlock, IPredicate> m_Ia;
	private final NestedWordAutomatonCache<CodeBlock, IPredicate> m_RejectionCache;
	
	private boolean m_ComputationFinished = false;
	
	private CodeBlock m_AssertedCodeBlock;
	private IPredicate m_AssertedState;
	private IPredicate m_AssertedHier;
	
	private final Map<IPredicate,Set<CodeBlock>> m_CachedInternal = new HashMap<IPredicate,Set<CodeBlock>>();
	private final Map<IPredicate,Set<Call>> m_CachedCall = new HashMap<IPredicate,Set<Call>>();
	private final Map<IPredicate,Map<IPredicate,Set<Return>>> m_CachedReturn = new HashMap<IPredicate,Map<IPredicate,Set<Return>>>();
	
	private boolean isCachedInternal(IPredicate state, CodeBlock cb) {
		Set<CodeBlock> cbs = m_CachedInternal.get(state);
		if (cbs == null) {
			return false;
		} else {
			return cbs.contains(cb);
		}
	}
	
	private boolean isCachedCall(IPredicate state, Call cb) {
		Set<Call> cbs = m_CachedCall.get(state);
		if (cbs == null) {
			return false;
		} else {
			return cbs.contains(cb);
		}
	}
	
	private boolean isCachedReturn(IPredicate state, IPredicate hier, Return cb) {
		Map<IPredicate, Set<Return>> hier2cbs = m_CachedReturn.get(state);
		if (hier2cbs == null) {
			return false;
		} else {
			Set<Return> cbs = hier2cbs.get(hier);
			if (cbs == null) {
				return false;
			} else {
				return cbs.contains(cb);
			}
		}
	}
	
	private void reportCachedInternal(IPredicate state, CodeBlock cb) {
		Set<CodeBlock> cbs = m_CachedInternal.get(state);
		if (cbs == null) {
			cbs = new HashSet<CodeBlock>();
			m_CachedInternal.put(state, cbs);
		}
		boolean modified = cbs.add(cb);
		assert modified : "added to cache twice";
	}
	
	private void reportCachedCall(IPredicate state, Call cb) {
		Set<Call> cbs = m_CachedCall.get(state);
		if (cbs == null) {
			cbs = new HashSet<Call>();
			m_CachedCall.put(state, cbs);
		}
		boolean modified = cbs.add(cb);
		assert modified : "added to cache twice";
	}
	
	private void reportCachedReturn(IPredicate state, IPredicate hier, Return cb) {
		Map<IPredicate, Set<Return>> hier2cbs = m_CachedReturn.get(state);
		if (hier2cbs == null) {
			hier2cbs = new HashMap<IPredicate, Set<Return>>();
			m_CachedReturn.put(state, hier2cbs);
		}
		Set<Return> cbs = hier2cbs.get(hier);
		if (cbs == null) {
			cbs = new HashSet<Return>();
			hier2cbs.put(hier, cbs);
		}
		boolean modified = cbs.add(cb);
		assert modified : "added to cache twice";
	}
	

	public EagerInterpolantAutomaton(EdgeChecker edgeChecker,
			NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		super();
		m_EdgeChecker = edgeChecker;
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
		if (m_AssertedHier != null) {
			m_EdgeChecker.unAssertHierPred();
			m_AssertedHier = null;
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
		if (m_AssertedHier != null) {
			m_EdgeChecker.unAssertHierPred();
			m_AssertedHier = null;
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
	
	
	/**
	 * Announce that computation is finished. From now on this automaton
	 * returns only existing transitions but does not compute new ones.
	 */
	public void finishConstruction() {
		if (m_ComputationFinished) {
			throw new AssertionError("Computation already finished.");
		} else {
			m_ComputationFinished = true;
			clearAssertionStack();
		}
		
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
	public int size() {
		return m_Ia.size();
	}

	@Override
	public Set<CodeBlock> getAlphabet() {
		return m_Ia.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		return m_Ia.sizeInformation();
	}

	@Override
	public Set<CodeBlock> getInternalAlphabet() {
		return m_Ia.getInternalAlphabet();
	}

	@Override
	public Set<CodeBlock> getCallAlphabet() {
		return m_Ia.getCallAlphabet();
	}

	@Override
	public Set<CodeBlock> getReturnAlphabet() {
		return m_Ia.getReturnAlphabet();
	}

	@Override
	public StateFactory<IPredicate> getStateFactory() {
		return m_Ia.getStateFactory();
	}

	@Override
	public IPredicate getEmptyStackState() {
		return m_Ia.getEmptyStackState();
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		return m_Ia.getInitialStates();
	}

	@Override
	public boolean isInitial(IPredicate state) {
		return m_Ia.isInitial(state);
	}

	@Override
	public boolean isFinal(IPredicate state) {
		return m_Ia.isFinal(state);
	}

	@Override
	public Set<CodeBlock> lettersInternal(IPredicate state) {
		return getInternalAlphabet();
	}

	@Override
	public Set<CodeBlock> lettersCall(IPredicate state) {
		return getCallAlphabet();
	}

	@Override
	public Set<CodeBlock> lettersReturn(IPredicate state) {
		return getReturnAlphabet();
	}

	@Override
	public Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(
			IPredicate state, CodeBlock letter) {
		if (!isCachedInternal(state, letter) && !m_ComputationFinished) {
			computeSuccInternal(state, letter);
			reportCachedInternal(state, letter);
		}
		return m_Ia.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(
			IPredicate state) {
		for (CodeBlock letter : lettersInternal(state)) {
			if (!isCachedInternal(state, letter) && !m_ComputationFinished) {
				computeSuccInternal(state, letter);
				reportCachedInternal(state, letter);
			}
		}
		return m_Ia.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(
			IPredicate state, CodeBlock letter) {
		Call call = (Call) letter;
		if (!isCachedCall(state, call) && !m_ComputationFinished) {
			computeSuccCall(state, call);
			reportCachedCall(state, call);
		}
		return m_Ia.callSuccessors(state, call);
	}

	@Override
	public Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(
			IPredicate state) {
		for (CodeBlock letter : lettersCall(state)) {
			Call call = (Call) letter;
			if (!isCachedCall(state, call) && !m_ComputationFinished) {
				computeSuccCall(state, call);
				reportCachedCall(state, call);
			}
		}
		return m_Ia.callSuccessors(state);
	}

	@Override
	public Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSucccessors(
			IPredicate state, IPredicate hier, CodeBlock letter) {
		Return ret = (Return) letter;
		if (!isCachedReturn(state, hier, ret) && !m_ComputationFinished) {
			computeSuccReturn(state, hier, ret);
			reportCachedReturn(state, hier, ret);
		}
		return m_Ia.returnSucccessors(state, hier, ret);
	}

	@Override
	public Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSuccessorsGivenHier(
			IPredicate state, IPredicate hier) {
		for (CodeBlock letter : lettersReturn(state)) {
			Return ret = (Return) letter;
			if (!isCachedReturn(state, hier, ret) && !m_ComputationFinished) {
				computeSuccReturn(state, hier, ret);
				reportCachedReturn(state, hier, ret);
			}
		}
		return m_Ia.returnSuccessorsGivenHier(state, hier);
	}

}
