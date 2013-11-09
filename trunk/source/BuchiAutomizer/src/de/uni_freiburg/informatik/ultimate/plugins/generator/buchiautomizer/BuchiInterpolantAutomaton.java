package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NwaCacheBookkeeping;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.BuchiPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * Given a lasso annotated with predicates, construct an interpolant automaton
 * that is nearly determinisitic.
 * @author Matthias Heizmann
 *
 */
public class BuchiInterpolantAutomaton implements
		INestedWordAutomatonSimple<CodeBlock, IPredicate> {
	
	protected final static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private final SmtManager m_SmtManager;
	private final EdgeChecker m_EdgeChecker;
	private final NestedWordAutomatonCache<CodeBlock, IPredicate> m_InputSuccessorCache;
	private final NestedWordAutomatonCache<CodeBlock, IPredicate> m_RejectionCache;
	private final NwaCacheBookkeeping<CodeBlock, IPredicate> m_InputBookkeeping;
	private final NestedWordAutomatonCache<CodeBlock, IPredicate> m_Result;
	private final NwaCacheBookkeeping<CodeBlock, IPredicate> m_ResultBookkeeping;
	
	private final Set<IPredicate> m_InputStemPredicates;
	private final Set<IPredicate> m_InputLoopPredicates;
	private final IPredicate m_HondaPredicate;
	
	private final Set<IPredicate> m_ResultStemPredicates;
	private final Set<IPredicate> m_ResultLoopPredicates;
	
	private final CodeBlock m_HondaEntererStem;
	private final CodeBlock m_HondaEntererLoop;
	
	private final Map<Set<IPredicate>, IPredicate> m_InputPreds2ResultPreds = 
			new HashMap<Set<IPredicate>, IPredicate>();

	private boolean m_ComputationFinished = false;
	
	private final boolean m_ScroogeNondeterminism;
	private final boolean m_HondaBouncerStem;
	private final boolean m_HondaBouncerLoop;
	
	
	private CodeBlock m_AssertedCodeBlock;
	private IPredicate m_AssertedState;
	private IPredicate m_AssertedHier;
	

	

	public BuchiInterpolantAutomaton(SmtManager smtManager, EdgeChecker edgeChecker,
			IPredicate precondition, Set<IPredicate> stemInterpolants, 
			IPredicate hondaPredicate, 
			Set<IPredicate> loopInterpolants, CodeBlock hondaEntererStem, CodeBlock hondaEntererLoop,
			INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction,
			boolean scroogeNondeterminism, boolean hondaBouncerStem, boolean hondaBouncerLoop) {
		super();
		m_SmtManager = smtManager;
		m_EdgeChecker = edgeChecker;
		m_InputSuccessorCache = new NestedWordAutomatonCache<CodeBlock, IPredicate>(
				abstraction.getInternalAlphabet(), 
				abstraction.getCallAlphabet(), 
				abstraction.getReturnAlphabet(), 
				abstraction.getStateFactory());
		m_RejectionCache = new NestedWordAutomatonCache<CodeBlock, IPredicate>(
				abstraction.getInternalAlphabet(), 
				abstraction.getCallAlphabet(), 
				abstraction.getReturnAlphabet(), 
				abstraction.getStateFactory());
		m_Result = new NestedWordAutomatonCache<CodeBlock, IPredicate>(
				abstraction.getInternalAlphabet(), 
				abstraction.getCallAlphabet(), 
				abstraction.getReturnAlphabet(), 
				abstraction.getStateFactory());
		m_InputStemPredicates = new HashSet<IPredicate>();
		m_InputLoopPredicates = new HashSet<IPredicate>();
		m_ResultStemPredicates = new HashSet<IPredicate>();
		m_ResultLoopPredicates = new HashSet<IPredicate>();
		m_InputStemPredicates.add(precondition);
		m_ResultStemPredicates.add(precondition);
		m_Result.addState(true, false, precondition);
		m_InputSuccessorCache.addState(true, false, precondition);
		m_RejectionCache.addState(true, false, precondition);
		for (IPredicate stemPredicate : stemInterpolants) {
			if (!m_InputStemPredicates.contains(stemPredicate)) {
				m_InputStemPredicates.add(stemPredicate);
				m_InputSuccessorCache.addState(false, false, stemPredicate);
				m_RejectionCache.addState(false, false, stemPredicate);
			}
		}
		m_HondaPredicate = hondaPredicate;
		m_Result.addState(false, true, hondaPredicate);
		m_InputSuccessorCache.addState(false, true, hondaPredicate);
		m_RejectionCache.addState(false, true, hondaPredicate);
		for (IPredicate loopPredicate : loopInterpolants) {
			if (!m_InputLoopPredicates.contains(loopPredicate)) {
				m_InputLoopPredicates.add(loopPredicate);
				m_InputSuccessorCache.addState(false, false, loopPredicate);
				m_RejectionCache.addState(false, false, loopPredicate);
			}
		}
		m_InputBookkeeping = new NwaCacheBookkeeping<CodeBlock, IPredicate>();
		m_ResultBookkeeping = new NwaCacheBookkeeping<CodeBlock, IPredicate>();
		m_HondaEntererStem = hondaEntererStem;
		m_HondaEntererLoop = hondaEntererLoop;
		/**
		 * Allow a some special nondeterministic transitions. For this 
		 * additional transition the
		 * - predecessor is some stem predicate
		 * - the letter is m_HondaEntererStem
		 * - the successor is the honda state
		 */
		m_ScroogeNondeterminism = scroogeNondeterminism;
		/**
		 * If set, the nondeterministic transition from the stem predicates
		 * into the honda is only allowed for the letter m_HondaEntererStem
		 */
		m_HondaBouncerStem = hondaBouncerStem;
		/**
		 * If set, a transition from the stem predicates may only go to the
		 * honda if the letter is m_HondaEntererLoop
		 */
		m_HondaBouncerLoop = hondaBouncerLoop;
		s_Logger.info(startMessage());
	}
	
	private StringBuilder startMessage() {
		StringBuilder sb = new StringBuilder();
		if (m_ScroogeNondeterminism) {
			sb.append("Defining Buchi interpolant automaton with scrooge nondeterministic");
		} else {
			sb.append("Defining deterministic Buchi interpolant automaton ");
		}
		sb.append(m_HondaBouncerStem ? "with " : "without ");
		sb.append("honda bouncer for stem and ");
		sb.append(m_HondaBouncerLoop ? "with " : "without ");
		sb.append("honda bouncer for loop.");
		sb.append(m_InputStemPredicates.size()).append(" stem predicates ");
		sb.append(m_InputLoopPredicates.size()).append(" loop predicates ");
		return sb;
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
			s_Logger.info(exitMessage());
		}
	}
	
	private StringBuilder exitMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Resulting Buchi interpolant automaton has ");
		sb.append(m_Result.size()).append(" states ");
		sb.append(m_ResultStemPredicates.size()).append(" stem states ");
		sb.append(m_ResultLoopPredicates.size()).append(" loop states ");
		return sb;
	}


	
	private void computeSuccInternalInput(IPredicate state, CodeBlock symbol, Iterable<IPredicate> preselection) {
		for (IPredicate succCand : preselection) {
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
				m_InputSuccessorCache.addInternalTransition(state, symbol, succCand);
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
	
	
	private void computeSuccCallInput(IPredicate state, CodeBlock symbol, Iterable<IPredicate> preselection) {
		for (IPredicate succCand : preselection) {
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
				m_InputSuccessorCache.addCallTransition(state, symbol, succCand);
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
	
	
	
	private void computeSuccReturnInput(IPredicate state, IPredicate hier, Return symbol, Iterable<IPredicate> preselection) {
		for (IPredicate succCand : preselection) {
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
				m_InputSuccessorCache.addReturnTransition(state, hier, symbol, succCand);
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

	@Override
	public boolean accepts(Word<CodeBlock> word) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int size() {
		return m_Result.size();
	}

	@Override
	public Set<CodeBlock> getAlphabet() {
		return m_Result.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		return m_Result.sizeInformation();
	}

	@Override
	public Set<CodeBlock> getInternalAlphabet() {
		return m_Result.getInternalAlphabet();
	}

	@Override
	public Set<CodeBlock> getCallAlphabet() {
		return m_Result.getCallAlphabet();
	}

	@Override
	public Set<CodeBlock> getReturnAlphabet() {
		return m_Result.getReturnAlphabet();
	}

	@Override
	public StateFactory<IPredicate> getStateFactory() {
		return m_Result.getStateFactory();
	}

	@Override
	public IPredicate getEmptyStackState() {
		return m_Result.getEmptyStackState();
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		return m_Result.getInitialStates();
	}

	@Override
	public boolean isInitial(IPredicate state) {
		return m_Result.isInitial(state);
	}

	@Override
	public boolean isFinal(IPredicate state) {
		return m_Result.isFinal(state);
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
	
	/**
	 * Get the predicate of the output automaton that represents a set of states
	 * from the input automaton. If this predicates does not yet exists, 
	 * construct it an put it to the given equivalence class. 
	 * @param inputPreds set of IPredicats from the input automaton
	 * @param equivalenceClass of the resulting automaton to that the resulting
	 * predicate will belong (either stem predicates or loop predicates)
	 */
	private IPredicate getOrConstructPredicate(Set<IPredicate> inputPreds, Set<IPredicate> equivalenceClass) {
		IPredicate resultPred;
		assert !inputPreds.isEmpty();
		if (inputPreds.size() == 1) {
			resultPred = inputPreds.iterator().next();

		} else {
			resultPred = m_InputPreds2ResultPreds.get(inputPreds);
			if (resultPred == null) {
				resultPred = m_SmtManager.newBuchiPredicate(inputPreds);
				m_InputPreds2ResultPreds.put(inputPreds,resultPred);
			}
			for (IPredicate pred : inputPreds) {
				assert m_InputStemPredicates.contains(pred) || 
						m_InputLoopPredicates.contains(pred);
			}
		}
		assert resultPred != m_HondaPredicate;
		if (!equivalenceClass.contains(resultPred)) {
			equivalenceClass.add(resultPred);
			m_Result.addState(false, false, resultPred);
		}
		return resultPred;
	}

	@Override
	public Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(
			IPredicate state, CodeBlock letter) {
		if (!m_ResultBookkeeping.isCachedInternal(state, letter) && !m_ComputationFinished) {
			computeSuccInternal(state, letter);
			m_ResultBookkeeping.reportCachedInternal(state, letter);
		}
		return m_Result.internalSuccessors(state, letter);
	}


	@Override
	public Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(
			IPredicate state) {
		for (CodeBlock letter : lettersInternal(state)) {
			if (!m_ResultBookkeeping.isCachedInternal(state, letter) && !m_ComputationFinished) {
				computeSuccInternal(state, letter);
				m_ResultBookkeeping.reportCachedInternal(state, letter);
			}
		}
		return m_Result.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(
			IPredicate state, CodeBlock letter) {
		Call call = (Call) letter;
		if (!m_ResultBookkeeping.isCachedCall(state, call) && !m_ComputationFinished) {
			computeSuccCall(state, call);
			m_ResultBookkeeping.reportCachedCall(state, call);
		}
		return m_Result.callSuccessors(state, call);
	}

	@Override
	public Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(
			IPredicate state) {
		for (CodeBlock letter : lettersCall(state)) {
			Call call = (Call) letter;
			if (!m_ResultBookkeeping.isCachedCall(state, call) && !m_ComputationFinished) {
				computeSuccCall(state, call);
				m_ResultBookkeeping.reportCachedCall(state, call);
			}
		}
		return m_Result.callSuccessors(state);
	}

	@Override
	public Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSucccessors(
			IPredicate state, IPredicate hier, CodeBlock letter) {
		Return ret = (Return) letter;
		if (!m_ResultBookkeeping.isCachedReturn(state, hier, ret) && !m_ComputationFinished) {
			computeSuccReturn(state, hier, ret);
			m_ResultBookkeeping.reportCachedReturn(state, hier, ret);
		}
		return m_Result.returnSucccessors(state, hier, ret);
	}

	@Override
	public Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSuccessorsGivenHier(
			IPredicate state, IPredicate hier) {
		for (CodeBlock letter : lettersReturn(state)) {
			Return ret = (Return) letter;
			if (!m_ResultBookkeeping.isCachedReturn(state, hier, ret) && !m_ComputationFinished) {
				computeSuccReturn(state, hier, ret);
				m_ResultBookkeeping.reportCachedReturn(state, hier, ret);
			}
		}
		return m_Result.returnSuccessorsGivenHier(state, hier);
	}
	
	
	private void computeSuccInternal(IPredicate resPred, CodeBlock letter) {
		if (m_ResultStemPredicates.contains(resPred)) {
			boolean leadsToHonda = false;
			if (!m_HondaBouncerStem || letter.equals(m_HondaEntererStem)) {
				LBool sat = computeSuccInternalSolver(resPred, letter, m_HondaPredicate);
				if (sat == LBool.UNSAT) {
					leadsToHonda = true;
					m_Result.addInternalTransition(resPred, letter, m_HondaPredicate);
				}
			}
			if (!leadsToHonda || m_ScroogeNondeterminism) {
				Set<IPredicate> succs = addSuccInternal(resPred, letter, m_InputStemPredicates);
				if (!succs.isEmpty()) {
					IPredicate stemSucc = getOrConstructPredicate(succs, m_ResultStemPredicates);
					m_Result.addInternalTransition(resPred, letter, stemSucc);
				}
			}
		} else {
			assert (m_ResultLoopPredicates.contains(resPred) || resPred == m_HondaPredicate);
			boolean leadsToHonda = false;
			if (!m_HondaBouncerLoop || letter.equals(m_HondaEntererLoop)) {
				LBool sat = computeSuccInternalSolver(resPred, letter, m_HondaPredicate);
				if (sat == LBool.UNSAT) {
					m_Result.addInternalTransition(resPred, letter, m_HondaPredicate);
					leadsToHonda = true;
				}
			}
			if (!leadsToHonda) {
				Set<IPredicate> succs = addSuccInternal(resPred, letter, m_InputLoopPredicates);
				if (!succs.isEmpty()) {
					IPredicate stemSucc = getOrConstructPredicate(succs, m_ResultLoopPredicates);
					m_Result.addInternalTransition(resPred, letter, stemSucc);
				}
			}
		}

	}
	
	/**
	 * Returns a set of input predicates such each predicate p
	 * - Hoare triple {resPred} letter {p} is valid
	 * - is contained in succCand
	 */
	private Set<IPredicate> addSuccInternal(IPredicate resPred, CodeBlock letter, Iterable<IPredicate> succCand) {
		HashSet<IPredicate> succs = new HashSet<IPredicate>();
		Collection<IPredicate> inputPredicates;
		if (resPred instanceof BuchiPredicate) {
			inputPredicates = ((BuchiPredicate) resPred).getConjuncts();
		} else {
			assert (resPred instanceof BasicPredicate);
			inputPredicates = new ArrayList<IPredicate>(1);
			inputPredicates.add(resPred);
		}
		for (IPredicate inputPred : inputPredicates) {
			if (!m_InputBookkeeping.isCachedInternal(inputPred, letter)) {
				computeSuccInternalInput(inputPred, letter, succCand);
				m_InputBookkeeping.reportCachedInternal(inputPred, letter);
			}
			Collection<IPredicate> inputPredSuccs = m_InputSuccessorCache.succInternal(inputPred, letter);
			if (inputPredSuccs != null) {
				succs.addAll(inputPredSuccs);
			}
		}
		return succs;
	}
	
	

	private void computeSuccCall(IPredicate resPred, CodeBlock letter) {
		if (m_ResultStemPredicates.contains(resPred)) {
			boolean leadsToHonda = false;
			if (!m_HondaBouncerStem || letter.equals(m_HondaEntererStem)) {
				LBool sat = computeSuccCallSolver(resPred, letter, m_HondaPredicate);
				if (sat == LBool.UNSAT) {
					leadsToHonda = true;
					m_Result.addCallTransition(resPred, letter, m_HondaPredicate);
				}
			}
			if (!leadsToHonda || m_ScroogeNondeterminism) {
				Set<IPredicate> succs = addSuccCall(resPred, letter, m_InputStemPredicates);
				if (!succs.isEmpty()) {
					IPredicate stemSucc = getOrConstructPredicate(succs, m_ResultStemPredicates);
					m_Result.addCallTransition(resPred, letter, stemSucc);
				}
			}

		} else {
			assert (m_ResultLoopPredicates.contains(resPred) || resPred == m_HondaPredicate);
			boolean hondaTransition = false;
			if (!m_HondaBouncerLoop || letter.equals(m_HondaEntererLoop)) {
				LBool sat = computeSuccCallSolver(resPred, letter, m_HondaPredicate);
				if (sat == LBool.UNSAT) {
					m_Result.addCallTransition(resPred, letter, m_HondaPredicate);
					hondaTransition = true;
				}
			}
			if (!hondaTransition) {
				Set<IPredicate> succs = addSuccCall(resPred, letter, m_InputLoopPredicates);
				if (!succs.isEmpty()) {
					IPredicate stemSucc = getOrConstructPredicate(succs, m_ResultLoopPredicates);
					m_Result.addCallTransition(resPred, letter, stemSucc);
				}
			}
		}

	}
	
	/**
	 * Returns a set of input predicates such each predicate p
	 * - Hoare triple {resPred} letter {p} is valid
	 * - is contained in succCand
	 */
	private Set<IPredicate> addSuccCall(IPredicate resPred, CodeBlock letter, Iterable<IPredicate> succCand) {
		HashSet<IPredicate> succs = new HashSet<IPredicate>();
		Collection<IPredicate> inputPredicates;
		if (resPred instanceof BuchiPredicate) {
			inputPredicates = ((BuchiPredicate) resPred).getConjuncts();
		} else {
			assert (resPred instanceof BasicPredicate);
			inputPredicates = new ArrayList<IPredicate>(1);
			inputPredicates.add(resPred);
		}
		for (IPredicate inputPred : inputPredicates) {
			if (!m_InputBookkeeping.isCachedCall(inputPred, letter)) {
				computeSuccCallInput(inputPred, letter, succCand);
				m_InputBookkeeping.reportCachedCall(inputPred, letter);
			}
			Collection<IPredicate> inputPredSuccs = m_InputSuccessorCache.succCall(inputPred, letter);
			if (inputPredSuccs != null) {
				succs.addAll(inputPredSuccs);
			}
		}
		return succs;
	}
	
	
	
	private void computeSuccReturn(IPredicate resPred, IPredicate resHier, CodeBlock letter) {
		if (m_ResultStemPredicates.contains(resPred)) {
			boolean leadsToHonda = false;
			if (!m_HondaBouncerStem || letter.equals(m_HondaEntererStem)) {
				LBool sat = computeSuccReturnSolver(resPred, resHier, letter, m_HondaPredicate);
				if (sat == LBool.UNSAT) {
					leadsToHonda = true;
					m_Result.addReturnTransition(resPred, resHier, letter, m_HondaPredicate);
				}
			}
			if (!leadsToHonda || m_ScroogeNondeterminism) {
				Set<IPredicate> succs = addSuccReturn(resPred, resHier, letter, m_InputStemPredicates);
				if (!succs.isEmpty()) {
					IPredicate stemSucc = getOrConstructPredicate(succs, m_ResultStemPredicates);
					m_Result.addReturnTransition(resPred, resHier, letter, stemSucc);
				}
			}
		} else {
			assert (m_ResultLoopPredicates.contains(resPred) || resPred == m_HondaPredicate);
			boolean hondaTransition = false;
			if (!m_HondaBouncerLoop || letter.equals(m_HondaEntererLoop)) {
				LBool sat = computeSuccReturnSolver(resPred, resHier, letter, m_HondaPredicate);
				if (sat == LBool.UNSAT) {
					m_Result.addReturnTransition(resPred, resHier, letter, m_HondaPredicate);
					hondaTransition = true;
				}
			}
			if (!hondaTransition) {
				Set<IPredicate> succs = addSuccReturn(resPred, resHier, letter, m_InputLoopPredicates);
				if (!succs.isEmpty()) {
					IPredicate stemSucc = getOrConstructPredicate(succs, m_ResultLoopPredicates);
					m_Result.addReturnTransition(resPred, resHier, letter, stemSucc);
				}
			}


		}

	}
	
	private Set<IPredicate> addSuccReturn(IPredicate resPred, IPredicate resHier, 
			CodeBlock letter, Iterable<IPredicate> succCand) {
		HashSet<IPredicate> succs = new HashSet<IPredicate>();
		Collection<IPredicate> inputPredicates;
		if (resPred instanceof BuchiPredicate) {
			inputPredicates = ((BuchiPredicate) resPred).getConjuncts();
		} else {
			assert (resPred instanceof BasicPredicate);
			inputPredicates = new ArrayList<IPredicate>(1);
			inputPredicates.add(resPred);
		}
		Collection<IPredicate> inputHiers;
		if (resHier instanceof BuchiPredicate) {
			inputHiers = ((BuchiPredicate) resHier).getConjuncts();
		} else {
			assert (resHier instanceof BasicPredicate);
			inputHiers = new ArrayList<IPredicate>(1);
			inputHiers.add(resHier);
		}
		for (IPredicate inputPred : inputPredicates) {
			for (IPredicate inputHier : inputHiers) {
				if (!m_InputBookkeeping.isCachedReturn(inputPred, inputHier, letter)) {
					computeSuccReturnInput(inputPred, inputHier, (Return) letter, succCand);
					m_InputBookkeeping.reportCachedReturn(inputPred, inputHier, letter);
				}
				Collection<IPredicate> inputPredSuccs = 
						m_InputSuccessorCache.succReturn(inputPred, inputHier, letter);
				if (inputPredSuccs != null) {
					succs.addAll(inputPredSuccs);
				}
			}
		}
		return succs;
	}



	public NestedWordAutomatonCache<CodeBlock, IPredicate> getAugmentedInputAutomaton() {
		return m_InputSuccessorCache;
	}
	
	
	@Override
	public String toString() {
		if (m_ComputationFinished) {
			return (new AtsDefinitionPrinter<String,String>("nwa", this)).getDefinitionAsString();
		} else {
			return "automaton under construction";
		}
	}

}
