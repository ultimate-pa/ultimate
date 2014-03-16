package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.HashRelation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NwaCacheBookkeeping;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Given a lasso annotated with predicates, construct an interpolant automaton
 * that is nearly determinisitic.
 * @author Matthias Heizmann
 *
 */
public class BuchiInterpolantAutomatonBouncer extends AbstractInterpolantAutomaton {
	
	private final NwaCacheBookkeeping<CodeBlock, IPredicate> m_ResultBookkeeping = 
			new NwaCacheBookkeeping<CodeBlock, IPredicate>();
	
	@Deprecated
	private final Set<IPredicate> m_InputStemPredicates = new HashSet<IPredicate>();
	@Deprecated
	private final Set<IPredicate> m_InputLoopPredicates = new HashSet<IPredicate>();
	
	/**
	 * Input predicates without auxiliary rank variables.
	 */
	private final Set<IPredicate> m_InputAuxFreePredicates = new HashSet<IPredicate>();

	/**
	 * Input predicates with auxiliary rank variables.
	 */
	private final Set<IPredicate> m_InputWithAuxPredicates = new HashSet<IPredicate>();
	
//	private final IPredicate m_HondaPredicate;
	
	private final CodeBlock m_HondaEntererStem;
	private final CodeBlock m_HondaEntererLoop;

	private final boolean m_ScroogeNondeterminismStem;
	private final boolean m_ScroogeNondeterminismLoop;
	private final boolean m_HondaBouncerStem;
	private final boolean m_HondaBouncerLoop;
	
	private final BinaryStatePredicateManager m_Bspm;
	
	
	private final Map<Set<IPredicate>, IPredicate> m_StemInputPreds2ResultPreds = 
			new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> m_StemResPred2InputPreds = 
			new HashRelation<IPredicate, IPredicate>();
	
	private final Map<Set<IPredicate>, IPredicate> m_LoopInputPreds2ResultPreds = 
			new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> m_LoopResPred2InputPreds = 
			new HashRelation<IPredicate, IPredicate>();
	
	private final Map<Set<IPredicate>, IPredicate> m_AcceptingInputPreds2ResultPreds = 
			new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> m_AcceptingResPred2InputPreds = 
			new HashRelation<IPredicate, IPredicate>();
	
	private final Map<Set<IPredicate>, IPredicate> m_RankEqInputPreds2ResultPreds = 
			new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> m_RankEqResPred2InputPreds = 
			new HashRelation<IPredicate, IPredicate>();
	
	private final Map<Set<IPredicate>, IPredicate> m_WithoutAuxInputPreds2ResultPreds = 
			new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> m_WithoutAuxPred2InputPreds = 
			new HashRelation<IPredicate, IPredicate>();



	private final PredicateUnifier m_StemPU;
	private final PredicateUnifier m_LoopPU;
	private final PredicateUnifier m_AcceptingPU;
	

	

	public BuchiInterpolantAutomatonBouncer(SmtManager smtManager,
			BinaryStatePredicateManager bspm,
			BuchiEdgeChecker edgeChecker,
			boolean emtpyStem,
			Set<IPredicate> stemInterpolants, 
			Set<IPredicate> loopInterpolants, CodeBlock hondaEntererStem, CodeBlock hondaEntererLoop,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			boolean scroogeNondeterminismStem, boolean scroogeNondeterminismLoop,
			boolean hondaBouncerStem, boolean hondaBouncerLoop, 
			PredicateFactory predicateFactory, PredicateUnifier stemPU, PredicateUnifier loopPU, IPredicate falsePredicate) {
		super(smtManager,edgeChecker,abstraction, falsePredicate, null);
		m_Bspm = bspm;
		m_StemPU = new PredicateUnifier(m_SmtManager, falsePredicate);
		m_LoopPU = new PredicateUnifier(m_SmtManager, falsePredicate);
		m_AcceptingPU = new PredicateUnifier(m_SmtManager, falsePredicate);
		IPredicate initialPredicate;
		if (emtpyStem) {
			Set<IPredicate> empty = Collections.emptySet();
			initialPredicate = getOrConstructAcceptingPredicate(empty, true);
		} else {
			initialPredicate = getOrConstructStemPredicate(Collections.singleton(m_Bspm.getStemPrecondition()), true);
		}

		initializeConstruction(emtpyStem, bspm, stemInterpolants, loopInterpolants);
		m_HondaEntererStem = hondaEntererStem;
		m_HondaEntererLoop = hondaEntererLoop;
		/**
		 * Allow a some special nondeterministic transitions. For this 
		 * additional transition the
		 * - predecessor is some stem predicate
		 * - the letter is m_HondaEntererStem
		 * - the successor is the honda state
		 */
		m_ScroogeNondeterminismStem = scroogeNondeterminismStem;
		m_ScroogeNondeterminismLoop = scroogeNondeterminismLoop;
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

	private void initializeConstruction(boolean emtpyStem,
			BinaryStatePredicateManager bspm,
			Set<IPredicate> stemInterpolants,
			Set<IPredicate> loopInterpolants) {
		IPredicate precondition = bspm.getStemPrecondition();
		if (!emtpyStem) {
			m_InputStemPredicates.add(precondition);
			for (IPredicate stemPredicate : stemInterpolants) {
				if (!m_InputStemPredicates.contains(stemPredicate)) {
					m_InputStemPredicates.add(stemPredicate);
				}
			}
		}
		for (IPredicate loopPredicate : loopInterpolants) {
			if (!m_InputLoopPredicates.contains(loopPredicate)) {
				m_InputLoopPredicates.add(loopPredicate);
			}
			if (bspm.containsOldRankVariable(loopPredicate)) {
				m_InputWithAuxPredicates.add(loopPredicate);
			} else {
				m_InputAuxFreePredicates.add(loopPredicate);
			}
		}
	}
	
	@Override
	protected String startMessage() {
		StringBuilder sb = new StringBuilder();
		if (m_ScroogeNondeterminismStem || m_ScroogeNondeterminismLoop) {
			sb.append("Defining Buchi interpolant automaton with scrooge nondeterminism ");
			if (m_ScroogeNondeterminismStem) {
				sb.append("in stem");
				if (m_ScroogeNondeterminismLoop) {
					sb.append("in loop");
				}
			} else {
				sb.append("in loop");
			}
		} else {
			sb.append("Defining deterministic Buchi interpolant automaton ");
		}
		sb.append(m_HondaBouncerStem ? "with " : "without ");
		sb.append("honda bouncer for stem and ");
		sb.append(m_HondaBouncerLoop ? "with " : "without ");
		sb.append("honda bouncer for loop.");
		sb.append(m_InputStemPredicates.size()).append(" stem predicates ");
		sb.append(m_InputLoopPredicates.size()).append(" loop predicates ");
		return sb.toString();
	}
	
	@Override
	protected String exitMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Resulting Buchi interpolant automaton has ");
		sb.append(m_Result.size()).append(" states ");
		sb.append(m_StemResPred2InputPreds.getDomain().size()).append(" stem states ");
		sb.append(m_LoopResPred2InputPreds.getDomain().size()).append(" non-accepting loop states ");
		sb.append(m_AcceptingResPred2InputPreds.getDomain().size()).append(" accepting loop states ");
		return sb.toString();
	}
	
	
	protected void computeSuccs(IPredicate resPred, IPredicate resHier, 
			CodeBlock letter, SuccessorComputationHelper sch) {
		if (isPredHierLetterFalse(resPred, resHier, letter, sch)) {
			if (!m_Result.contains(m_IaFalseState)) {
				m_Result.addState(false, true, m_IaFalseState);
				s_Logger.warn("BenchmarkResult: Transition to False Predicate");
			}
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
		} else if (isFalseSucc(resPred, resHier, letter, sch)) {
			if (!m_Result.contains(m_IaFalseState)) {
				m_Result.addState(false, true, m_IaFalseState);
				s_Logger.warn("BenchmarkResult: Transition to False Predicate");
			}
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
		} else if (m_StemResPred2InputPreds.getDomain().contains(resPred)) {
			computeSuccsStem(resPred, resHier, letter, sch);
		} else if (m_AcceptingResPred2InputPreds.getDomain().contains(resPred)) {
			computeSuccsLoop(resPred, resHier, letter, sch);
		} else if (m_LoopResPred2InputPreds.getDomain().contains(resPred)) {
			computeSuccsLoop(resPred, resHier, letter, sch);
		} else {
			throw new AssertionError("unknown state");
		}
		sch.reportCacheEntry(resPred, resHier, letter, m_ResultBookkeeping);
	}
	
	private boolean isPredHierLetterFalse(IPredicate resPred, IPredicate resHier, 
			CodeBlock letter, SuccessorComputationHelper sch) {
		final boolean result;
		if (letter.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
			result = true;
		} else if (sch.isLinearPredecessorFalse(resPred)) {
			result = true;
		} else if (sch.isHierarchicalPredecessorFalse(resHier)) {
			result = true;
		} else {
			result = false;
		}
		return result;
	}
	
	private boolean isFalseSucc(IPredicate resPred, IPredicate resHier, 
			CodeBlock letter, SuccessorComputationHelper sch) {
		final boolean result;
		LBool sat = sch.sdecToFalse(resPred, resHier, letter);
		if (sat == null) {
			sat = sch.computeSuccWithSolver(resPred, resHier, letter, m_IaFalseState);
			if (sat == LBool.UNSAT) {
				result = true;
			} else {
				result = false;
			}
		} else {
			result = false;
		}
		return result;
	}
	
	
	private void computeSuccsStem(IPredicate resPred, IPredicate resHier, 
			CodeBlock letter, SuccessorComputationHelper sch) {
		IPredicate acceptingSucc;
		if (mayEnterAcceptingFromLoop(letter)) {
			acceptingSucc = addAcceptingSuccStem(resPred, resHier, letter, sch);
		} else {
			acceptingSucc = null;
		}
		if (acceptingSucc == null || m_ScroogeNondeterminismStem) {
			addNonAcceptingSuccStem(resPred, resHier, letter, sch);
		}
	}
	
	
	
	private IPredicate addAcceptingSuccStem(IPredicate resPred,
			IPredicate resHier, CodeBlock letter, SuccessorComputationHelper sch) {
		final Set<IPredicate> inputSuccsWithoutAux = new HashSet<IPredicate>();
		for (IPredicate succCand : m_InputAuxFreePredicates) {
			LBool sat = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
			if (sat == LBool.UNSAT) {
				inputSuccsWithoutAux.add(succCand);
			}
		}
		IPredicate resSucc = getOrConstructAcceptingPredicate(inputSuccsWithoutAux, false);
		sch.addTransition(resPred, resHier, letter, resSucc);
		return resSucc;
	}
	
	private IPredicate getOrConstructAcceptingPredicate(
			Set<IPredicate> inputSuccsWithoutAuxVar, boolean isInitial) {
		IPredicate withoutAux = getOrConstructPredicate(inputSuccsWithoutAuxVar, m_StemPU, m_WithoutAuxInputPreds2ResultPreds, m_WithoutAuxPred2InputPreds);
		Set<IPredicate> inputSuccsRankDecreaseAndBound = new HashSet<IPredicate>(inputSuccsWithoutAuxVar);
		inputSuccsRankDecreaseAndBound.add(m_Bspm.getRankDecreaseAndBound());
		IPredicate rankDecreaseAndBound = getOrConstructPredicate(inputSuccsRankDecreaseAndBound, m_AcceptingPU, m_AcceptingInputPreds2ResultPreds, m_AcceptingResPred2InputPreds);
		Set<IPredicate> inputSuccsRankEquality = new HashSet<IPredicate>(inputSuccsWithoutAuxVar);
		inputSuccsRankEquality.add(m_Bspm.getRankEquality());
		IPredicate rankEquality = getOrConstructPredicate(inputSuccsRankEquality, m_LoopPU, m_RankEqInputPreds2ResultPreds, m_RankEqResPred2InputPreds);
		if (!m_Result.contains(rankDecreaseAndBound)) {
			m_Result.addState(isInitial, true, rankDecreaseAndBound);
		}
		((BuchiEdgeChecker) m_EdgeChecker).putDecreaseEqualPair(rankDecreaseAndBound, rankEquality);
		return rankDecreaseAndBound;
	}
	
	private IPredicate getOrConstructStemPredicate(
			Set<IPredicate> inputSuccs, boolean isInitial) {
		IPredicate resSucc = getOrConstructPredicate(inputSuccs, m_StemPU, m_StemInputPreds2ResultPreds, m_StemResPred2InputPreds);
		if (!m_Result.contains(resSucc)) {
			m_Result.addState(isInitial, false, resSucc);
		}
		return resSucc;
	}
	
	private IPredicate getOrConstructLoopPredicate(
			Set<IPredicate> inputSuccs, boolean isInitial) {
		IPredicate resSucc = getOrConstructPredicate(inputSuccs, m_LoopPU, m_LoopInputPreds2ResultPreds, m_LoopResPred2InputPreds);
		if (!m_Result.contains(resSucc)) {
			m_Result.addState(isInitial, false, resSucc);
		}
		return resSucc;
	}
	
	

	private void addNonAcceptingSuccStem(IPredicate resPred,
			IPredicate resHier, CodeBlock letter, SuccessorComputationHelper sch) {
		final Set<IPredicate> inputSuccs = new HashSet<IPredicate>();
		for (IPredicate succCand : m_InputStemPredicates) {
			LBool sat = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
			if (sat == LBool.UNSAT) {
				inputSuccs.add(succCand);
			}
		}
		if (!inputSuccs.isEmpty()) {
			IPredicate resSucc = getOrConstructStemPredicate(inputSuccs, false);
			sch.addTransition(resPred, resHier, letter, resSucc);
		}
	}

	private void computeSuccsLoop(IPredicate resPred, IPredicate resHier, 
			CodeBlock letter, SuccessorComputationHelper sch) {
		IPredicate acceptingSucc;
		if (mayEnterAcceptingFromLoop(letter)) {
			acceptingSucc = addAcceptingSuccLoop(resPred, resHier, letter, sch);
		} else {
			acceptingSucc = null;
		}
		if (acceptingSucc == null || m_ScroogeNondeterminismLoop) {
			addNonAcceptingSuccLoop(resPred, resHier, letter, sch);
		}
	}
	
	private IPredicate addAcceptingSuccLoop(IPredicate resPred,
			IPredicate resHier, CodeBlock letter, SuccessorComputationHelper sch) {
		LBool satDecr = sch.computeSuccWithSolver(resPred, resHier, letter, m_Bspm.getRankDecreaseAndBound());
		if (satDecr != LBool.UNSAT) {
			return null;
		}
		final Set<IPredicate> inputSuccsWithoutAux = new HashSet<IPredicate>();
		for (IPredicate succCand : m_InputAuxFreePredicates) {
			LBool sat = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
			if (sat == LBool.UNSAT) {
				inputSuccsWithoutAux.add(succCand);
			}
		}
		IPredicate resSucc = getOrConstructAcceptingPredicate(inputSuccsWithoutAux, false);
		sch.addTransition(resPred, resHier, letter, resSucc);
		return resSucc;
	}
	
	private void addNonAcceptingSuccLoop(IPredicate resPred,
			IPredicate resHier, CodeBlock letter, SuccessorComputationHelper sch) {
		final Set<IPredicate> inputSuccs = new HashSet<IPredicate>();
		for (IPredicate succCand : m_InputLoopPredicates) {
			LBool sat = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
			if (sat == LBool.UNSAT) {
				inputSuccs.add(succCand);
			}
		}
		if (!inputSuccs.isEmpty()) {
			IPredicate resSucc = getOrConstructLoopPredicate(inputSuccs, false);
			sch.addTransition(resPred, resHier, letter, resSucc);
		}
	}
	
	
	
	
	
	private IPredicate getOrConstructPredicate(Set<IPredicate> succs,
			PredicateUnifier predicateUnifier,
			Map<Set<IPredicate>, IPredicate> inputPreds2ResultPreds, 
			HashRelation<IPredicate, IPredicate> resPred2InputPreds) {
		IPredicate resSucc = inputPreds2ResultPreds.get(succs);
		if (resSucc == null) {
			TermVarsProc conjunction = m_SmtManager.and(succs.toArray(new IPredicate[0]));
			clearAssertionStack();
			resSucc = predicateUnifier.getOrConstructPredicate(conjunction);
			assert resSucc != m_IaFalseState : "false should have been handeled before";
			inputPreds2ResultPreds.put(succs, resSucc);
			for (IPredicate succ : succs) {
				resPred2InputPreds.addPair(resSucc, succ);
			} 
		}
		return resSucc;
	}
	
	

	/**
	 * Do we allow that a transition labeled with letter has the honda as target.
	 * @param letter
	 * @return
	 */
	protected boolean mayEnterAcceptingFromLoop(CodeBlock letter) {
		return !m_HondaBouncerLoop || letter.equals(m_HondaEntererLoop);
	}

	/**
	 * Do we allow that a transition labeled with letter has the honda as target.
	 * @param letter
	 * @return
	 */
	protected boolean mayEnterAcceptingFromStem(CodeBlock letter) {
		return !m_HondaBouncerStem || letter.equals(m_HondaEntererStem);
	}
	


	@Override
	protected boolean areInternalSuccsComputed(IPredicate state,
			CodeBlock letter) {
		return m_ResultBookkeeping.isCachedInternal(state, letter);
	}

	@Override
	protected boolean areCallSuccsComputed(IPredicate state, Call call) {
		return m_ResultBookkeeping.isCachedCall(state, call);
	}

	@Override
	protected boolean areReturnSuccsComputed(IPredicate state, IPredicate hier,
			Return ret) {
		return m_ResultBookkeeping.isCachedReturn(state, hier, ret);
	}

	@Override
	protected boolean reviewInductiveInternal(IPredicate resPred,
			CodeBlock letter, IPredicate succCand, LBool result) {
		s_Logger.warn("result reviewing not implemented");
		return true;
	}

	@Override
	protected boolean reviewInductiveCall(IPredicate resPred, Call letter,
			IPredicate succCand, LBool result) {
		s_Logger.warn("result reviewing not implemented");
		return true;
	}

	@Override
	protected boolean reviewInductiveReturn(IPredicate resPred,
			IPredicate resHier, Return letter, IPredicate succCand, LBool result) {
		s_Logger.warn("result reviewing not implemented");
		return true;
	}
	

}
