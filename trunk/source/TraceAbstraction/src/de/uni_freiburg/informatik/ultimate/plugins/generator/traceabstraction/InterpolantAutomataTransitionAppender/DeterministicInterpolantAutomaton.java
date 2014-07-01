package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * Given a lasso annotated with predicates, construct an interpolant automaton
 * that is nearly determinisitic.
 * @author Matthias Heizmann
 *
 */
public class DeterministicInterpolantAutomaton extends AbstractInterpolantAutomaton {
	
	private final Map<Set<IPredicate>, IPredicate> m_InputPreds2ResultPreds = 
			new HashMap<Set<IPredicate>, IPredicate>();
	private final HashRelation<IPredicate, IPredicate> m_ResPred2InputPreds = 
			new HashRelation<IPredicate, IPredicate>();


	private final IPredicate m_IaFalseState;
	private final IPredicate m_IaTrueState;
	
	private final Set<IPredicate> m_NonTrivialPredicates;

	private final boolean m_UseLazyEdgeChecks;
	

	private final PredicateUnifier m_PredicateUnifier;
	
	/**
	 * Split up predicates in their conjuncts. 
	 * First experiments on few examples showed that this is decreasing the
	 * performance.
	 */
	private boolean m_Cannibalize = false;
	

	

	public DeterministicInterpolantAutomaton(SmtManager smtManager, EdgeChecker edgeChecker,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction, 
			NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton, 
			TraceChecker traceChecker) {
		super(smtManager,edgeChecker, abstraction, traceChecker.getPostcondition(), interpolantAutomaton);
		m_UseLazyEdgeChecks = false;
		m_PredicateUnifier = traceChecker.getPredicateUnifier();
		Collection<IPredicate> allPredicates;
		if (m_Cannibalize ) {
			allPredicates = m_PredicateUnifier.cannibalizeAll(interpolantAutomaton.getStates().toArray(new IPredicate[0]));
			for (IPredicate pred : allPredicates) {
				if (!interpolantAutomaton.getStates().contains(pred)) {
					interpolantAutomaton.addState(false, false, pred);
				}
			}
		} else {
			allPredicates = interpolantAutomaton.getStates(); 
		}
		m_IaTrueState = traceChecker.getPrecondition();
		assert m_IaTrueState.getFormula().toString().equals("true");
		assert allPredicates.contains(m_IaTrueState);
		m_Result.addState(true, false, m_IaTrueState);
		m_ResPred2InputPreds.addPair(m_IaTrueState, m_IaTrueState);
		m_IaFalseState = traceChecker.getPostcondition();
		assert m_IaFalseState.getFormula().toString().equals("false");
		assert allPredicates.contains(m_IaFalseState);
		m_Result.addState(false, true, m_IaFalseState);
		m_ResPred2InputPreds.addPair(m_IaFalseState, m_IaFalseState);

		m_NonTrivialPredicates = new HashSet<IPredicate>();
		for (IPredicate state : allPredicates) {
			if (state != m_IaTrueState && state != m_IaFalseState) {
				m_ResPred2InputPreds.addPair(state, state);
				m_NonTrivialPredicates.add(state);
			}
		}

		s_Logger.info(startMessage());
		
	}
	
	@Override
	protected String startMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Constructing interpolant automaton ");
		sb.append("starting with ");
		sb.append(m_NonTrivialPredicates.size() + 2);
		sb.append(" interpolants.");
		return sb.toString();
	}
	
	@Override
	protected String exitMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Resulting deterministic interpolant automaton has ");
		sb.append(m_Result.size()).append(" states. ");
		return sb.toString();
	}


	
	protected void computeSuccs(IPredicate resPred, IPredicate resHier, 
			CodeBlock letter, SuccessorComputationHelper sch) {
		// if (linear) predecessor is false, the successor is false
		if (sch.isLinearPredecessorFalse(resPred)) {
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
			return;
		}
		// if (hierarchical) predecessor is false, the successor is false
		if (sch.isHierarchicalPredecessorFalse(resHier)) {
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
			return;
		} 
		// if the letter is already infeasible, the successor is false
		if (letter.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
			return;
		}
		// get all successor whose inductivity we already know from the
		// input interpolant automaton
		final Collection<IPredicate> automatonSuccs = 
				getConjunctSuccsInterpolantAutomaton(resPred, resHier, letter, sch);
		// check if false is implied
		if (automatonSuccs.contains(m_IaFalseState)){
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
			return;
		} else {
			LBool sat = sch.sdecToFalse(resPred, resHier, letter);
			if (sat == null) {
				sat = sch.computeSuccWithSolver(resPred, resHier, letter, m_IaFalseState);
				if (sat == LBool.UNSAT) {
					sch.addTransition(resPred, resHier, letter, m_IaFalseState);
					return;
				}
			}
		}
		// check all other predicates
		final Set<IPredicate> inputSuccs = new HashSet<IPredicate>();
		for (IPredicate succCand : m_NonTrivialPredicates) {
			if (automatonSuccs.contains(succCand)) {
				inputSuccs.add(succCand);
			} else if (sch.isInductiveSefloop(resPred, resHier, letter, succCand)) {
				inputSuccs.add(succCand);
			} else {
				LBool sat = null;
				if (m_UseLazyEdgeChecks) {
					sat = sch.sdLazyEc(resPred, resHier, letter, succCand);
				} else {
					sat = sch.sdec(resPred, resHier, letter, succCand);
				}
				if (sat == null) {
					sat = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
				}
				assert sch.reviewResult(resPred, resHier, letter, succCand, sat);
				if (sat == LBool.UNSAT) {
					inputSuccs.add(succCand);
				}
			}
		}
		IPredicate resSucc = getOrConstructPredicate(inputSuccs);
		sch.addTransition(resPred, resHier, letter, resSucc);
	}


	/**
	 * Returns all successors of resPred, resHier, and letter in automaton.
	 * If resPred and resHier were constructed as a conjunction of 
	 * inputPredicates, we also take the conjuncts.
	 */
	private Collection<IPredicate> getConjunctSuccsInterpolantAutomaton(
			IPredicate resPred, IPredicate resHier, CodeBlock letter,
			SuccessorComputationHelper sch) {
		final Set<IPredicate> resPredConjuncts = m_ResPred2InputPreds.getImage(resPred);
		assert resPredConjuncts != null;
		final Set<IPredicate> resHierConjuncts;
		if (resHier == null) {
			resHierConjuncts = null;
		} else {
			resHierConjuncts = m_ResPred2InputPreds.getImage(resHier);
		}
		Collection<IPredicate> result;
		if (resPredConjuncts.size() == 1 && 
				(resHier == null || resHierConjuncts.size() == 1)) {
			result = sch.getSuccsInterpolantAutomaton(resPred, resHier, letter);
		} else {
			result = new HashSet<IPredicate>();
			for (IPredicate inputPred : resPredConjuncts) {
				if (resHier == null) {
					result = sch.getSuccsInterpolantAutomaton(inputPred, null, letter);
				} else {
					for (IPredicate inputHier : resHierConjuncts) {
						result = sch.getSuccsInterpolantAutomaton(inputPred, inputHier, letter);
					}
				}
			}
		}
		return result;
	}


	/**
	 * Returns true iff  both of the following are true: 
	 *  - m_InterpolantAutomaton contains resPred
	 *  - resHier is null or m_InterpolantAutomaton contains resHier
	 */
	private boolean interpolantAutomatonContainsStates(IPredicate resPred,
			IPredicate resHier) {
		Collection<IPredicate> states = m_InterpolantAutomaton.getStates();
		if (states.contains(resPred)) {
			if (resHier == null || states.contains(resHier)) {
				return true;
			} else {
				return false;
			}
		} else {
			return false;
		}
	}


	


	


	private IPredicate getOrConstructPredicate(Set<IPredicate> succs) {
		final IPredicate result;
		if (succs.isEmpty()) {
			result = m_IaTrueState;
		} else if (succs.size() == 1) {
			result = succs.iterator().next();
			if (!m_Result.contains(result)) {
				m_Result.addState(false, false, result);
			}
		} else {
			IPredicate resSucc = m_InputPreds2ResultPreds.get(succs);
			if (resSucc == null) {
				TermVarsProc conjunction = m_SmtManager.and(succs.toArray(new IPredicate[0]));
				clearAssertionStack();
				resSucc = m_PredicateUnifier.getOrConstructPredicate(conjunction);
				m_InputPreds2ResultPreds.put(succs, resSucc);
				for (IPredicate succ : succs) {
					if (m_NonTrivialPredicates.contains(succ)) {
						m_ResPred2InputPreds.addPair(resSucc, succ);
					}
				}
				if (!m_Result.contains(resSucc)) {
					m_Result.addState(false, false, resSucc);
				}
			} 
			result = resSucc;
		}
		return result;
	}
	
	
	
	
	@Override
	protected boolean reviewInductiveInternal(IPredicate state, CodeBlock cb, IPredicate succ, LBool result) {
		clearAssertionStack();
		LBool reviewResult = m_EdgeChecker.getSmtManager().isInductive(state, cb, succ);
		if (satCompatible(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "  Review result: " + reviewResult);
		}
	}
	
	@Override
	protected boolean reviewInductiveCall(IPredicate state, Call cb, IPredicate succ, LBool result) {
		clearAssertionStack();
		LBool reviewResult = m_EdgeChecker.getSmtManager().isInductiveCall(state, cb, succ);
		if (satCompatible(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "  Review result: " + reviewResult);
		}

	}
	
	@Override
	protected boolean reviewInductiveReturn(IPredicate state, IPredicate hier, Return cb, IPredicate succ, LBool result) {
		clearAssertionStack();
		LBool reviewResult = m_EdgeChecker.getSmtManager().isInductiveReturn(state, hier, cb, succ);
		if (satCompatible(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "  Review result: " + reviewResult);
		}
	}
	
	
	/**
	 * Return true if both inputs are UNSAT or both inputs are in {SAT,UNKNOWN}.
	 */
	private boolean satCompatible(LBool sat1, LBool sat2) {
		switch (sat1) {
		case UNSAT:
			return sat2 == LBool.UNSAT;
		case SAT: //same as unknown
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
	

	@Override
	protected boolean areInternalSuccsComputed(IPredicate state, CodeBlock letter) {
		Collection<IPredicate> succs = m_Result.succInternal(state, letter);
		if (succs == null) {
			return false;
		} else {
			return succs.iterator().hasNext();
		}
	}

	@Override
	protected boolean areCallSuccsComputed(IPredicate state, Call call) {
		Collection<IPredicate> succs = m_Result.succCall(state, call);
		if (succs == null) {
			return false;
		} else {
			return succs.iterator().hasNext();
		}
	}


	@Override
	protected boolean areReturnSuccsComputed(IPredicate state, IPredicate hier,	Return ret) {
		Collection<IPredicate> succs = m_Result.succReturn(state, hier, ret);
		if (succs == null) {
			return false;
		} else {
			return succs.iterator().hasNext();
		}
	}


	
	
}
