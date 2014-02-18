package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

/**
 * Given a lasso annotated with predicates, construct an interpolant automaton
 * that is nearly determinisitic.
 * @author Matthias Heizmann
 *
 */
public class DeterministicInterpolantAutomaton extends AbstractInterpolantAutomaton {
	
	protected final static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private final Map<Set<IPredicate>, IPredicate> m_InputPreds2ResultPreds = 
			new HashMap<Set<IPredicate>, IPredicate>();

	
	private final IPredicate m_IaFalseState;
	private final IPredicate m_IaTrueState;
	private final Set<IPredicate> m_NonTrivialPredicates;

	private final boolean m_UseLazyEdgeChecks;
	
	private final InternalSuccessorComputation m_InSucComp;
	private final CallSuccessorComputation m_CaSucComp;
	private final ReturnSuccessorComputation m_ReSucComp;
	private final PredicateUnifier m_PredicateUnifier;
	

	

	public DeterministicInterpolantAutomaton(SmtManager smtManager, EdgeChecker edgeChecker,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction, TraceChecker traceChecker) {
		super(smtManager,edgeChecker, abstraction);
		m_UseLazyEdgeChecks = false;
		m_IaTrueState = traceChecker.getPrecondition();
		assert m_IaTrueState.getFormula().toString().equals("true");
		m_Result.addState(true, false, m_IaTrueState);
		m_IaFalseState = traceChecker.getPostcondition();
		assert m_IaFalseState.getFormula().toString().equals("false");
		m_Result.addState(false, true, m_IaFalseState);
		m_InSucComp = new InternalSuccessorComputation();
		m_CaSucComp = new CallSuccessorComputation();
		m_ReSucComp = new ReturnSuccessorComputation();
		m_NonTrivialPredicates = new HashSet<IPredicate>();
		for (IPredicate pred : traceChecker.getInterpolants()) {
			if (pred != m_IaTrueState && pred != m_IaFalseState) {
				m_NonTrivialPredicates.add(pred);
			}
		}
		m_PredicateUnifier = traceChecker.getPredicateUnifier();
		s_Logger.info(startMessage());
		
	}
	
	private StringBuilder startMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Constructing interpolant automaton ");
		sb.append("starting with ");
		sb.append(m_NonTrivialPredicates.size() + 2);
		sb.append(" interpolants.");
		return sb;
	}
	
	protected String exitMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Resulting deterministic interpolant automaton has ");
		sb.append(m_Result.size()).append(" states. ");
		return sb.toString();
	}


	
	@Override
	protected void computeSuccsInternal(IPredicate state, CodeBlock letter) {
		m_InSucComp.compute(state, null, letter);
	}

	@Override
	protected void computeSuccsCall(IPredicate state, Call call) {
		m_CaSucComp.compute(state, null, call);
	}

	@Override
	protected void computeSuccsReturn(IPredicate state, IPredicate hier,
			Return ret) {
		m_ReSucComp.compute(state, hier, ret);
	}
	
	
	
	/**
	 * Abstract class for successor computation. Subclasses are
	 * the successor computations for internal, call, and return.
	 * Because we can only override methods with the same signature (in Java)
	 * we use the 3-parameter-signature for return (with hierarchical state)
	 * and use null as hierarchical state for call and internal.
	 */
	private abstract class AbstractSuccessorComputation {
		final void compute(IPredicate resPred, IPredicate resHier, CodeBlock letter) {
			// if (linear) predecessor is false, the successor is false
			if (isLinearPredecessorFalse(resPred)) {
				addTransition(resPred, resHier, letter, m_IaFalseState);
				return;
			}
			// if (hierarchical) predecessor is false, the successor is false
			if (isHierarchicalPredecessorFalse(resHier)) {
				addTransition(resPred, resHier, letter, m_IaFalseState);
				return;
			} 
			// if the letter is already infeasible, the successor is false
			if (letter.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
				addTransition(resPred, resHier, letter, m_IaFalseState);
				return;
			}
			// check if false is implied
			{
				LBool sat = sdecToFalse(resPred, resHier, letter);
				if (sat == null) {
					sat = computeSuccWithSolver(resPred, resHier, letter, m_IaFalseState);
					if (sat == LBool.UNSAT) {
						addTransition(resPred, resHier, letter, m_IaFalseState);
						return;
					}
				}
			}
			// check all other predicates
			Set<IPredicate> inputSuccs = new HashSet<IPredicate>();
			for (IPredicate succCand : m_NonTrivialPredicates) {
				if (isInductiveSefloop(resPred, resHier, letter, succCand)) {
					inputSuccs.add(succCand);
				} else {
					LBool sat = null;
					if (m_UseLazyEdgeChecks) {
						sat = sdLazyEc(resPred, resHier, letter, succCand);
					} else {
						sat = sdec(resPred, resHier, letter, succCand);
					}
					if (sat == null) {
						sat = computeSuccWithSolver(resPred, resHier, letter, succCand);
						if (sat == LBool.UNSAT) {
							inputSuccs.add(succCand);
						}
					}
					assert reviewResult(resPred, resHier, letter, succCand, sat);
				}
			}
			IPredicate resSucc = getOrConstructPredicate(inputSuccs);
			addTransition(resPred, resHier, letter, resSucc);
		}


		protected abstract boolean isLinearPredecessorFalse(IPredicate resPred);
		
		protected abstract boolean isHierarchicalPredecessorFalse(IPredicate resPred);

		protected abstract void addTransition(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate iaFalseState);

		protected abstract LBool computeSuccWithSolver(IPredicate resPred,
				IPredicate resHier, CodeBlock letter, IPredicate iaFalseState);
		
		protected abstract LBool sdecToFalse(IPredicate resPred, IPredicate resHier,
				CodeBlock letter);
		
		protected abstract boolean isInductiveSefloop(IPredicate resPred,
				IPredicate resHier, CodeBlock letter, IPredicate succCand);

		protected abstract LBool sdec(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand);

		protected abstract LBool sdLazyEc(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand);

		protected abstract boolean reviewResult(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand, LBool result);
	}
	
	private class InternalSuccessorComputation extends AbstractSuccessorComputation {

		@Override
		protected boolean isLinearPredecessorFalse(IPredicate resPred) {
			return resPred == m_IaFalseState;
		}

		@Override
		protected boolean isHierarchicalPredecessorFalse(IPredicate resHier) {
			assert resHier == null;
			return false;
		}

		@Override
		protected void addTransition(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate inputSucc) {
			assert resHier == null;
			m_Result.addInternalTransition(resPred, letter, inputSucc);
		}

		@Override
		protected LBool computeSuccWithSolver(IPredicate resPred,
				IPredicate resHier, CodeBlock letter, IPredicate inputSucc) {
			assert resHier == null;
			return DeterministicInterpolantAutomaton.super.
					computeSuccInternalSolver(resPred, letter, inputSucc);
		}

		@Override
		protected LBool sdecToFalse(IPredicate resPred, IPredicate resHier,
				CodeBlock letter) {
			assert resHier == null;
			return m_EdgeChecker.sdecInternalToFalse(resPred, letter);
		}

		@Override
		protected boolean isInductiveSefloop(IPredicate resPred,
				IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			if ((resPred == succCand) &&
				(m_EdgeChecker.sdecInternalSelfloop(resPred, letter) == LBool.UNSAT)) {
				return true;
			} else {
				return false;
			}
		}

		@Override
		protected LBool sdec(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			return m_EdgeChecker.sdecInteral(resPred, letter, succCand);
		}

		@Override
		protected LBool sdLazyEc(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			return m_EdgeChecker.sdLazyEcInteral(resPred, letter, succCand);
		}

		@Override
		protected boolean reviewResult(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand, LBool result) {
			assert resHier == null;
			return reviewInductiveInternal(resPred, letter, succCand, result);
		}
	}
	
	
	
	private class CallSuccessorComputation extends AbstractSuccessorComputation {

		@Override
		protected boolean isLinearPredecessorFalse(IPredicate resPred) {
			return resPred == m_IaFalseState;
		}

		@Override
		protected boolean isHierarchicalPredecessorFalse(IPredicate resHier) {
			assert resHier == null;
			return false;
		}

		@Override
		protected void addTransition(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate inputSucc) {
			assert resHier == null;
			m_Result.addCallTransition(resPred, letter, inputSucc);
		}

		@Override
		protected LBool computeSuccWithSolver(IPredicate resPred,
				IPredicate resHier, CodeBlock letter, IPredicate inputSucc) {
			assert resHier == null;
			return DeterministicInterpolantAutomaton.super.
					computeSuccCallSolver(resPred, letter, inputSucc);
		}

		@Override
		protected LBool sdecToFalse(IPredicate resPred, IPredicate resHier,
				CodeBlock letter) {
			assert resHier == null;
			// TODO:
			// there could be a contradiction if the Call is not a simple call
			// but interprocedural sequential composition 
			return null;
		}

		@Override
		protected boolean isInductiveSefloop(IPredicate resPred,
				IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			if ((resPred == succCand) &&
				(m_EdgeChecker.sdecCallSelfloop(resPred, letter) == LBool.UNSAT)) {
				return true;
			} else {
				return false;
			}
		}

		@Override
		protected LBool sdec(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			return m_EdgeChecker.sdecCall(resPred, letter, succCand);
		}

		@Override
		protected LBool sdLazyEc(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			return m_EdgeChecker.sdLazyEcCall(resPred, (Call) letter, succCand);
		}

		@Override
		protected boolean reviewResult(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand, LBool result) {
			assert resHier == null;
			return reviewInductiveCall(resPred, (Call) letter, succCand, result);
		}
	}
	
	
	private class ReturnSuccessorComputation extends AbstractSuccessorComputation {

		@Override
		protected boolean isLinearPredecessorFalse(IPredicate resPred) {
			return resPred == m_IaFalseState;
		}

		@Override
		protected boolean isHierarchicalPredecessorFalse(IPredicate resHier) {
			return resHier == m_IaFalseState;
		}

		@Override
		protected void addTransition(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate inputSucc) {
			m_Result.addReturnTransition(resPred, resHier, letter, inputSucc);
		}

		@Override
		protected LBool computeSuccWithSolver(IPredicate resPred,
				IPredicate resHier, CodeBlock letter, IPredicate inputSucc) {
			return DeterministicInterpolantAutomaton.super.
					computeSuccReturnSolver(resPred, resHier, letter, inputSucc);
		}

		@Override
		protected LBool sdecToFalse(IPredicate resPred, IPredicate resHier,
				CodeBlock letter) {
			//TODO: is there some useful rule?
			return null;
		}

		@Override
		protected boolean isInductiveSefloop(IPredicate resPred,
				IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			if ((resPred == succCand) &&
				(m_EdgeChecker.sdecReturnSelfloopPre(resPred, (Return) letter) == LBool.UNSAT)) {
				return true;
			} else if ((resHier == succCand) &&
					(m_EdgeChecker.sdecReturnSelfloopHier(resHier, (Return) letter) == LBool.UNSAT)) {
				return true;
			} else {
				return false;
			}
		}

		@Override
		protected LBool sdec(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand) {
			return m_EdgeChecker.sdecReturn(resPred, resHier, letter, succCand);
		}

		@Override
		protected LBool sdLazyEc(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand) {
			return m_EdgeChecker.sdLazyEcReturn(resPred, resHier, (Return) letter, succCand);
		}

		@Override
		protected boolean reviewResult(IPredicate resPred, IPredicate resHier,
				CodeBlock letter, IPredicate succCand, LBool result) {
			return reviewInductiveReturn(resPred, resHier, (Return) letter, succCand, result);
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
				if (!m_Result.contains(resSucc)) {
					m_Result.addState(false, false, resSucc);
				}
			} 
			result = resSucc;
		}
		return result;
	}
	
	
	
	
	
	private boolean reviewInductiveInternal(IPredicate state, CodeBlock cb, IPredicate succ, LBool result) {
		clearAssertionStack();
		LBool reviewResult = m_EdgeChecker.getSmtManager().isInductive(state, cb, succ);
		if (satCompatible(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "Review result: " + reviewResult);
		}
	}
	
	private boolean reviewInductiveCall(IPredicate state, Call cb, IPredicate succ, LBool result) {
		clearAssertionStack();
		LBool reviewResult = m_EdgeChecker.getSmtManager().isInductiveCall(state, cb, succ);
		if (satCompatible(result, reviewResult)) {
			return true;
		} else {
			throw new AssertionError("Result: " + result 
					+ "Review result: " + reviewResult);
		}

	}
	
	private boolean reviewInductiveReturn(IPredicate state, IPredicate hier, Return cb, IPredicate succ, LBool result) {
		clearAssertionStack();
		LBool reviewResult = m_EdgeChecker.getSmtManager().isInductiveReturn(state, hier, cb, succ);
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
