package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public abstract class TotalInterpolantAutomaton extends
		AbstractInterpolantAutomaton2 {

	protected final IPredicate m_IaTrueState;


	public TotalInterpolantAutomaton(IUltimateServiceProvider services,
			SmtManager smtManager, IHoareTripleChecker hoareTripleChecker,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			IPredicate trueState,
			IPredicate falseState,
			NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton,
			Logger logger) {
		super(services, smtManager, hoareTripleChecker, abstraction,
				falseState, interpolantAutomaton, logger);
		m_IaTrueState = trueState;
	}

	protected void computeSuccs(IPredicate resPred, IPredicate resHier, CodeBlock letter,
			SuccessorComputationHelper sch) {
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
		final Set<IPredicate> inputSuccs = new HashSet<IPredicate>();
		// get all successor whose inductivity we already know from the
		// input interpolant automaton
		addInputAutomatonSuccs(resPred, resHier, letter, sch, inputSuccs);
		// check if false is implied
		if (inputSuccs.contains(m_IaFalseState)){
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
			return;
		} else {
			Validity sat = sch.computeSuccWithSolver(resPred, resHier, letter, m_IaFalseState);
			if (sat == Validity.VALID) {
				sch.addTransition(resPred, resHier, letter, m_IaFalseState);
				return;
			}
		}
		// check all other predicates
		addOtherSuccessors(resPred, resHier, letter, sch, inputSuccs);
		constructSuccessorsAndTransitions(resPred, resHier, letter, sch, inputSuccs);
	}
	
	

	protected abstract void addOtherSuccessors(IPredicate resPred, IPredicate resHier,
			CodeBlock letter, SuccessorComputationHelper sch,
			Set<IPredicate> inputSuccs);

	protected abstract void addInputAutomatonSuccs(IPredicate resPred, IPredicate resHier,
			CodeBlock letter, SuccessorComputationHelper sch,
			Set<IPredicate> inputSuccs);
	
	protected abstract void constructSuccessorsAndTransitions(IPredicate resPred,
			IPredicate resHier, CodeBlock letter, SuccessorComputationHelper sch, Set<IPredicate> inputSuccs);

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
	protected boolean areReturnSuccsComputed(IPredicate state, IPredicate hier,
			Return ret) {
		Collection<IPredicate> succs = m_Result.succReturn(state, hier, ret);
		if (succs == null) {
			return false;
		} else {
			return succs.iterator().hasNext();
		}
	}

}