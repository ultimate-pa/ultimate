package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Implementation of AbstractInterpolantAutomaton that already provides basic
 * operations for successor computation.
 * @author Matthias Heizmann
 */
public abstract class BasicAbstractInterpolantAutomaton extends
		AbstractInterpolantAutomaton {
	
	protected final IPredicate m_IaTrueState;
	protected final PredicateUnifier m_PredicateUnifier;


	public BasicAbstractInterpolantAutomaton(IUltimateServiceProvider services,
			SmtManager smtManager, IHoareTripleChecker hoareTripleChecker,
			boolean useEfficientTotalAutomatonBookkeeping,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			PredicateUnifier predicateUnifier,
			NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton,
			Logger logger) {
		super(services, smtManager, hoareTripleChecker, useEfficientTotalAutomatonBookkeeping, abstraction,
				predicateUnifier.getFalsePredicate(), interpolantAutomaton, logger);
		m_PredicateUnifier = predicateUnifier;
		m_IaTrueState = predicateUnifier.getTruePredicate();
	}

	protected void computeSuccs(IPredicate resPred, IPredicate resHier, CodeBlock letter,
			SuccessorComputationHelper sch) {
		// if (linear) predecessor is false, the successor is false
		if (sch.isLinearPredecessorFalse(resPred)) {
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
			sch.reportSuccsComputed(resPred, resHier, letter);
			return;
		}
		// if (hierarchical) predecessor is false, the successor is false
		if (sch.isHierarchicalPredecessorFalse(resHier)) {
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
			sch.reportSuccsComputed(resPred, resHier, letter);
			return;
		} 
		// if the letter is already infeasible, the successor is false
		if (letter.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
			sch.reportSuccsComputed(resPred, resHier, letter);
			return;
		}
		final Set<IPredicate> inputSuccs = new HashSet<IPredicate>();
		// get all successor whose inductivity we already know from the
		// input interpolant automaton
		addInputAutomatonSuccs(resPred, resHier, letter, sch, inputSuccs);
		// check if false is implied
		if (inputSuccs.contains(m_IaFalseState)){
			sch.addTransition(resPred, resHier, letter, m_IaFalseState);
			sch.reportSuccsComputed(resPred, resHier, letter);
			return;
		} else {
			Validity sat = sch.computeSuccWithSolver(resPred, resHier, letter, m_IaFalseState);
			if (sat == Validity.VALID) {
				sch.addTransition(resPred, resHier, letter, m_IaFalseState);
				sch.reportSuccsComputed(resPred, resHier, letter);
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



}