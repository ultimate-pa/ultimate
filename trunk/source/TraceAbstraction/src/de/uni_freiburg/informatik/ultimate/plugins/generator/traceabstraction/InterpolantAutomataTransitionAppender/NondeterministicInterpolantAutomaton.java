package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Nondeterministic interpolant automaton with on-demand construction.
 * @author Matthias Heizmann
 *
 */
public class NondeterministicInterpolantAutomaton extends TotalInterpolantAutomaton {
	
	protected final Set<IPredicate> m_NonTrivialPredicates;
	

	public NondeterministicInterpolantAutomaton(IUltimateServiceProvider services, 
			SmtManager smtManager, ModifiableGlobalVariableManager modglobvarman, IHoareTripleChecker hoareTripleChecker,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction, 
			NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton, 
			PredicateUnifier predicateUnifier, Logger  logger) {
		super(services, smtManager, hoareTripleChecker, abstraction, 
				predicateUnifier, 
				interpolantAutomaton, logger);
		Collection<IPredicate> allPredicates = interpolantAutomaton.getStates(); 
		
		assert SmtUtils.isTrue(m_IaTrueState.getFormula());
		assert allPredicates.contains(m_IaTrueState);
		m_Result.addState(true, false, m_IaTrueState);
		assert SmtUtils.isFalse(m_IaFalseState.getFormula());
		assert allPredicates.contains(m_IaFalseState);
		m_Result.addState(false, true, m_IaFalseState);

		m_NonTrivialPredicates = new HashSet<IPredicate>();
		for (IPredicate state : allPredicates) {
			if (state != m_IaTrueState && state != m_IaFalseState) {
				m_NonTrivialPredicates.add(state);
				m_Result.addState(false, false, state);
			}
		}

		mLogger.info(startMessage());
		
	}
	
	@Override
	protected String startMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Constructing nondeterministic interpolant automaton ");
		sb.append(" with ");
		sb.append(m_NonTrivialPredicates.size() + 2);
		sb.append(" interpolants.");
		return sb.toString();
	}
	
	@Override
	protected String switchToReadonlyMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Switched to read-only mode: nondeterministic interpolant automaton has ");
		sb.append(m_Result.size()).append(" states. ");
		return sb.toString();
	}
	
	@Override
	protected String switchToOnTheFlyConstructionMessage() {
		StringBuilder sb = new StringBuilder();
		sb.append("Switched to On-DemandConstruction mode: nondeterministic interpolant automaton has ");
		sb.append(m_Result.size()).append(" states. ");
		return sb.toString();
	}


	
	protected void addOtherSuccessors(IPredicate resPred, IPredicate resHier,
			CodeBlock letter, SuccessorComputationHelper sch,
			final Set<IPredicate> inputSuccs) {
		for (IPredicate succCand : m_NonTrivialPredicates) {
			if (!inputSuccs.contains(succCand)) {
				Validity sat = sch.computeSuccWithSolver(resPred, resHier, letter, succCand);
				if (sat == Validity.VALID) {
					inputSuccs.add(succCand);
				}
			}
		}
		if (inputSuccs.isEmpty()) {
			inputSuccs.add(m_IaTrueState);
		}
	}


	/**
	 * Add all successors of input automaton
	 * @param inputSuccs 
	 */
	protected void addInputAutomatonSuccs(
			IPredicate resPred, IPredicate resHier, CodeBlock letter,
			SuccessorComputationHelper sch, Set<IPredicate> inputSuccs) {
			inputSuccs.addAll(sch.getSuccsInterpolantAutomaton(resPred, resHier, letter));
	}

	@Override
	protected void constructSuccessorsAndTransitions(IPredicate resPred,
			IPredicate resHier, CodeBlock letter, 
			SuccessorComputationHelper sch, Set<IPredicate> inputSuccs) {
		for (IPredicate succ : inputSuccs) {
			sch.addTransition(resPred, resHier, letter, succ);
		}
	}
	
	
}
