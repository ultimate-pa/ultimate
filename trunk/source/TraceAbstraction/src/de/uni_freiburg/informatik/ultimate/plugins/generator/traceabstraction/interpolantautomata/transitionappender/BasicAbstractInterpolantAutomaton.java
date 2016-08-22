/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Implementation of AbstractInterpolantAutomaton that already provides basic
 * operations for successor computation.
 * @author Matthias Heizmann
 */
public abstract class BasicAbstractInterpolantAutomaton extends
		AbstractInterpolantAutomaton {
	
	protected final IPredicate mIaTrueState;
	protected final PredicateUnifier mPredicateUnifier;


	public BasicAbstractInterpolantAutomaton(IUltimateServiceProvider services,
			SmtManager smtManager, IHoareTripleChecker hoareTripleChecker,
			boolean useEfficientTotalAutomatonBookkeeping,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			PredicateUnifier predicateUnifier,
			NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton,
			ILogger logger) {
		super(services, smtManager, hoareTripleChecker, useEfficientTotalAutomatonBookkeeping, abstraction,
				predicateUnifier.getFalsePredicate(), interpolantAutomaton, logger);
		mPredicateUnifier = predicateUnifier;
		mIaTrueState = predicateUnifier.getTruePredicate();
	}

	@Override
	protected void computeSuccs(IPredicate resPred, IPredicate resHier, CodeBlock letter,
			SuccessorComputationHelper sch) {
		// if (linear) predecessor is false, the successor is false
		if (sch.isLinearPredecessorFalse(resPred)) {
			sch.addTransition(resPred, resHier, letter, mIaFalseState);
			sch.reportSuccsComputed(resPred, resHier, letter);
			return;
		}
		// if (hierarchical) predecessor is false, the successor is false
		if (sch.isHierarchicalPredecessorFalse(resHier)) {
			sch.addTransition(resPred, resHier, letter, mIaFalseState);
			sch.reportSuccsComputed(resPred, resHier, letter);
			return;
		} 
		// if the letter is already infeasible, the successor is false
		if (letter.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
			sch.addTransition(resPred, resHier, letter, mIaFalseState);
			sch.reportSuccsComputed(resPred, resHier, letter);
			return;
		}
		final Set<IPredicate> inputSuccs = new HashSet<IPredicate>();
		// get all successor whose inductivity we already know from the
		// input interpolant automaton
		addInputAutomatonSuccs(resPred, resHier, letter, sch, inputSuccs);
		// check if false is implied
		if (inputSuccs.contains(mIaFalseState)){
			sch.addTransition(resPred, resHier, letter, mIaFalseState);
			sch.reportSuccsComputed(resPred, resHier, letter);
			return;
		} else {
			final Validity sat = sch.computeSuccWithSolver(resPred, resHier, letter, mIaFalseState);
			if (sat == Validity.VALID) {
				sch.addTransition(resPred, resHier, letter, mIaFalseState);
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
