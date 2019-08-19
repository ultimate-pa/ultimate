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
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 * Implementation of AbstractInterpolantAutomaton that already provides basic operations for successor computation.
 *
 * @author Matthias Heizmann
 */
public abstract class BasicAbstractInterpolantAutomaton<LETTER extends IAction>
		extends AbstractInterpolantAutomaton<LETTER> {

	protected final IPredicate mIaTrueState;

	public BasicAbstractInterpolantAutomaton(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final IHoareTripleChecker hoareTripleChecker, final boolean useEfficientTotalAutomatonBookkeeping,
			final IPredicateUnifier predicateUnifier,
			final INestedWordAutomaton<LETTER, IPredicate> inputInterpolantAutomaton) {
		super(services, csToolkit, hoareTripleChecker, useEfficientTotalAutomatonBookkeeping,
				predicateUnifier.getFalsePredicate(), inputInterpolantAutomaton);
		mIaTrueState = predicateUnifier.getTruePredicate();
	}

	@Override
	protected void computeSuccs(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
			final SuccessorComputationHelper sch) {
		if (chooseFalseSuccessor1(resPred, resHier, letter, sch)) {
			addTransitionToFalse(resPred, resHier, letter, sch);
			return;
		}
		final Set<IPredicate> inputSuccs = new HashSet<>();
		// get all successors whose inductivity we already know from the input interpolant automaton
		addInputAutomatonSuccs(resPred, resHier, letter, sch, inputSuccs);
		// check if false is implied
		if (chooseFalseSuccessor2(resPred, resHier, letter, sch, inputSuccs)) {
			addTransitionToFalse(resPred, resHier, letter, sch);
			return;
		}
		// check all other predicates
		addOtherSuccessors(resPred, resHier, letter, sch, inputSuccs);
		constructSuccessorsAndTransitions(resPred, resHier, letter, sch, inputSuccs);
	}

	protected void addTransitionToFalse(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
			final SuccessorComputationHelper sch) {
		sch.addTransition(resPred, resHier, letter, mIaFalseState);
		sch.reportSuccsComputed(resPred, resHier, letter);
	}

	protected boolean chooseFalseSuccessor1(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
			final AbstractInterpolantAutomaton<LETTER>.SuccessorComputationHelper sch) {
		// if (linear) predecessor is false, the successor is false
		if (sch.isLinearPredecessorFalse(resPred)) {
			return true;
		}
		// if (hierarchical) predecessor is false, the successor is false
		if (sch.isHierarchicalPredecessorFalse(resHier)) {
			return true;
		}
		// if the letter is already infeasible, the successor is false
		return letter.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE;
	}

	protected boolean chooseFalseSuccessor2(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
			final SuccessorComputationHelper sch, final Set<IPredicate> inputSuccs) {
		if (inputSuccs.contains(mIaFalseState)) {
			return true;
		}
		return sch.computeSuccWithSolver(resPred, resHier, letter, mIaFalseState) == Validity.VALID;
	}

	protected abstract void addOtherSuccessors(IPredicate resPred, IPredicate resHier, LETTER letter,
			SuccessorComputationHelper sch, Set<IPredicate> inputSuccs);

	protected abstract void addInputAutomatonSuccs(IPredicate resPred, IPredicate resHier, LETTER letter,
			SuccessorComputationHelper sch, Set<IPredicate> inputSuccs);

	protected abstract void constructSuccessorsAndTransitions(IPredicate resPred, IPredicate resHier, LETTER letter,
			SuccessorComputationHelper sch, Set<IPredicate> inputSuccs);

}
