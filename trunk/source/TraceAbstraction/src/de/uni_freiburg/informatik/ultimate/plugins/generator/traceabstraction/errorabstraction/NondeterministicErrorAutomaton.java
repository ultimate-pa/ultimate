/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;

/**
 * Error automaton with on-demand enhancement.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 */
public class NondeterministicErrorAutomaton<LETTER extends IAction>
		extends NondeterministicInterpolantAutomaton<LETTER> {
	/**
	 * @param services
	 *            Ultimate services
	 * @param csToolkit
	 *            SMT toolkit
	 * @param hoareTripleChecker
	 *            'Hoare triple checker'
	 * @param inputAutomaton
	 *            input automaton
	 * @param predicateUnifier
	 *            predicate unifier
	 */
	public NondeterministicErrorAutomaton(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final IHoareTripleChecker hoareTripleChecker, final INestedWordAutomaton<LETTER, IPredicate> inputAutomaton,
			final IPredicateUnifier predicateUnifier) {
		super(services, csToolkit, hoareTripleChecker, inputAutomaton, predicateUnifier, false, false);
	}

	@Override
	protected String startMessage() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Constructing nondeterministic error automaton ").append(" with ")
				.append(mNonTrivialPredicates.size()).append(" predicates.");
		return sb.toString();
	}

	@Override
	protected boolean isFalsePresent(final Collection<IPredicate> allPredicates) {
		// we actually do not want to have a 'False' state
		return !super.isFalsePresent(allPredicates);
	}

	@Override
	protected void copyAllButTrue(final Set<IPredicate> target, final Collection<IPredicate> source) {
		// we even copy transitions to true
		target.addAll(source);
	}

	@Override
	protected void addIfNontrivialPredicate(final IPredicate state) {
		// we add all states because we have no nontrivial predicates
		mNonTrivialPredicates.add(state);
	}

	@Override
	protected void addTargetStateTrueIfStateIsTrue(final IPredicate resPred, final Set<IPredicate> inputSuccs) {
		// we do nothing here, 'True' does not play a special role here (in fact most self-loops for 'True' are wrong)
	}

	@Override
	protected boolean chooseFalseSuccessor1(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
			final AbstractInterpolantAutomaton<LETTER>.SuccessorComputationHelper sch) {
		// we do not want to have a 'False' state
		return false;
	}

	@Override
	protected boolean chooseFalseSuccessor2(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
			final AbstractInterpolantAutomaton<LETTER>.SuccessorComputationHelper sch,
			final Set<IPredicate> inputSuccs) {
		// we do not even have the 'False' state
		return false;
	}
}
