/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 * A {@link DeterministicInterpolantAutomaton} that only tries to add successors on demand for letters that are not in a
 * pre-defined alphabet.
 * 
 * This automaton type is used during verification with reuse.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ReusingDeterministicInterpolantAutomaton<LETTER extends IAction>
		extends DeterministicInterpolantAutomaton<LETTER> {

	private final VpAlphabet<LETTER> mOldAlphabet;

	public ReusingDeterministicInterpolantAutomaton(final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final IHoareTripleChecker hoareTripleChecker,
			final INestedWordAutomaton<LETTER, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final boolean conservativeSuccessorCandidateSelection,
			final boolean cannibalize, final VpAlphabet<LETTER> oldAlphabet) {
		super(services, csToolkit, hoareTripleChecker, inputInterpolantAutomaton, predicateUnifier,
				conservativeSuccessorCandidateSelection, cannibalize);
		mOldAlphabet = oldAlphabet;
	}

	@Override
	protected void computeSuccs(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
			final AbstractInterpolantAutomaton<LETTER>.SuccessorComputationHelper sch) {
		if (mOldAlphabet.containsAny(letter)) {
			// only add already known successors if the letter is old
			if (chooseFalseSuccessor1(resPred, resHier, letter, sch)) {
				addTransitionToFalse(resPred, resHier, letter, sch);
				return;
			}
			final Set<IPredicate> inputSuccs = new HashSet<>();
			addInputAutomatonSuccs(resPred, resHier, letter, sch, inputSuccs);
			constructSuccessorsAndTransitions(resPred, resHier, letter, sch, inputSuccs);
			return;
		}
		super.computeSuccs(resPred, resHier, letter, sch);
	}

}
