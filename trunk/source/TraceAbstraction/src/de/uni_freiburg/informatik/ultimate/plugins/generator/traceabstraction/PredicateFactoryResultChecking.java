/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationCheckResultStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetAndAutomataInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IConcurrentProductStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISenwaStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SmtFreePredicateFactory;

/**
 * StateFactory that should be used for result checking. Supports most operations but constructs always only an
 * auxiliary predicate.
 *
 * @author Matthias Heizmann
 *
 */
public class PredicateFactoryResultChecking
		implements ISenwaStateFactory<IPredicate>, IConcurrentProductStateFactory<IPredicate>,
		IMinimizationStateFactory<IPredicate>, IMinimizationCheckResultStateFactory<IPredicate>,
		IPetriNetAndAutomataInclusionStateFactory<IPredicate> {

	protected final SmtFreePredicateFactory mPredicateFactory;
	private static final String STATE_LABEL =
			"auxiliary predicate that should only be used while checking correctness of automata operations";

	public PredicateFactoryResultChecking(final SmtFreePredicateFactory predicateFactory) {
		mPredicateFactory = predicateFactory;
	}

	@Override
	public IPredicate intersection(final IPredicate p1, final IPredicate p2) {
		return mPredicateFactory.newDebugPredicate(STATE_LABEL);
	}

	@Override
	public IPredicate determinize(final Map<IPredicate, Set<IPredicate>> down2up) {
		return mPredicateFactory.newDebugPredicate(STATE_LABEL);
	}

	@Override
	public IPredicate createSinkStateContent() {
		return mPredicateFactory.newDebugPredicate(STATE_LABEL);
	}

	@Override
	public IPredicate createEmptyStackState() {
		return mPredicateFactory.newDebugPredicate(STATE_LABEL);
	}

	@Override
	public IPredicate merge(final Collection<IPredicate> states) {
		return mPredicateFactory.newDebugPredicate(STATE_LABEL);
	}

	@Override
	public IPredicate senwa(final IPredicate entry, final IPredicate state) {
		assert false : "still used?";
		return mPredicateFactory.newDontCarePredicate(((SPredicate) state).getProgramPoint());
	}

	@Override
	public IPredicate buchiComplementFkv(final LevelRankingState compl) {
		return mPredicateFactory.newDebugPredicate(STATE_LABEL);
	}

	@Override
	public IPredicate intersectBuchi(final IPredicate s1, final IPredicate s2, final int track) {
		return mPredicateFactory.newDebugPredicate(STATE_LABEL);
	}

	@Override
	public IPredicate concurrentProduct(final IPredicate c1, final IPredicate c2) {
		return mPredicateFactory.newDebugPredicate(STATE_LABEL);
	}

	@Override
	public IPredicate getContentOnPetriNet2FiniteAutomaton(final Marking<?, IPredicate> marking) {
		return mPredicateFactory.newDebugPredicate(STATE_LABEL);
	}
}
