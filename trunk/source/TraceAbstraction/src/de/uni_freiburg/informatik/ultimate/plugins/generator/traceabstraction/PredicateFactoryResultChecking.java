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

import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * StateFactory that should be used for result checking. 
 * Supports most operations but constructs always only an auxiliary predicate.
 * @author Matthias Heizmann
 *
 */
public class PredicateFactoryResultChecking extends StateFactory<IPredicate> {
	
	protected final SmtManager mSmtManager;
	private final String s_StateLabel = 
			"auxiliary predicate that should only be used while checking correctness of automata operations";
	
	public PredicateFactoryResultChecking(SmtManager smtManager) {
		mSmtManager = smtManager;
	}
	
	@Override
	public IPredicate intersection(IPredicate p1, IPredicate p2) {
		return mSmtManager.getPredicateFactory().newDebugPredicate(s_StateLabel);
	}
	
	@Override
	public IPredicate determinize(Map<IPredicate, Set<IPredicate>> down2up) {
		return mSmtManager.getPredicateFactory().newDebugPredicate(s_StateLabel);
	}
	
	@Override
	public IPredicate createSinkStateContent() {
		return mSmtManager.getPredicateFactory().newDebugPredicate(s_StateLabel);
	}

	@Override
	public IPredicate createEmptyStackState(){
		return mSmtManager.getPredicateFactory().newDebugPredicate(s_StateLabel);
	}

	@Override
	public IPredicate createDoubleDeckerContent(IPredicate down,
			IPredicate up) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	public IPredicate minimize(Collection<IPredicate> states) {
		return mSmtManager.getPredicateFactory().newDebugPredicate(s_StateLabel);
	}
	
	@Override
	public IPredicate senwa(IPredicate entry, IPredicate state) {
		assert false : "still used?";
		return mSmtManager.getPredicateFactory().newDontCarePredicate(((SPredicate) state).getProgramPoint());
	}

	@Override
	public IPredicate buchiComplementFKV(LevelRankingState compl) {
		return mSmtManager.getPredicateFactory().newDebugPredicate(s_StateLabel);
	}

	@Override
	public IPredicate intersectBuchi(IPredicate s1, IPredicate s2, int track) {
		return mSmtManager.getPredicateFactory().newDebugPredicate(s_StateLabel);
	}
	
	@Override
	public IPredicate getContentOnConcurrentProduct(IPredicate c1,
			IPredicate c2) {
		return mSmtManager.getPredicateFactory().newDebugPredicate(s_StateLabel);
	}
}
