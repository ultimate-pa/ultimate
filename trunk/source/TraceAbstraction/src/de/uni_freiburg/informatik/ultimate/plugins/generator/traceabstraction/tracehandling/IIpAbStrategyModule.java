/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <L>
 */
public interface IIpAbStrategyModule<L> {

	IpAbStrategyModuleResult<L> buildInterpolantAutomaton(List<QualifiedTracePredicates> perfectIpps,
			List<QualifiedTracePredicates> imperfectIpps) throws AutomataOperationCanceledException;

	/**
	 * 
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 */
	public static final class IpAbStrategyModuleResult<L> {
		private final NestedWordAutomaton<L, IPredicate> mAutomaton;
		private final List<QualifiedTracePredicates> mUsedTracePredicates;

		public IpAbStrategyModuleResult(final NestedWordAutomaton<L, IPredicate> automaton,
				final List<QualifiedTracePredicates> predicates) {
			mAutomaton = automaton;
			mUsedTracePredicates = predicates;
		}

		public NestedWordAutomaton<L, IPredicate> getAutomaton() {
			return mAutomaton;
		}

		public List<QualifiedTracePredicates> getUsedTracePredicates() {
			return mUsedTracePredicates;
		}

	}
}
