/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE KInduction Library.
 *
 * The ULTIMATE KInduction Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE KInduction Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE KInduction Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE KInduction Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE KInduction Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

/**
 * The transition relation {@link LoopTreeFormulaBuilder} reads its flat graph from. It is the part of
 * {@link INestedWordAutomaton} that the builder actually uses, so that the builder's nodes do not have to be the
 * automaton's states.
 * <p>
 * Two implementations exist. {@link AutomatonGraph} is the automaton itself, for a caller that hands the builder a
 * scope of plain states. {@link UnfoldedGraph} has {@link CallNode}s as nodes, so that a callee which is unfolded
 * rather than summarized contributes one copy of its states per call site; the call and the return themselves are
 * not transitions there but virtual edges built by {@link ProcedureSummaries}.
 * <p>
 * The call and return accessors exist only so that {@code LoopTreeFormulaBuilder} can <b>refuse</b> a call or
 * return that would silently become an ordinary edge of a stackless graph. An implementation whose calls are all
 * resolved already reports none.
 *
 * @param <LETTER>
 *            letter type
 * @param <NODE>
 *            node type of the flat graph
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public interface ICallResolvedGraph<LETTER extends IAction, NODE> {

	Iterable<OutgoingInternalTransition<LETTER, NODE>> internalSuccessors(NODE node);

	/** The unresolved call transitions leaving {@code node}; empty if this graph resolves all of them. */
	Iterable<OutgoingCallTransition<LETTER, NODE>> callSuccessors(NODE node);

	/** The unresolved return transitions leaving {@code node} for the call site {@code hier}. */
	Iterable<OutgoingReturnTransition<LETTER, NODE>> returnSuccessorsGivenHier(NODE node, NODE hier);
}
