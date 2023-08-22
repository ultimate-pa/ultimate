/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction.IAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;

/**
 * An interface for abstraction functions that can be refined to ensure they remain sound wrt the current abstraction
 * computed by a CEGAR loop.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <P>
 *            The type of infeasibility proof produced by the CEGAR loop
 * @param <H>
 *            The type of abstraction levels
 * @param <L>
 *            The type of abstracted actions
 */
public interface IRefinableAbstraction<P, H, L extends IAction> extends IAbstraction<H, L> {
	/**
	 * Retrieves the initial abstraction level. By default, this is the top element of the abstraction hierarchy (see
	 * {@link #getHierarchy()}).
	 */
	default H getInitial() {
		return getHierarchy().getTop();
	}

	/**
	 * Computes a refined abstraction level for the next CEGAR iteration.
	 *
	 * @param current
	 *            the abstraction level used in the last iteration
	 * @param refinement
	 *            the refinement made during the last iteration
	 * @return the new refinement level, which must be less or equal to the current level
	 */
	H refine(H current, IRefinementEngineResult<L, P> refinement);
}
