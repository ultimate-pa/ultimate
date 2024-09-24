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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Interface for the computation of the initial abstraction used by a CEGAR loop.
 *
 * Separating the computation of the initial abstraction in this interface and its various implementations allows for
 * the following benefits:
 *
 * <ul>
 * <li>decoupling: CEGAR loops do not depend on the many possible (and configurable) steps in the creation of the
 * initial abstraction (nested word automata, Petri nets, Petri net LBE, partial order reduction, ...).</li>
 * <li>deduplication: Implementations of this interface can be used for different CEGAR loops, avoiding code
 * duplication.</li>
 * <li>flexibility: Representing the computation of the initial abstraction as a separate artifact allows it to be used
 * in more flexible ways, e.g. reusing the same initial abstraction for multiple CEGAR loop instances.</li>
 * </ul>
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of transitions
 * @param <A>
 *            The type of the computed abstraction
 */
public interface IInitialAbstractionProvider<L extends IIcfgTransition<?>, A extends IAutomaton<L, ?>> {
	/**
	 * Computes the initial abstraction for the given control flow graph and error locations.
	 *
	 * @param icfg
	 *            The control flow graph from which an abstraction is computed
	 * @param errorLocs
	 *            The error locations to consider for the abstraction
	 * @return the new initial abstraction
	 * @throws AutomataLibraryException
	 *             The computation of the initial abstraction typically involves automata operations and may throw
	 *             {@link AutomataLibraryException}s.
	 */
	A getInitialAbstraction(IIcfg<? extends IcfgLocation> icfg, Set<? extends IcfgLocation> errorLocs)
			throws AutomataLibraryException;

	default IStatisticsDataProvider getStatistics() {
		return new AbstractStatisticsDataProvider() {
			// by default, no statistics are reported
		};
	}
}
