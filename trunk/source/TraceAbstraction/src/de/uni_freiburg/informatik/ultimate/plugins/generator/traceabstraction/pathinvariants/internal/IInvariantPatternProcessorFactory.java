/*
 * Copyright (C) 2015 Dirk Steinmetz
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * A factory producing {@link IInvariantPatternProcessor}s.
 *
 * @param <IPT>
 *            Invariant Pattern Type: Type used for invariant patterns
 */
public interface IInvariantPatternProcessorFactory<IPT> {

	/**
	 * Produces a new {@link IInvariantPatternProcessor} instance for a given {@link ControlFlowGraph}.
	 *
	 * @param cfg
	 *            the control flow graph to generate a processor for
	 * @param precondition
	 *            the invariant on the {@link ControlFlowGraph#getEntry()} of cfg
	 * @param postcondition
	 *            the invariant on the {@link ControlFlowGraph#getExit()} of cfg
	 * @param startLocation
	 * @param errorLocations
	 *            a set of error locations
	 *
	 * @return new {@link IInvariantPatternProcessor} instance
	 */
	IInvariantPatternProcessor<IPT> produce(final List<IcfgLocation> locations,
			final List<IcfgInternalTransition> transitions, final IPredicate precondition,
			final IPredicate postcondition, final IcfgLocation startLocation, final Set<IcfgLocation> errorLocations);
}
