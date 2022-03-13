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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;

/**
 * An {@link IIpTcStrategyModule} acts as a constructor for an {@link IInterpolatingTraceCheck} (<b>I</b>nter<b>p</b>
 * olating<b>T</b>race<b>c</b>heck) used in {@link IRefinementStrategy}s.
 *
 * Usually, {@link IInterpolatingTraceCheck} implementations do all their work directly in the constructor to avoid
 * creating mutable state. Hence, these wrapper classes are necessary to allow an {@link IRefinementStrategy} to create
 * an {@link IInterpolatingTraceCheck}s on demand.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <T>
 *            The actual {@link IInterpolatingTraceCheck} that is constructed by this module.
 * @param <L>
 *            The type of Icfg transition for which this strategy is used.
 *
 * @see IIpgStrategyModule
 * @see ITraceCheckStrategyModule
 */
public interface IIpTcStrategyModule<T extends IInterpolatingTraceCheck<L>, L extends IAction>
		extends IIpgStrategyModule<T, L>, ITraceCheckStrategyModule<L, T> {
	// only for grouping, do not extend!
}
