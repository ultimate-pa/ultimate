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

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;

/**
 * A strategy to generate invariant patterns composed of each a disjunction of a
 * increasing number of conjunctions of a increasing number of inequalities over
 * all program variables.
 * 
 * @see LinearInequalityInvariantPatternProcessor
 */
public interface ILinearInequalityInvariantPatternStrategy {

	/**
	 * Returns the number of elements in the outer disjunction and in each inner
	 * conjunction.
	 * 
	 * @param location
	 *            the location to generate an invariant pattern for
	 * @param round
	 *            the round
	 * 
	 * @return Array with exactly two fields, the first one containing the
	 *         number of elements in the outer disjunction and the second one
	 *         containing the number of elements within each inner conjunction,
	 *         where each element means
	 *         "one strict inequality and one non-strict one".
	 */
//	public int[] getDimensions(final Location location, final int round);
	public int[] getDimensions(final BoogieIcfgLocation location, final int round);
	

	/**
	 * Returns the maximal number of attempts to re-generate the invariant
	 * pattern map.
	 * 
	 * The round parameter will get for each integer between 0 and
	 * <code>getMaxRounds() - 1</code>.
	 * 
	 * @return maximal number of attempts to re-generate the invariant map
	 */
	public int getMaxRounds();
}
