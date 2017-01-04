/*
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2016 Betim Musa
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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * A strategy to generate invariant patterns composed of each a disjunction of a
 * increasing number of conjunctions of a increasing number of inequalities over
 * all program variables.
 * 
 * @see LinearInequalityInvariantPatternProcessor
 */
public interface ILinearInequalityInvariantPatternStrategy<IPT> {

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
	public int[] getDimensions(final IcfgLocation location, final int round);
	
	/**
	 * Returns an invariant pattern for the given location.
	 * 
	 * @param location
	 *            the location to generate an invariant pattern for
	 * @param round
	 *            attempt number, initialized with 0 and increased on each
	 *            attempt; see {@link #getMaxRounds()}
	 * @return invariant pattern for location
	 */
	public IPT getInvariantPatternForLocation(final IcfgLocation location,
			final int round, final Script solver, final String prefix);
	
	public IPT getInvariantPatternForLocation(final IcfgLocation location,
			final int round, final Script solver, final String prefix, Set<IProgramVar> vars);
	
	/**
	 * Applies the configuration found with
	 * {@link #hasValidConfiguration(Collection, int)} to a given invariant
	 * pattern.
	 * 
	 * The behaviour of this method is undefined, when the last call to
	 * {@link #hasValidConfiguration(Collection, int)} returned false or if
	 * {@link #hasValidConfiguration(Collection, int)} has not yet been called
	 * at all.
	 * 
	 * @param pattern the pattern to apply the configuration to
	 * @return the predicate representing the invariant found
	 */
//	public IPredicate applyConfiguration(IPT pattern);
	

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
	
	public Set<IProgramVar> getPatternVariablesForLocation(final IcfgLocation location,
			final int round);
	
	public void changePatternSettingForLocation(final IcfgLocation location);

	public void resetSettings();

}
