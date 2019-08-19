/* Copyright (C) 2017 Betim Musa
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2015-2017 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * An interface for getting invariant patterns (templates) needed to generate constraints.
 * An invariant pattern or template over the program variables x_1, ..., x_n is a formula
 * in disjunctive normal form (D_1 \/ D_2 \/ ... \/ D_d) where each disjunct D_i consists of a conjunction
 * of inequalities ((c_1 * x_1 + c_2*x_2 + ... c_n*x_n <= 0) /\ ...). The variables c_1, ..., c_n are called
 * the parameters or coefficients of the invariant template.
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
	 *         containing the number of elements within each inner conjunction.
	 */
	public int[] getDimensions(final IcfgLocation location, final int round);


	/**
	 * Construct an invariant pattern for the given location and round.
	 * @param location
	 * @param round
	 * @param solver
	 * @param prefix - is prepended to each coefficient used in the invariant pattern
	 * @return
	 */
	public IPT getInvariantPatternForLocation(final IcfgLocation location,
			final int round, final Script solver, final String prefix);


	/**
	 * Construct an invariant pattern for the given location and round, but restrict the program variables used to the given
	 * set, i.e. use at most the given variables in the invariant pattern.
	 * @param location
	 * @param round
	 * @param solver
	 * @param prefix - is prepended to each coefficient used in the invariant pattern
	 * @param vars - the set of variables that should be used in the invariant pattern
	 * @return
	 */
	public IPT getInvariantPatternForLocation(final IcfgLocation location,
			final int round, final Script solver, final String prefix, Set<IProgramVar> vars);

	/**
	 * Get the set of coefficients/parameters used in the invariant pattern for the given
	 * location.
	 */
	public Set<Term> getPatternCoefficientsForLocation(final IcfgLocation location);

	public void setNumOfConjunctsForLocation(final IcfgLocation location, int numOfConjuncts);

	public void setNumOfDisjunctsForLocation(final IcfgLocation location, int numOfDisjuncts);

	/**
	 * Constructs a pattern for the given transition and round.
	 *
	 * @param transition
	 *            the transition to generate the pattern for
	 * @param round
	 *            the current round
	 * @param solver
	 *            a Script
	 * @param prefix
	 *            is prepended to each coefficient used in the pattern
	 * @return an pattern for the transition
	 * @throws UnsupportedOperationException
	 *             when patterns for transitions are not supported by the current strategy.
	 */
	IPT getPatternForTransition(IcfgEdge transition, int round, Script solver, String prefix);

	/**
	 * Get the set of integer coefficients for the given transition.
	 *
	 * @param transition
	 *            the transition
	 * @return a set of coefficients
	 * @throws UnsupportedOperationException
	 *             when patterns for transitions are not supported by the current strategy.
	 */
	Set<Term> getIntegerCoefficientsForTransition(final IcfgEdge transition);

	/**
	 * Returns the maximal number of attempts that should be respected while trying to find a solution for the constraints.
	 */
	public int getMaxRounds();


	/**
	 * Get the program variables contained in the invariant pattern that is used at the given location.
	 * @param location
	 * @param round
	 * @return
	 */
	public Set<IProgramVar> getPatternVariablesForLocation(final IcfgLocation location,
			final int round);

	/**
	 * Change the setting (i.e. increase num. of conjuncts/disjuncts and/or add/remove program variables) that is used to construct
	 * the invariant pattern for the given location.
	 * @param location
	 */
	public void changePatternSettingForLocation(final IcfgLocation location, final int round);


	/**
	 * TODO
	 * @param location
	 * @param locationsInUnsatCore
	 */
	public void changePatternSettingForLocation(final IcfgLocation location, final int round,
			final Set<IcfgLocation> locationsInUnsatCore);

	public void resetSettings();

}
