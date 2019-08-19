/*
 * Copyright (C) 2015-2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint;

import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * The result of an abstract interpretation analysis run.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public interface IAbstractInterpretationResult<STATE extends IAbstractState<STATE>, ACTION, LOCATION> {

	/**
	 * @return a {@link Map} mapping to each location that was reachable during the analysis the computed fixpoint as
	 *         {@link Term}.
	 */
	Map<LOCATION, Term> getLoc2Term();

	/**
	 * @return a {@link Map} mapping each location that was reachable during the analysis of the computed fixpoint to
	 *         the corresponding abstract states.
	 */
	Map<LOCATION, Set<STATE>> getLoc2States();

	/**
	 * @return a {@link Map} mapping each location that was reachable during the analysis of the computed fixpoint to
	 *         one abstract state which is the result of the merging operation of all corresponding abstract states at
	 *         that location.
	 */
	Map<LOCATION, STATE> getLoc2SingleStates();

	/**
	 * @return a {@link Set} containing all fixpoints computed during the analysis as {@link Term}s.
	 */
	Set<Term> getTerms();

	/**
	 * @return A {@link List} of all (potentially spurious) abstract counterexamples found during the analysis. A
	 *         counterexample is a sequence of ACTIONs from an initial location to an error location. An abstract
	 *         counterexample does not contain the correct number of loop unrollings, but rather the number of loop
	 *         unrollings until a fixpoint was computed.
	 */
	List<AbstractCounterexample<DisjunctiveAbstractState<STATE>, ACTION, LOCATION>> getCounterexamples();

	/**
	 * @return true if the analysis could reach an error location, false otherwise.
	 */
	boolean hasReachedError();

	/**
	 * Generates a single string that represents this result. The string contains all fixpoints computed during the
	 * analysis.
	 *
	 * @param funSimplify
	 *            A function that takes a {@link Term} as parameter and returns a {@link String} representing the term.
	 * @return A string representing this result.
	 */
	String toSimplifiedString(Function<Term, String> funSimplify);

	/**
	 * @return The {@link IAbstractDomain} used during the analysis.
	 */
	IAbstractDomain<STATE, ACTION> getUsedDomain();

	Set<STATE> getPostStates(final Deque<ACTION> callStack, final ACTION symbol, final Set<STATE> preStates);

	IVariableProvider<STATE, ACTION> getUsedVariableProvider();

	/**
	 * @return the benchmark object of this fixpoint engine run.
	 */
	ICsvProviderProvider<Object> getBenchmark();
}
