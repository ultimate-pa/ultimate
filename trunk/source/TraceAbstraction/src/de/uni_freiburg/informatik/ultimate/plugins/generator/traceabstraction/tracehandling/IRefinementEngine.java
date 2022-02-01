/*
 * Copyright (C) 2016-2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2019 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Checks a trace for feasibility and, if infeasible, constructs a proof of infeasibility.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            The type of the infeasibility proof, e.g., an interpolant automaton or a set of Hoare triples.
 */
public interface IRefinementEngine<L extends IAction, T> {
	/**
	 *
	 * @see ITraceCheck#isCorrect()
	 * @see ITraceCheckStrategyModule#isCorrect()
	 * @return
	 *         <ul>
	 *         <li>SAT if the trace does not fulfill its specification (e.g., if an error location is reachable),
	 *         <li>UNSAT if the trace does fulfill its specification,
	 *         <li>UNKNOWN if it was not possible to determine if the trace fulfills its specification.
	 *         </ul>
	 */
	LBool getCounterexampleFeasibility();

	/**
	 * This method may only be called if {@link #getCounterexampleFeasibility()} returns {@code UNSAT}.
	 *
	 * @return A proof of infeasibility in a format specified by the implementer. Examples include a NestedWordAutomaton
	 *         or just a sequence of predicates.
	 */
	T getInfeasibilityProof();

	/**
	 * @return true if {@link #getCounterexampleFeasibility()} was {@link LBool#UNSAT} and the underlying strategy can
	 *         be queried via {@link #getIcfgProgramExecution()} to retrieve a program exeuction that describes the
	 *         counterexample.
	 */
	boolean providesIcfgProgramExecution();

	/**
	 * @return An {@link IProgramExecution} if {@link #providesIcfgProgramExecution()} is true.
	 */
	IProgramExecution<L, Term> getIcfgProgramExecution();

	/**
	 * @return true if the refinement engine found a perfect sequence of interpolants, i.e., a sequence where each
	 *         interpolant is inductive w.r.t. the path program.
	 */
	boolean somePerfectSequenceFound();

	/**
	 * @return A list of {@link QualifiedTracePredicates} used in the result of {@link #getInfeasibilityProof()} or null
	 *         if no such proof was constructed.
	 */
	List<QualifiedTracePredicates> getUsedTracePredicates();

	/**
	 * Provides a {@link IHoareTripleChecker} that corresponds to the generated interpolants if this is needed. May
	 * return null.
	 *
	 * @see IRefinementStrategy#getHoareTripleChecker(IRefinementEngine)
	 */
	IHoareTripleChecker getHoareTripleChecker();

	/**
	 * @return An {@link IPredicateUnifier} instance that already knows all {@link IPredicate} that are used in the
	 *         infeasibility proof provided by {@link #getInfeasibilityProof()}.
	 */
	IPredicateUnifier getPredicateUnifier();

	/**
	 * @return An {@link RefinementEngineStatisticsGenerator} instance that contains all statistics collected during the
	 *         execution of this {@link IRefinementEngine} instance.
	 */
	RefinementEngineStatisticsGenerator getRefinementEngineStatistics();
}
