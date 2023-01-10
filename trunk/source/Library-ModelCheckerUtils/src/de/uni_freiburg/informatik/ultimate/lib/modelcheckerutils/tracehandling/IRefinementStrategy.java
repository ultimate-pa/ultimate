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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling;

import java.util.List;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * A {@link IRefinementStrategy} allows an {@link IRefinementEngine} to try multiple combinations of strategy modules,
 * i.e.,
 * <ol>
 * <li>a {@link ITraceCheckStrategyModule},</li>
 * <li>an {@link IIpgStrategyModule}, and</li>
 * <li>an {@link IIpAbStrategyModule}.</li>
 * </ol>
 * In the following class documentation this combination is just called "combination".
 * <p>
 * A refinement strategy is always invoked from a {@link IRefinementEngine}. It expects to be used like two iterators
 * and a field.
 *
 * First, a trace is checked for feasibility with possibly multiple {@link ITraceCheckStrategyModule}s using
 * {@link #hasNextFeasilibityCheck()} and {@link #nextFeasibilityCheck()}.
 *
 * <ul>
 * <li>If a {@link ITraceCheckStrategyModule} answers {@link LBool#SAT}, the strategy is finished.
 * <li>If it answers {@link LBool#UNKNOWN} and the strategy still {@link #hasNextFeasilibityCheck()}, then the
 * {@link #nextFeasibilityCheck()} is questioned.
 * <li>If it answers {@link LBool#UNSAT}, the strategy then can provide {@link IIpgStrategyModule}s.
 * </ul>
 *
 * The strategy controls how many of its {@link IIpgStrategyModule}s are used through
 * {@link #hasNextInterpolantGenerator(List, List)}.
 *
 * If it does not provide more generators, the generated sequences of perfect and/or imperfect interpolants is given to
 * the {@link IIpAbStrategyModule} provided by this strategy.
 *
 * The resulting automaton is then used to refine the trace abstraction of the current iteration.
 *
 * If no interpolants have been generated, the strategy fails and trace abstraction aborts.
 *
 * </p>
 *
 * @see IRefinementEngine
 * @see ITraceCheckStrategyModule
 * @see IIpgStrategyModule
 * @see IIpTcStrategyModule
 * @see IIpAbStrategyModule
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public interface IRefinementStrategy<L extends IAction> {

	/**
	 * @return the name of this strategy, usually the corresponding {@link RefinementStrategy} as String.
	 */
	String getName();

	/**
	 * @return true if {@link #nextFeasibilityCheck()} can be called to retrieve another
	 *         {@link ITraceCheckStrategyModule}.
	 */
	boolean hasNextFeasilibityCheck();

	/**
	 * @return the next {@link ITraceCheckStrategyModule}.
	 * @throws NoSuchElementException
	 */
	ITraceCheckStrategyModule<L, ?> nextFeasibilityCheck();

	/**
	 * @param perfectIpps
	 *            All perfect sequences of interpolants collected so far.
	 * @param imperfectIpps
	 *            All imperfect sequences of interpolants collected so far.
	 * @return true if {@link #nextInterpolantGenerator()} can be called to retrieve another {@link IIpgStrategyModule}.
	 */
	boolean hasNextInterpolantGenerator(List<QualifiedTracePredicates> perfectIpps,
			List<QualifiedTracePredicates> imperfectIpps);

	/**
	 * @return the next {@link IIpgStrategyModule}.
	 * @throws NoSuchElementException
	 */
	IIpgStrategyModule<?, L> nextInterpolantGenerator();

	/**
	 * @return A {@link RefinementStrategyExceptionBlacklist} that defines how exceptions during trace checks or
	 *         interpolant generation (i.e., through interactions with underlying solvers) should be handled.
	 */
	RefinementStrategyExceptionBlacklist getExceptionBlacklist();

	/**
	 * Some strategies might need a specific {@link IHoareTripleChecker} (e.g., AbsInt, ...) and can provide it here.
	 * The refinement engine will pick it up after completing a strategy and provide it to this iteration of the CEGAR
	 * loop.
	 *
	 * If your strategy does not require a specific {@link IHoareTripleChecker}, return null.
	 *
	 * @param engine
	 *            the {@link IRefinementEngine} instance after the strategy has been completely processed.
	 * @return An {@link IHoareTripleChecker} instance particular to this strategy or null
	 */
	IHoareTripleChecker getHoareTripleChecker(IRefinementEngine<L, ?> engine);

	/**
	 * Some strategies need a specific {@link IPredicateUnifier} (e.g., AbsInt, ...) and can provide it here. The
	 * refinement engine will pick it up after completing a strategy and provide it to this iteration of the CEGAR loop.
	 *
	 * @param engine
	 *            the {@link IRefinementEngine} instance after the strategy has been completely processed.
	 * @return An {@link IPredicateUnifier} instance particular to this strategy
	 */
	IPredicateUnifier getPredicateUnifier(IRefinementEngine<L, ?> engine);

	/**
	 * Merges the interpolants {@code perfectIpps} and {@code imperfectIpps} and optionally discards some of them.
	 *
	 * @param perfectIpps
	 *            A collection of perfect interpolants.
	 * @param imperfectIpps
	 *            A collection of imperfect interpolants.
	 * @return A subset of the union of {@code perfectIpps} and {@code imperfectIpps} that should be processed further.
	 */
	List<QualifiedTracePredicates> mergeInterpolants(List<QualifiedTracePredicates> perfectIpps,
			List<QualifiedTracePredicates> imperfectIpps);
}
