/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation.InterpolantConsolidationBenchmarkGenerator;

/**
 * Checks a trace for feasibility and, if infeasible, constructs an interpolant automaton.<br>
 * This class is used in the {@link BasicCegarLoop}.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class TraceAbstractionRefinementEngine<LETTER extends IIcfgTransition<?>>
		implements IRefinementEngine<NestedWordAutomaton<LETTER, IPredicate>> {
	private final ILogger mLogger;
	private final BaseRefinementStrategy<LETTER> mStrategy;

	/* outputs */
	private final LBool mFeasibility;

	/**
	 * @param logger
	 *            Logger.
	 * @param strategy
	 *            strategy
	 */
	public TraceAbstractionRefinementEngine(final ILogger logger, final BaseRefinementStrategy<LETTER> strategy) {
		// initialize fields
		mLogger = logger;
		mStrategy = Objects.requireNonNull(strategy);
		mLogger.info("Using refinement strategy " + mStrategy.getClass().getSimpleName());
		mFeasibility = mStrategy.executeStrategy();
	}

	@Override
	public LBool getCounterexampleFeasibility() {
		return mFeasibility;
	}

	@Override
	public boolean providesICfgProgramExecution() {
		return mStrategy.providesICfgProgramExecution();
	}

	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getIcfgProgramExecution() {
		return mStrategy.getIcfgProgramExecution();
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getInfeasibilityProof() {
		return mStrategy.getInfeasibilityProof();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mStrategy.getPredicateUnifier();
	}

	@Override
	public CachingHoareTripleChecker getHoareTripleChecker() {
		return mStrategy.getHoareTripleChecker();
	}

	@Override
	public boolean somePerfectSequenceFound() {
		return mStrategy.somePerfectSequenceFound();
	}

	public InterpolantConsolidationBenchmarkGenerator getInterpolantConsolidationStatistics() {
		return mStrategy.getInterpolantConsolidationStatistics();
	}
}
