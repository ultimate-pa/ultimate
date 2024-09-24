/*
 * Copyright (C) 2023 Marcel Ebbinghaus
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

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;

/**
 * An implementation of ITraceChecker which checks whether the postcondition holds after the execution of the run.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class PostConditionTraceChecker<L extends IIcfgTransition<?>> implements ITraceChecker<L> {
	private final IUltimateServiceProvider mServices;
	private final IAutomaton<L, IPredicate> mAbstraction;
	private final TaskIdentifier mTaskIdentifier;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private final StrategyFactory<L> mStrategyFactory;
	private final IPredicateUnifier mPredicateUnifier;
	private boolean mImperfectProof;

	/**
	 * Constructs a PostConditionTraceChecker.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param services
	 *            Ultimate services.
	 * @param abstraction
	 *            The type of letters.
	 * @param taskIdentifier
	 *            Task identifier.
	 * @param emptyStackStateFactory
	 *            Factory.
	 * @param predicateUnifier
	 *            predicate unifier.
	 * @param strategyFactory
	 *            Strategy factory.
	 */
	public PostConditionTraceChecker(final IUltimateServiceProvider services,
			final IAutomaton<L, IPredicate> abstraction, final TaskIdentifier taskIdentifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, final IPredicateUnifier predicateUnifier,
			final StrategyFactory<L> strategyFactory) {
		mServices = services;
		mAbstraction = abstraction;
		mTaskIdentifier = taskIdentifier;
		mEmptyStackFactory = emptyStackStateFactory;
		mPredicateUnifier = predicateUnifier;
		mStrategyFactory = strategyFactory;
		mImperfectProof = false;
	}

	@SuppressWarnings("unchecked")
	@Override
	public TracePredicates checkTrace(final IRun<L, IPredicate> run, final IPredicate preCondition,
			final IPredicate postCondition) {

		final ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(mServices, run, mAbstraction,
				mTaskIdentifier, mEmptyStackFactory, mPredicateUnifier, mPredicateUnifier.getTruePredicate(),
				mPredicateUnifier.getOrConstructPredicate(postCondition), RefinementStrategy.SMTINTERPOLSLEEPSETPOR);

		while (strategy.hasNextFeasilibityCheck()) {
			final ITraceCheckStrategyModule<L, ?> check = strategy.nextFeasibilityCheck();
			// boolean test = check.isCorrect().equals(LBool.UNSAT);
			mImperfectProof = false;
			if (check.isCorrect().equals(LBool.UNSAT)
					&& check instanceof IpTcStrategyModuleSmtInterpolCraigSleepSetPOR) {
				final InterpolatingTraceCheckCraig<L> checkCraig =
						((IpTcStrategyModuleSmtInterpolCraigSleepSetPOR<L>) check).construct();
				if (checkCraig.isPerfectSequence()) {
					return checkCraig.getIpp();
				}
				mImperfectProof = true;
				// return checkCraig.getIpp();
			}
		}
		return null;
	}

	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public boolean wasImperfectProof() {
		return mImperfectProof;
	}
}
