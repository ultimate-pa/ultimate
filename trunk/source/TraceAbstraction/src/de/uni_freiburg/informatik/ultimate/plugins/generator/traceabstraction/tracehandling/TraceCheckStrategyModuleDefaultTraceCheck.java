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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator.RefinementEngineStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class TraceCheckStrategyModuleDefaultTraceCheck<L extends IIcfgTransition<?>>
		implements ITraceCheckStrategyModule<L, TraceCheck<L>> {

	private final IUltimateServiceProvider mServices;
	private final TaCheckAndRefinementPreferences<?> mPrefs;
	private final AssertionOrderModulation<L> mAssertionOrderModulation;
	private final IRun<L, ?> mCounterexample;
	private final IPredicateUnifier mPredicateUnifier;
	private final IPredicate mPrecondition;

	private TraceCheck<L> mTraceCheck;

	protected TraceCheckStrategyModuleDefaultTraceCheck(final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<L> prefs, final AssertionOrderModulation<L> assertionOrderModulation,
			final IRun<L, ?> counterexample, final IPredicateUnifier predicateUnifier, final IPredicate precondition) {
		mServices = services;
		mPrefs = prefs;
		mAssertionOrderModulation = assertionOrderModulation;
		mCounterexample = counterexample;
		mPredicateUnifier = predicateUnifier;
		mPrecondition = precondition;
	}

	@Override
	public LBool isCorrect() {
		return getOrConstruct().isCorrect();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return getOrConstruct().providesRcfgProgramExecution();
	}

	@Override
	public IProgramExecution<L, Term> getRcfgProgramExecution() {
		return getOrConstruct().getRcfgProgramExecution();
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return getOrConstruct().getTraceCheckReasonUnknown();
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator stats) {
		stats.addStatistics(RefinementEngineStatisticsDefinitions.TRACE_CHECK, getOrConstruct().getStatistics());
	}

	@Override
	public TraceCheck<L> getOrConstruct() {
		if (mTraceCheck == null) {
			final AssertCodeBlockOrder assertionOrder = mAssertionOrderModulation.get(mCounterexample, null);
			final IPredicate postcondition = mPredicateUnifier.getFalsePredicate();
			mTraceCheck = new TraceCheck<>(mPrecondition, postcondition, new TreeMap<Integer, IPredicate>(),
					NestedWord.nestedWord(mCounterexample.getWord()), mServices, mPrefs.getCfgSmtToolkit(),
					assertionOrder, mPrefs.computeCounterexample(), mPrefs.collectInterpolantStatistics());
		}
		return mTraceCheck;
	}

}
