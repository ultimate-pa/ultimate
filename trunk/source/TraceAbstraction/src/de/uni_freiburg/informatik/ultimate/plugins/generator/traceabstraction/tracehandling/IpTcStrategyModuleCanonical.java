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

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class IpTcStrategyModuleCanonical<T extends IInterpolatingTraceCheck<LETTER>, LETTER extends IIcfgTransition<?>>
		extends IpTcStrategyModuleBase<T, LETTER> {

	protected final TaskIdentifier mTaskIdentifier;
	protected final IUltimateServiceProvider mServices;
	protected final TaCheckAndRefinementPreferences<?> mPrefs;
	protected final AssertionOrderModulation<LETTER> mAssertionOrderModulation;
	protected final IRun<LETTER, IPredicate, ?> mCounterexample;
	protected final IPredicateUnifier mPredicateUnifier;
	protected final IPredicate mPrecondition;
	protected final PredicateFactory mPredicateFactory;

	public IpTcStrategyModuleCanonical(final TaskIdentifier taskIdentifier, final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final IRun<LETTER, IPredicate, ?> counterExample,
			final IPredicate precondition, final AssertionOrderModulation<LETTER> assertionOrderModulation,
			final IPredicateUnifier predicateUnifier, final PredicateFactory predicateFactory) {
		mServices = services;
		mPrefs = prefs;
		mAssertionOrderModulation = assertionOrderModulation;
		mCounterexample = counterExample;
		mPredicateUnifier = predicateUnifier;
		mPredicateFactory = predicateFactory;
		mPrecondition = precondition;
		mTaskIdentifier = taskIdentifier;
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator statistics) {
		statistics.addTraceCheckStatistics(getOrConstruct().getStatistics());
	}

	protected ManagedScript createExternalManagedScript(final Script script) {
		mPrefs.getIcfgContainer().getCfgSmtToolkit().getSmtFunctionsAndAxioms().transferSymbols(script);
		return new ManagedScript(mServices, script);
	}
}
