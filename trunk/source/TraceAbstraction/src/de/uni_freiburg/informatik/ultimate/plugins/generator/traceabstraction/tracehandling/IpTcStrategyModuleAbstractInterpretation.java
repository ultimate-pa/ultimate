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

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator.RefinementEngineStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * Creates {@link IInterpolatingTraceCheck} using fixpoint computation based on abstract interpretation plugin.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IpTcStrategyModuleAbstractInterpretation<LETTER extends IIcfgTransition<?>>
		extends IpTcStrategyModuleBase<IInterpolatingTraceCheck<LETTER>, LETTER> {

	private final Word<LETTER> mCounterExample;
	private final IPredicateUnifier mPredicateUnifier;
	private final TAPreferences mTaPrefs;
	private final PathProgramCache<LETTER> mPathProgramCache;
	private final IIcfg<?> mIcfg;
	private final IUltimateServiceProvider mServices;

	private CegarAbsIntRunner<LETTER> mAbsIntRunner;

	public IpTcStrategyModuleAbstractInterpretation(final Word<LETTER> counterexample,
			final IPredicateUnifier predicateUnifier, final IUltimateServiceProvider services, final IIcfg<?> icfg,
			final PathProgramCache<LETTER> pathProgramCache, final TAPreferences taPrefs) {
		super();
		mServices = services;
		mIcfg = icfg;
		mPathProgramCache = pathProgramCache;
		mTaPrefs = taPrefs;
		mCounterExample = counterexample;
		mPredicateUnifier = predicateUnifier;
	}

	public CegarAbsIntRunner<LETTER> getOrConstructRunner() {
		if (mAbsIntRunner == null) {
			mAbsIntRunner = new CegarAbsIntRunner<>(mServices, mIcfg, mPathProgramCache, mTaPrefs, mCounterExample,
					mPredicateUnifier);
		}
		return mAbsIntRunner;
	}

	@Override
	protected IInterpolatingTraceCheck<LETTER> construct() {
		return getOrConstructRunner().getInterpolantGenerator();
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator stats) {
		stats.addStatistics(RefinementEngineStatisticsDefinitions.ABSTRACT_INTERPRETATION,
				getOrConstructRunner().getStatistics());
	}

	@Override
	public IHoareTripleChecker getHoareTripleChecker() {
		return getOrConstructRunner().getHoareTripleChecker();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return getOrConstructRunner().getPredicateUnifier();
	}

}
