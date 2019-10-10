/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpAbStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpgStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyModuleFactory;

/**
 * {@link IRefinementStrategy} that provides only one element, namely the one selected in the Ultimate preferences.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class FixedRefinementStrategy<LETTER extends IIcfgTransition<?>> extends BasicRefinementStrategy<LETTER> {

	public FixedRefinementStrategy(final StrategyModuleFactory<LETTER> factory,
			final RefinementStrategyExceptionBlacklist exceptionBlacklist) {
		super(factory, createModules(factory), exceptionBlacklist);
	}

	@SuppressWarnings("unchecked")
	private static final <LETTER extends IIcfgTransition<?>> StrategyModules<LETTER>
			createModules(final StrategyModuleFactory<LETTER> factory) {
		final IIpTcStrategyModule<?, LETTER> preferenceIpTc = factory.createIpTcStrategyModulePreferences();
		final ITraceCheckStrategyModule<?>[] traceChecks = new ITraceCheckStrategyModule[] { preferenceIpTc };
		final IIpgStrategyModule<?, LETTER>[] interpolantGenerators = new IIpgStrategyModule[] { preferenceIpTc };
		final IIpAbStrategyModule<LETTER> interpolantAutomatonBuilder =
				factory.createInterpolantAutomatonBuilderStrategyModulePreferences(preferenceIpTc);
		return new StrategyModules<>(traceChecks, interpolantGenerators, interpolantAutomatonBuilder);
	}

	@Override
	public String getName() {
		return RefinementStrategy.FIXED_PREFERENCES.toString();
	}
}
