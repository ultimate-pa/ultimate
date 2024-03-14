/*
 * Copyright (C) 2024 Marcel Ebbinghaus
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;

/**
 * Variant of SmTInterpolRefinementStrategy for POR with sleep sets.
 * 
 * @author Marcel Ebbinghaus
 */
public class SmtInterpolSleepSetPORRefinementStrategy<L extends IIcfgTransition<?>> extends BasicRefinementStrategy<L> {

	/**
	 * Constructor.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param factory
	 *            factory.
	 * @param exceptionBlacklist
	 *            exceptionBlacklist.    
	 */
	@SuppressWarnings("unchecked")
	public SmtInterpolSleepSetPORRefinementStrategy(final StrategyFactory<L>.StrategyModuleFactory factory,
			final RefinementStrategyExceptionBlacklist exceptionBlacklist) {
		super(factory,
				new IIpTcStrategyModule[] {
						factory.createIpTcStrategyModuleSmtInterpolCraigSleepSetPOR(
								InterpolationTechnique.Craig_NestedInterpolation)/*,
						factory.createIpTcStrategyModuleSmtInterpolSpWp(InterpolationTechnique.ForwardPredicates)*/ },
				factory.createIpAbStrategyModuleStraightlineAll(), exceptionBlacklist);
	}

	@Override
	public String getName() {
		return RefinementStrategy.SMTINTERPOL.toString();
	}
}