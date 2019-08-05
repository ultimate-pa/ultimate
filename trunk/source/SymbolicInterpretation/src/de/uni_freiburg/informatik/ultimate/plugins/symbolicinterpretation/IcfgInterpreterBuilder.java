/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE SymbolicInterpretation plug-in.
 *
 * The ULTIMATE SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.symbolicinterpretation;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.ExplicitValueDomain;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.fluid.AlwaysFluid;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.fluid.LogSizeWrapperFluid;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.fluid.NeverFluid;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.FixpointLoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.ILoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.TopInputCallSummarizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.symbolicinterpretation.preferences.SymbolicInterpretationPreferences;

/**
 * Constructs a new sifa interpreter using the settings from {@link SymbolicInterpretationPreferences}.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class IcfgInterpreterBuilder {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IPreferenceProvider mPrefs;

	public IcfgInterpreterBuilder(final IUltimateServiceProvider services, final ILogger logger) {
		mServices = services;
		mLogger = logger;
		mPrefs = SymbolicInterpretationPreferences.getPreferenceProvider(mServices);
	}

	public IcfgInterpreter construct(final IIcfg<IcfgLocation> icfg) {
		final SymbolicTools tools = new SymbolicTools(mServices, icfg);
		final IProgressAwareTimer timer = mServices.getProgressMonitorService();
		final IDomain domain = constructDomain(tools);
		final IFluid fluid = constructFluid();
		final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSum =
				constructLoopSummarizer(timer, tools, domain);
		final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSum =
				constructCallSummarizer(tools);
		return new IcfgInterpreter(mLogger, timer, tools, icfg, IcfgInterpreter.allErrorLocations(icfg),
				domain, fluid, loopSum, callSum);
	}

	private IDomain constructDomain(final SymbolicTools tools) {
		final String prefDomain = mPrefs.getString(SymbolicInterpretationPreferences.LABEL_ABSTRACT_DOMAIN);
		final IDomain domain;
		if (ExplicitValueDomain.class.getSimpleName().equals(prefDomain)) {
			domain = new ExplicitValueDomain(mServices, tools,
					mPrefs.getInt(SymbolicInterpretationPreferences.LABEL_EXPLVALDOM_PARALLEL_STATES));
		} else if (IntervalDomain.class.getSimpleName().equals(prefDomain)) {
			domain = new IntervalDomain(mServices, tools);
		} else {
			throw new IllegalArgumentException("Unknown domain setting: " + prefDomain);
		}
		return domain;
	}

	private IFluid constructFluid() {
		final String prefFluid = mPrefs.getString(SymbolicInterpretationPreferences.LABEL_FLUID);
		return constructFluid(prefFluid);
	}

	private IFluid constructFluid(final String prefFluid) {
		final IFluid fluid;
		if (NeverFluid.class.getSimpleName().equals(prefFluid)) {
			fluid = new NeverFluid();
		} else if (AlwaysFluid.class.getSimpleName().equals(prefFluid)) {
			fluid = new AlwaysFluid();
		} else if (LogSizeWrapperFluid.class.getSimpleName().equals(prefFluid)) {
			final String prefInternFluid =
					mPrefs.getString(SymbolicInterpretationPreferences.LABEL_LOGFLUID_INTERN_FLUID);
			fluid = new LogSizeWrapperFluid(mLogger, constructFluid(prefInternFluid));
		} else {
			throw new IllegalArgumentException("Unknown fluid setting: " + prefFluid);
		}
		return fluid;
	}

	private Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> constructLoopSummarizer(
			final IProgressAwareTimer timer, final SymbolicTools tools, final IDomain domain) {
		final String prefLoopSum = mPrefs.getString(SymbolicInterpretationPreferences.LABEL_LOOP_SUMMARIZER);
		if (FixpointLoopSummarizer.class.getSimpleName().equals(prefLoopSum)) {
			return icfgIpr -> dagIpr -> new FixpointLoopSummarizer(mLogger, timer, tools, domain, dagIpr);
		} else {
			throw new IllegalArgumentException("Unknown loop summarizer setting: " + prefLoopSum);
		}
	}

	private Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> constructCallSummarizer(
			final SymbolicTools tools) {
		final String prefCallSum = mPrefs.getString(SymbolicInterpretationPreferences.LABEL_CALL_SUMMARIZER);
		if (TopInputCallSummarizer.class.getSimpleName().equals(prefCallSum)) {
			return icfgIpr -> dagIpr -> new TopInputCallSummarizer(tools, icfgIpr.procedureResourceCache(), dagIpr);
		} else {
			throw new IllegalArgumentException("Unknown call summarizer setting: " + prefCallSum);
		}
	}

}
