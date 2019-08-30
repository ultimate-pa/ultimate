/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Sifa plug-in.
 *
 * The ULTIMATE Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.sifa;

import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.ExplicitValueDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.StatsWrapperDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.AlwaysFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.LogSizeWrapperFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.NeverFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.SizeLimitFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.StatsWrapperFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.FixpointLoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.InterpretCallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ReUseSupersetCallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.TopInputCallSummarizer;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.preferences.SifaPreferences;

/**
 * Constructs a new sifa interpreter using the settings from {@link SifaPreferences}.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class SifaBuilder {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IPreferenceProvider mPrefs;

	public SifaBuilder(final IUltimateServiceProvider services, final ILogger logger) {
		mServices = services;
		mLogger = logger;
		mPrefs = SifaPreferences.getPreferenceProvider(mServices);
	}

	public SifaComponents construct(final IIcfg<IcfgLocation> icfg, final IProgressAwareTimer timer) {
		final SifaStats stats = new SifaStats();
		final SymbolicTools tools = constructTools(stats, icfg);
		final IDomain domain = constructStatsDomain(stats, tools, timer);
		final IFluid fluid = constructStatsFluid(stats);
		final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSum =
				constructLoopSummarizer(stats, timer, tools, domain, fluid);
		final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSum =
				constructCallSummarizer(stats, tools, domain);
		final IcfgInterpreter icfgInterpreter = new IcfgInterpreter(mLogger, timer, stats, tools, icfg,
				IcfgInterpreter.allErrorLocations(icfg), domain, fluid, loopSum, callSum);
		return new SifaComponents(icfgInterpreter, domain, stats);
	}

	private SymbolicTools constructTools(final SifaStats stats, final IIcfg<IcfgLocation> icfg) {
		return new SymbolicTools(mServices, stats, icfg,
			mPrefs.getEnum(SifaPreferences.LABEL_SIMPLIFICATION, SifaPreferences.CLASS_SIMPLIFICATION),
			mPrefs.getEnum(SifaPreferences.LABEL_XNF_CONVERSION, SifaPreferences.CLASS_XNF_CONVERSION));
	}

	private IDomain constructStatsDomain(final SifaStats stats, final SymbolicTools tools,
			final IProgressAwareTimer timer) {
		return new StatsWrapperDomain(stats, constructDomain(tools, timer));
	}

	private IDomain constructDomain(final SymbolicTools tools, final IProgressAwareTimer timer) {
		final String prefDomain = mPrefs.getString(SifaPreferences.LABEL_ABSTRACT_DOMAIN);
		if (CompoundDomain.class.getSimpleName().equals(prefDomain)) {
			final List<IDomain> subdomains = SifaPreferences.SubdomainValidator
					.subdomains(mPrefs.getString(SifaPreferences.LABEL_COMPOUNDDOM_SUBDOM))
					.map(subDomName -> constructNonCompoundDomain(subDomName, tools, timer))
					.collect(Collectors.toList());
			return new CompoundDomain(tools, subdomains);

		} else {
			return constructNonCompoundDomain(prefDomain, tools, timer);
		}
	}

	private IDomain constructNonCompoundDomain(final String domainName,
			final SymbolicTools tools, final IProgressAwareTimer timer) {
		final IDomain domain;
		if (ExplicitValueDomain.class.getSimpleName().equals(domainName)) {
			domain = new ExplicitValueDomain(tools,
					mPrefs.getInt(SifaPreferences.LABEL_EXPLVALDOM_MAX_PARALLEL_STATES));
		} else if (IntervalDomain.class.getSimpleName().equals(domainName)) {
			domain = new IntervalDomain(mLogger, tools,
					mPrefs.getInt(SifaPreferences.LABEL_INTERVALDOM_MAX_PARALLEL_STATES),
					() -> timer);
		} else {
			throw new IllegalArgumentException("Unknown domain setting: " + domainName);
		}
		return domain;

	}

	private IFluid constructStatsFluid(final SifaStats stats) {
		final String prefFluid = mPrefs.getString(SifaPreferences.LABEL_FLUID);
		return new StatsWrapperFluid(stats, constructFluid(prefFluid));
	}

	private IFluid constructFluid(final String prefFluid) {
		final IFluid fluid;
		if (NeverFluid.class.getSimpleName().equals(prefFluid)) {
			fluid = new NeverFluid();
		} else if (SizeLimitFluid.class.getSimpleName().equals(prefFluid)) {
			fluid = new SizeLimitFluid(
					mPrefs.getInt(SifaPreferences.LABEL_SIZELIMITFLUID_MAX_DAGSIZE),
					mPrefs.getInt(SifaPreferences.LABEL_SIZELIMITFLUID_MAX_DISJUNCTS));
		} else if (AlwaysFluid.class.getSimpleName().equals(prefFluid)) {
			fluid = new AlwaysFluid();
		} else if (LogSizeWrapperFluid.class.getSimpleName().equals(prefFluid)) {
			final String prefInternFluid =
					mPrefs.getString(SifaPreferences.LABEL_LOGFLUID_INTERN_FLUID);
			fluid = new LogSizeWrapperFluid(mLogger, constructFluid(prefInternFluid));
		} else {
			throw new IllegalArgumentException("Unknown fluid setting: " + prefFluid);
		}
		return fluid;
	}

	private Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> constructLoopSummarizer(
			final SifaStats stats, final IProgressAwareTimer timer, final SymbolicTools tools,
			final IDomain domain, final IFluid fluid) {
		final String prefLoopSum = mPrefs.getString(SifaPreferences.LABEL_LOOP_SUMMARIZER);
		if (FixpointLoopSummarizer.class.getSimpleName().equals(prefLoopSum)) {
			return icfgIpr -> dagIpr -> new FixpointLoopSummarizer(
					stats, mLogger, () -> timer, tools, domain, fluid, dagIpr);
		} else {
			throw new IllegalArgumentException("Unknown loop summarizer setting: " + prefLoopSum);
		}
	}

	private Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> constructCallSummarizer(
			final SifaStats stats, final SymbolicTools tools, final IDomain domain) {
		final String prefCallSum = mPrefs.getString(SifaPreferences.LABEL_CALL_SUMMARIZER);
		if (TopInputCallSummarizer.class.getSimpleName().equals(prefCallSum)) {
			return icfgIpr -> dagIpr -> new TopInputCallSummarizer(
					stats, tools, icfgIpr.procedureResourceCache(), dagIpr);
		} else if (InterpretCallSummarizer.class.getSimpleName().equals(prefCallSum)) {
			return constructIprCallSummarizer(stats);
		} else if (ReUseSupersetCallSummarizer.class.getSimpleName().equals(prefCallSum)) {
			final SifaStats ignoreNestedStats = new SifaStats();
			return icfgIpr -> dagIpr -> new ReUseSupersetCallSummarizer(stats, tools, domain,
					constructIprCallSummarizer(ignoreNestedStats).apply(icfgIpr).apply(dagIpr));
		} else {
			throw new IllegalArgumentException("Unknown call summarizer setting: " + prefCallSum);
		}
	}

	private static Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> constructIprCallSummarizer(
			final SifaStats stats) {
		return icfgIpr -> dagIpr -> new InterpretCallSummarizer(stats, icfgIpr.procedureResourceCache(), dagIpr);
	}

	/**
	 * Sifa is divided into components – this class stores the main component {@link #getIcfgInterpreter()}
	 * and gives access to some intern components which are useful after interpretation.
	 *
	 * @author schaetzc@tf.uni-freiburg.de
	 */
	public static class SifaComponents {
		private final IcfgInterpreter mIcfgInterpreter;
		private final IDomain mDomain;
		private final SifaStats mStats;
		public SifaComponents(final IcfgInterpreter icfgInterpreter, final IDomain domain, final SifaStats stats) {
			mIcfgInterpreter = icfgInterpreter;
			mDomain = domain;
			mStats = stats;
		}
		public IcfgInterpreter getIcfgInterpreter() {
			return mIcfgInterpreter;
		}
		public IDomain getDomain() {
			return mDomain;
		}
		public SifaStats getStats() {
			return mStats;
		}
	}
}
