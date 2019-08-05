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

public class IcfgInterpreterBuilder {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	final IPreferenceProvider mPrefs;


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
		// TODO use settings
		return icfgIpr -> dagIpr -> new FixpointLoopSummarizer(mLogger, timer, tools, domain, dagIpr);
	}


	private Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> constructCallSummarizer(
			final SymbolicTools tools) {
		// TODO use settings
		return icfgIpr -> dagIpr -> new TopInputCallSummarizer(tools, icfgIpr.procedureResourceCache(), dagIpr);
	}

	/**
	 * another option: fluid API and builder pattern
	 *
	 * @param value
	 * @return
	 */
	/*
	public IcfgInterpreterBuilder setDomain(final DomainEnum value) {
		/mOptionDomain = Objects.requireNonNull(value);
		return this;
	}
	*/

}
