package de.uni_freiburg.informatik.ultimate.plugins.symbolicinterpretation;

import java.util.Objects;
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
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.FixpointLoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.ILoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.TopInputCallSummarizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.symbolicinterpretation.preferences.SymbolicInterpretationPreferences;

public class IcfgInterpreterBuilder {

	public enum DomainEnum {
		EXPLICIT_VALUE
	}

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private DomainEnum mOptionDomain;

	public IcfgInterpreterBuilder(final IUltimateServiceProvider services, final ILogger logger) {
		mServices = services;
		mLogger = logger;

		mOptionDomain = null;
	}

	public IcfgInterpreter constructInterpreter(final IIcfg<IcfgLocation> icfg) {
		final SymbolicTools tools = new SymbolicTools(mServices, icfg);

		final IPreferenceProvider prefs = SymbolicInterpretationPreferences.getPreferenceProvider(mServices);

		final IDomain domain;

		final DomainEnum denum = prefs.getEnum("SymbolicInterpretationPreferences.LABEL", DomainEnum.class);

		switch (denum) {
		case EXPLICIT_VALUE:
			domain = new ExplicitValueDomain(mServices, tools);
			break;
		default:
			throw new UnsupportedOperationException("Value not supported:		 " + denum);
		}

		final IFluid fluid = null;
		// TODO: Another swicth

		final IProgressAwareTimer timer = mServices.getProgressMonitorService();

		final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSummarizerFactory =
				(icfgIpr -> dagIpr -> new FixpointLoopSummarizer(mLogger, timer, tools, domain, dagIpr));
		final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSummarizerFactory =
				icfgIpr -> dagIpr -> new TopInputCallSummarizer(tools, icfgIpr.procedureResourceCache(), dagIpr);

		return new IcfgInterpreter(mLogger, timer, tools, icfg, IcfgInterpreter.allErrorLocations(icfg), domain, fluid,
				loopSummarizerFactory, callSummarizerFactory);
	}

	/**
	 * another option: fluid API and builder pattern
	 * 
	 * @param value
	 * @return
	 */
	public IcfgInterpreterBuilder setDomain(final DomainEnum value) {
		mOptionDomain = Objects.requireNonNull(value);
		return this;
	}

}
