package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class StrategyContext<LETTER extends IIcfgTransition<?>> {
	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	private final TAPreferences mPrefsConsolidation;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mToolkit;
	private final AssertionOrderModulation<LETTER> mAssertionOrderModulation;

	public StrategyContext(ILogger logger, TaCheckAndRefinementPreferences<LETTER> prefs,
			TAPreferences taPrefsForInterpolantConsolidation, IUltimateServiceProvider services, CfgSmtToolkit toolkit,
			AssertionOrderModulation<LETTER> assertionOrderModulation) {
		mLogger = logger;
		mPrefs = prefs;
		mPrefsConsolidation = taPrefsForInterpolantConsolidation;
		mServices = services;
		mToolkit = toolkit;
		mAssertionOrderModulation = assertionOrderModulation;
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public TaCheckAndRefinementPreferences<LETTER> getPrefs() {
		return mPrefs;
	}

	public IUltimateServiceProvider getServices() {
		return mServices;
	}

	public CfgSmtToolkit getToolkit() {
		return mToolkit;
	}

	public AssertionOrderModulation<LETTER> getAssertionOrderModulation() {
		return mAssertionOrderModulation;
	}

	public TAPreferences getPrefsConsolidation() {
		return mPrefsConsolidation;
	}
}
