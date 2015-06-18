package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbstractInterpretationPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetector;

public class AbstractInterpretation implements IAnalysis {

	protected Logger mLogger;
	private IUltimateServiceProvider mServices;
	private List<IObserver> mObserver;

	public AbstractInterpretation() {
	}

	@Override
	public GraphType getOutputDefinition() {
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		final String creator = graphType.getCreator();
		switch (creator) {
		case "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder":
			mObserver = new ArrayList<IObserver>();
			RCFGLoopDetector externalLoopDetector = new RCFGLoopDetector(mServices);
			mObserver.add(externalLoopDetector);
			mObserver.add(new AbstractInterpretationRcfgObserver(mServices, externalLoopDetector));
			break;
		default:
			mObserver = null;
			break;
		}
	}

	@Override
	public List<IObserver> getObservers() {
		if (mObserver == null) {
			return Collections.emptyList();
		}
		return mObserver;
	}

	@Override
	public void init() {
		// not used
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new AbstractInterpretationPreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(IToolchainStorage services) {
		// not used
	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		// not used
	}

}
