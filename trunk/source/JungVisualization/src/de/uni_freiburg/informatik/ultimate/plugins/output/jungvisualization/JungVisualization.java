package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization;

import java.util.Collections;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences.JungPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences.JungPreferenceValues;

public class JungVisualization implements IOutput {

	public final static String PLUGIN_ID = Activator.PLUGIN_ID;

	private Logger mLogger;

	private GraphType mGraphType;

	private IUltimateServiceProvider mServices;

	@Override
	public List<String> getDesiredToolID() {
		// Never called
		return null;
	}

	@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList((IObserver) new JungVisualizationObserver(mLogger, mGraphType, mServices));
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		UltimatePreferenceStore ups = new UltimatePreferenceStore(getPluginID());
		return ups.getEnum(JungPreferenceValues.LABEL_WHICH_MODEL, QueryKeyword.class);
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		mGraphType = graphType;
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return PLUGIN_ID;
	}

	@Override
	public void init() {
	}

	@Override
	public boolean isGuiRequired() {
		return true;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new JungPreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mServices = services;
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub

	}

}
