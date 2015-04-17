package de.uni_freiburg.informatik.ultimate.output.cfgconsoleout;

import java.util.Collections;
import java.util.List;
import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.GraphType;

public class CFGConsoleOut implements IOutput {

	private IObserver mObserver;
	private IUltimateServiceProvider mServices;

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList(mObserver);
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {

	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public void init() {
		mObserver = new CFGConsoleOutObserver(mServices);
	}

	@Override
	public void finish() {

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
		return null;
	}

}
