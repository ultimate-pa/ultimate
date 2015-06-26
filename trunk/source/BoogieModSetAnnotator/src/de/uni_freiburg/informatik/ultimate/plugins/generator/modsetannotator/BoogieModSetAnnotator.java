package de.uni_freiburg.informatik.ultimate.plugins.generator.modsetannotator;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.boogie.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;

/**
 * 
 * @author arenis@informatik.uni-freiburg.de
 * 
 */
public class BoogieModSetAnnotator implements IAnalysis {

	private IUltimateServiceProvider mServices;

	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	public void init() {
	}

	/**
	 * I give you every model.
	 */
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	/**
	 * I don't need a special tool
	 */
	public List<String> getDesiredToolID() {
		return null;
	}

	public GraphType getOutputDefinition() {
		/* use old graph type definition */
		return null;
	}

	public void setInputDefinition(GraphType graphType) {
		// not required.
	}

	// @Override
	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		ModSetAnalyzer analyzer = new ModSetAnalyzer(mServices);
		observers.add(analyzer);
		observers.add(new ModSetWriter(analyzer, mServices));
		return observers;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// storage is not used by this plugin
	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;

	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub

	}
}
