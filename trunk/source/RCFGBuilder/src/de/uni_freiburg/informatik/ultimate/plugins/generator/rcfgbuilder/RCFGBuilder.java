package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer;

/**
 * Main class of Plug-In RCFGBuilder
 * 
 * 
 * TODO: refine comments
 * 
 */
public class RCFGBuilder implements IGenerator {

	
	
	private static final String s_PLUGIN_NAME = Activator.PLUGIN_NAME;
	public static final String s_PLUGIN_ID = Activator.PLUGIN_ID;

	private RCFGBuilderObserver m_Observer;
	private GraphType m_InputDefinition;
	private IUltimateServiceProvider mServices;
	private IToolchainStorage mStorage;

	@Override
	public String getPluginName() {
		return s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	@Override
	public int init() {
		return 0;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		this.m_InputDefinition = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		m_Observer = new RCFGBuilderObserver(mServices,mStorage);
		return Collections.singletonList((IObserver) m_Observer);
	}

	@Override
	public GraphType getOutputDefinition() {
		/*
		 * TODO This generated method body only assumes a standard case. Adapt
		 * it if necessary. Otherwise remove this todo-tag.
		 */
		return new GraphType(Activator.PLUGIN_ID, GraphType.Type.CFG, m_InputDefinition.getFileNames());

	}

	@Override
	public IElement getModel() {
		return this.m_Observer.getRoot();
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
		mStorage = storage;
	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
	}
}
