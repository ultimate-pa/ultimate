package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LassoRankerTerminationAnalysis;

/**
 * Main class of Plug-In LassoRanker
 * 
 * @see LassoRankerObserver
 * @see LassoRankerTerminationAnalysis
 */
public class LassoRanker implements IAnalysis {

	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	
	private LassoRankerObserver m_Observer;
	private GraphType m_InputDefinition;

	/**
	 * @return a human readable Name for the plugin
	 */
	@Override
	public String getName() {
		return s_PLUGIN_NAME;
	}

	/**
	 * @return the plugin ID
	 */
	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	/**
	 * Initialization
	 * Method is called by core after the plugin is loaded
	 */
	@Override
	public int init(Object param) {
		m_Observer = new LassoRankerObserver();
		return 0;
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
		this.m_InputDefinition = graphType;
	}

	//@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList((IObserver) m_Observer);
	}
	
	public GraphType getOutputDefinition() {
		/* 
		 * TODO This generated method body only assumes a standard case.
		 * Adapt it if necessary. Otherwise remove this todo-tag.
		 */
		return new GraphType(Activator.s_PLUGIN_ID,
				m_InputDefinition.getType(), m_InputDefinition.getFileNames());
	}
	
	@Override
	public boolean isGuiRequired() {
		return false;
	}
	

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferencesInitializer();
	}
}
