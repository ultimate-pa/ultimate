package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

/**
 * Main class of Plug-In LassoRanker
 * 
 *
 * TODO: refine comments
 * 
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
	 * Method which returns ID of the Plugin.
	 * @return String containing Plugin ID
	 */
	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	/**
	 * Initialisation
	 * method is called by core after the plugin is loaded
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setTokenMap(TokenMap tokenMap) {
		// TODO Auto-generated method stub

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
	
	/**
	* @return marked traces or null if no special markers shall be added for output plug-ins
	*/
	public List<MarkedTrace> getMarkedTraces(){
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs,
			IScopeContext is) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}
}
