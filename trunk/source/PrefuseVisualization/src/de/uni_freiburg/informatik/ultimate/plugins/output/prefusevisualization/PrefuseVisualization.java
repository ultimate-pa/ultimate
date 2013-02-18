package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import prefuse.data.Graph;
import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.preferences.PreferenceValues;

/**
 * @author keil
 * 
 */
public class PrefuseVisualization implements IOutput {
	private static final String s_PLUGIN_NAME = "Prefuse Visualization";
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;
	private static final Logger s_Logger = UltimateServices.getInstance().getLogger(s_PLUGIN_ID);
	private static TokenMap s_ActiveTokenMap;
	private GraphType m_GraphType;
	private IObserver m_Observer;

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin#init(java.lang.Object)
	 */
	public int init(Object params) {
		PreferenceValues.initializeDefaultPreferences();
		return 0;
	}



	/**
	 * Create an Graph from an existing Node
	 * 
	 * @return Returns the created PrefuseGraph
	 */
	private Graph createGraph(boolean isDirected) {

		Graph g = new Graph(isDirected);

		// saves the name of the node
		g.addColumn("name", String.class);

		// saves the uid of the node
		g.addColumn("uid", String.class);
		
		// saves the type of the visual item
		g.addColumn("type", String.class);
		
		return g;
	}
	//TODO: Set directed / not directed right
	public List<IObserver> getObservers() {
		if(m_GraphType.isCyclic()){
			m_Observer = new PrefuseGraphObserver(createGraph(true),m_GraphType);
			s_Logger.debug("Selecting PrefuseGraphObserver (new)...");
		}
		else {
			s_Logger.debug("Selecting PrefuseObserver (old)...");
			m_Observer = new PrefuseObserver(createGraph(false),m_GraphType);	
		}
		
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(m_Observer);
		return observers;
	}

	/**
	 * There should be no need to modify the following methods.
	 */

	public QueryKeyword getQueryKeyword() {
		// The user should decide which model he wants to be visualized
		return QueryKeyword.USER;
	}

	public List<String> getDesiredToolID() {
		// Null because this Plugin does not rely on a special tool to be run
		// before itself
		return null;
	}

	public void setTokenMap(TokenMap tokenMap) {
		s_ActiveTokenMap = tokenMap;
	}

	public static TokenMap getActiveTokenMap() {
		return s_ActiveTokenMap;
	}

	public GraphType getOutputDefinition() {
		// Null indicates no change to the model structure
		return null;
	}

	public String getName() {
		return s_PLUGIN_NAME;
	}

	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	public void setInputDefinition(GraphType graphType) {
		this.m_GraphType = graphType;
	}



	@Override
	public void setMarkedTraces(List<MarkedTrace> traces) {
		// TODO Auto-generated method stub
		
	}



	@Override
	public boolean isGuiRequired() {
		return true;
	}



	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs, IScopeContext is) {
		return new IEclipsePreferences[] {cs.getNode(s_PLUGIN_ID)};
	}
}
