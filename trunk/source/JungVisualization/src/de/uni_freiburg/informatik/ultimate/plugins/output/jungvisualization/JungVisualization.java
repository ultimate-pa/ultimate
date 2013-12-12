package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.GraphType;


public class JungVisualization implements IOutput {
	
	public final static String PLUGIN_ID = Activator.PLUGIN_ID;

	private IObserver mobserver;
	
	
	
	
	@Override
	public List<String> getDesiredToolID() {
		// Never called
		return null;
	}

	@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList(mobserver);
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		// Use last model
		return QueryKeyword.LAST;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		// Do not need this information
	}


	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getName()
	 */
	@Override
	public String getName() {
		return "Jung Graph Visualization";
	}

	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getPluginID()
	 */
	@Override
	public String getPluginID() {
		return PLUGIN_ID;
	}

	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java.lang.Object)
	 */
	@Override
	public int init(Object params) {
		mobserver = new JungVisualizationObserver();
		return 0;
	}

	@Override
	public boolean isGuiRequired() {
		// TODO Auto-generated method stub
		return false;
	}


	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}

}
