package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;


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

	@Override
	public void setTokenMap(TokenMap tokenMap) {
		// Don't need a token map
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
	public void setMarkedTraces(List<MarkedTrace> traces) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean isGuiRequired() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs, IScopeContext is) {
		return new IEclipsePreferences[] {cs.getNode(PLUGIN_ID)};
	}

}
