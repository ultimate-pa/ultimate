package de.uni_freiburg.informatik.ultimate.plugins.output.consoleout;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;
import de.uni_freiburg.informatik.ultimate.plugins.output.consoleout.preferences.PreferenceValues;

/**
 * This class initializes the Text Output plugin.
 * 
 * @author dietsch
 *
 */
public class ConsoleOut implements IOutput {

	private static final String s_PLUGIN_NAME = "ConsoleOut";
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	
	private ConsoleOutObserver m_Observer;
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(s_PLUGIN_ID);

	
    public String getName() {
        return s_PLUGIN_NAME;
    }

    public String getPluginID() {
        return s_PLUGIN_ID;
    }

    public int init(Object param) {

    	m_Observer = new ConsoleOutObserver(PreferenceValues.VALUE_SHOWALLANNOTATIONS_DEFAULT); 
    	// get parameters from config
    	ConfigurationScope config = new ConfigurationScope();
    	boolean showAllAnnotations = config.getNode(s_PLUGIN_ID).getBoolean(PreferenceValues.NAME_SHOWALLANNOTATIONS, PreferenceValues.VALUE_SHOWALLANNOTATIONS_DEFAULT);
    	s_Logger.debug("showAllAnnotations="+showAllAnnotations);
    	// set them
    	m_Observer.setShowAllAnnotations(showAllAnnotations);
		return 0;
    }

	/**
	 * I give you every model.
	 */
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.ALL;
	}

	/**
	 * I don't need a special tool
	 */
	public List<String> getDesiredToolID() {
		return null;
	}

	/**
	 * I don't use the TokenMap right now.
	 */
	public void setTokenMap(TokenMap tokenMap) {
	}

	public GraphType getOutputDefinition() {
		return null;
	}

	public void setInputDefinition(GraphType graphType) {
		m_Observer.setInputDefinition(graphType);
	}

	//@Override
	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(m_Observer);
		return observers;
	}

	@Override
	public void setMarkedTraces(List<MarkedTrace> traces) {
		// ignore marked traces
		return;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs, IScopeContext is) {
		return new IEclipsePreferences[] {cs.getNode(s_PLUGIN_ID)};
	}



}
