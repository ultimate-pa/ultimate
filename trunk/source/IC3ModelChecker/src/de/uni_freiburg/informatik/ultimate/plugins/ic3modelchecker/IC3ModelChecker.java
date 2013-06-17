package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;


public class IC3ModelChecker implements IOutput {

	private static final String s_PLUGIN_NAME = "IC3ModelChecker";
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;
	
	private IC3ModelCheckerObserver m_Observer;
	//private static Logger s_Logger = Logger.getRootLogger();

	
    public String getName() {
        return s_PLUGIN_NAME;
    }

    public String getPluginID() {
        return s_PLUGIN_ID;
    }

    public int init(Object param) {
    	m_Observer = new IC3ModelCheckerObserver();
    	return 0;
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

	/**
	 * I don't use the TokenMap right now.
	 */
	public void setTokenMap(TokenMap tokenMap) {
	}

	public GraphType getOutputDefinition() {
		return null;
	}

	public void setInputDefinition(GraphType graphType) {
	}

	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(m_Observer);
		return observers;
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
		return new IEclipsePreferences[] {cs.getNode(s_PLUGIN_ID)};
	}
}
