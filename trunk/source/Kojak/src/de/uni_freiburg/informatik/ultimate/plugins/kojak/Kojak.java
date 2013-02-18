package de.uni_freiburg.informatik.ultimate.plugins.kojak;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

//import org.apache.log4j.Logger;
import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;

public class Kojak implements IGenerator {

	private static final String s_PLUGIN_NAME = "Kojak" +
			"";
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;
	
	private KojakObserver m_Observer;
	//private static Logger s_Logger = Logger.getRootLogger();
	private GraphType m_InputDefinition;

	
    public String getName() {
        return s_PLUGIN_NAME;
    }

    public String getPluginID() {
        return s_PLUGIN_ID;
    }

    public int init(Object param) {
    	m_Observer = new KojakObserver();
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
		return new GraphType(Activator.PLUGIN_ID,
				GraphType.Type.CFG, m_InputDefinition.getFileNames());
	}

	public void setInputDefinition(GraphType graphType) {
		this.m_InputDefinition = graphType;
	}

	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(new AddKojakAnnotationsObserver());
		observers.add(m_Observer);
		return observers;
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

	@Override
	public List<MarkedTrace> getMarkedTraces() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IElement getModel() {
		return m_Observer.getRoot();
	}



}
