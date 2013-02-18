package de.uni_freiburg.informatik.ultimate.boogie.cfgreducer;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.boogie.cfgreducer.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.cfgreducer.CFGReducerObserver;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;

public class CFGReducer implements IGenerator {
	private static final String s_PLUGIN_NAME = "CFGReducer";
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;
	
	private CFGReducerObserver m_ReducerObserver;

	private GraphType m_InputType;
	
    public String getName() {
        return s_PLUGIN_NAME;
    }

    public String getPluginID() {
        return s_PLUGIN_ID;
    }

    public int init(Object param) {
    	m_ReducerObserver = new CFGReducerObserver();
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
		try
		{
			return new GraphType(getPluginID(), GraphType.Type.CFG, m_InputType.getFileNames());
		}
		catch(Exception e)
		{
			return null;
		}
	}

	public void setInputDefinition(GraphType graphType) {
		this.m_InputType = graphType;
	}

	//@Override
	public List<IObserver> getObservers() {
		List<IObserver> observerList = new ArrayList<IObserver>();
		observerList.add(m_ReducerObserver);
		return observerList;
	}

	public IElement getModel() {
		return this.m_ReducerObserver.getRoot();
	}

	@Override
	public List<MarkedTrace> getMarkedTraces() {
		// TODO Auto-generated method stub
		return null;
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
