package local.stalin.boogie.cfg2smt;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import local.stalin.access.IObserver;
import local.stalin.boogie.cfg2smt.Activator;
import local.stalin.boogie.cfg2smt.CFG2SMTObserver;
import local.stalin.ep.interfaces.IAnalysis;
import local.stalin.model.GraphType;
import local.stalin.model.MarkedTrace;
import local.stalin.model.TokenMap;

public class CFG2SMT implements IAnalysis {

	private static final String s_PLUGIN_NAME = "CFG2SMT";
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;
	
	private CFG2SMTObserver m_Observer;

	private GraphType m_InputType;
	
    public String getName() {
        return s_PLUGIN_NAME;
    }

    public String getPluginID() {
        return s_PLUGIN_ID;
    }

    public int init(Object param) {
    	m_Observer = new CFG2SMTObserver();
    	return 0;
    }
	
	//@Override
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

	//@Override
	public List<String> getDesiredToolID() {
		// TODO Auto-generated method stub
		return null;
	}

	//@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList((IObserver) m_Observer);
	}

	//@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	//@Override
	public void setInputDefinition(GraphType graphType) {
		this.m_InputType = graphType;
	}

	//@Override
	public void setTokenMap(TokenMap tokenMap) {
		// TODO Auto-generated method stub

	}

	@Override
	public List<MarkedTrace> getMarkedTraces() {
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs, IScopeContext is) {
		return null;
	}
}
