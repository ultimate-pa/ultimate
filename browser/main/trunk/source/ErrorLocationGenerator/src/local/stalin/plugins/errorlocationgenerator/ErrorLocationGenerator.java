package local.stalin.plugins.errorlocationgenerator;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import local.stalin.access.IObserver;
import local.stalin.ep.interfaces.IGenerator;
import local.stalin.model.GraphType;
import local.stalin.model.IElement;
import local.stalin.model.MarkedTrace;
import local.stalin.model.TokenMap;

public class ErrorLocationGenerator implements IGenerator {

	private static final String s_PLUGIN_NAME = "ErrorLocationGenerator";
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;
	
	private ErrorLocationGeneratorObserver m_Observer;
	@SuppressWarnings("unused")
	private static Logger s_Logger = Logger.getRootLogger();

	private GraphType m_InputType;
	
    public String getName() {
        return s_PLUGIN_NAME;
    }

    public String getPluginID() {
        return s_PLUGIN_ID;
    }

    public int init(Object param) {
    	m_Observer = new ErrorLocationGeneratorObserver();
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

	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(m_Observer);
		return observers;
	}

	@Override
	public IElement getModel() {
		// TODO Auto-generated method stub
		return this.m_Observer.getRoot();
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
		return null;
	}
}
