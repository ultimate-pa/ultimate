package local.stalin.boogie.DSITransformer;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import local.stalin.access.IObserver;
import local.stalin.ep.interfaces.IGenerator;
import local.stalin.model.GraphType;
import local.stalin.model.INode;
import local.stalin.model.MarkedTrace;
import local.stalin.model.TokenMap;

/**
 * This Class transforms a Boogie AST into a new one to generate data structure invariants
 * 
 * @author arenis
 *
 */

public class DSITransformer implements IGenerator {

	private static final String s_PLUGIN_NAME = "DSITransformer";
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	
	private DSITransformerObserver m_Observer;

	private GraphType m_InputType;
	
    /**
	 * I don't need a special tool
	 */
	public List<String> getDesiredToolID() {
		return null;
	}

    @Override
	public List<MarkedTrace> getMarkedTraces() {
		return null;
	}

    public INode getModel() {
		return this.m_Observer.getRoot();
	}

	public String getName() {
        return s_PLUGIN_NAME;
    }

	@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList((IObserver) m_Observer);
	}

	public GraphType getOutputDefinition() {
		try
		{
			return new GraphType(getPluginID(), GraphType.Type.AST, m_InputType.getFileNames());
		}
		catch(Exception e)
		{
			return null;
		}
	}

	public String getPluginID() {
        return s_PLUGIN_ID;
    }

	/**
	 * I give you every model.
	 */
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	public int init(Object param) {
    	m_Observer = new DSITransformerObserver();
    	return 0;
    }

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	public void setInputDefinition(GraphType graphType) {
		this.m_InputType = graphType;
	}

	/**
	 * I don't use the TokenMap right now.
	 */
	public void setTokenMap(TokenMap tokenMap) {
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs, IScopeContext is) {
		return new IEclipsePreferences[] {cs.getNode(s_PLUGIN_ID)};
	}
}
