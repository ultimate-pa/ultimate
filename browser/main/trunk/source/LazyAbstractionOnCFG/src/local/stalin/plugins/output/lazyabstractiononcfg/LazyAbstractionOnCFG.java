package local.stalin.plugins.output.lazyabstractiononcfg;

import java.util.Collections;
import java.util.List;

import local.stalin.access.IObserver;
import local.stalin.ep.interfaces.IOutput;
import local.stalin.model.GraphType;
import local.stalin.model.MarkedTrace;
import local.stalin.model.TokenMap;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

/**
 * Main class of Plug-In LazyAbstractionOnCFG
 * 
 *
 * TODO: refine comments
 * 
 */
public class LazyAbstractionOnCFG implements IOutput {

	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	
	private LazyAbstractionOnCFGObserver m_Observer;
	private GraphType m_InputDefinition;
	
	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	* Keeps track of marked traces that should be visualized in a way.
	*/
	private List<MarkedTrace> m_MarkedTraces;
	
	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.IRCPPlugin#getName()
	 */
	@Override
    public String getName() {
        return s_PLUGIN_NAME;
    }

	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.IRCPPlugin#getPluginID()
	 */
	@Override
    public String getPluginID() {
        return s_PLUGIN_ID;
    }

	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.IRCPPlugin#init(java.lang.Object)
	 */
	@Override
    public int init(Object param) {
    	m_Observer = new LazyAbstractionOnCFGObserver();
    	return 0;
    }

	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ITool#getQueryKeyword()
	 */
	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ITool#getDesiredToolID()
	 */
	@Override
	public List<String> getDesiredToolID() {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ITool#setTokenMap(local.stalin.model.TokenMap)
	 */
	@Override
	public void setTokenMap(TokenMap tokenMap) {
		// TODO Auto-generated method stub

	}

	//copied from safetychecker -> not sure what it does
	public GraphType getOutputDefinition() {
		return null;
	}
	
	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ITool#setInputDefinition(local.stalin.model.GraphType)
	 */
	@Override
	public void setInputDefinition(GraphType graphType) {
//		this.m_InputDefinition = graphType;
	}

	//@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList((IObserver) m_Observer);
	}
	
	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ITool#getRequireGui()
	 */
	@Override
	public boolean isGuiRequired() {
		return false;
	}
	
	/**
	* Keeps track of marked traces that should be visualized in a way.
	*/
	public void setMarkedTraces(List<MarkedTrace> traces){
		this.m_MarkedTraces = traces;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs,
			IScopeContext is) {
		// TODO Auto-generated method stub
		return null;
	}
}
