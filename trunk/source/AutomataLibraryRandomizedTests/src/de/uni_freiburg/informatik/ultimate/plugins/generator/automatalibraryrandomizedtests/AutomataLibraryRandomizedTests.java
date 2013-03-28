package de.uni_freiburg.informatik.ultimate.plugins.generator.automatalibraryrandomizedtests;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

/**
 * Main class of Plug-In AutomataLibraryRandomizedTests
 * 
 *
 * TODO: refine comments
 * 
 */
public class AutomataLibraryRandomizedTests implements IGenerator {

	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	
	private AutomataLibraryRandomizedTestsObserver m_Observer;
	private GraphType m_InputDefinition;
	
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getName()
	 */
	@Override
    public String getName() {
        return s_PLUGIN_NAME;
    }

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getPluginID()
	 */
	@Override
    public String getPluginID() {
        return s_PLUGIN_ID;
    }

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java.lang.Object)
	 */
	@Override
    public int init(Object param) {
    	m_Observer = new AutomataLibraryRandomizedTestsObserver();
    	return 0;
    }

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getQueryKeyword()
	 */
	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getDesiredToolID()
	 */
	@Override
	public List<String> getDesiredToolID() {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#setTokenMap(de.uni_freiburg.informatik.ultimate.model.TokenMap)
	 */
	@Override
	public void setTokenMap(TokenMap tokenMap) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#setInputDefinition(de.uni_freiburg.informatik.ultimate.model.GraphType)
	 */
	@Override
	public void setInputDefinition(GraphType graphType) {
		this.m_InputDefinition = graphType;
	}

	//@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList((IObserver) m_Observer);
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IModifyingTool#getOutputDefinition()
	 */
	public GraphType getOutputDefinition() {
		/* 
		 * TODO This generated method body only assumes a standard case.
		 * Adapt it if necessary. Otherwise remove this todo-tag.
		 */
		return new GraphType(Activator.s_PLUGIN_ID,
				m_InputDefinition.getType(), m_InputDefinition.getFileNames());
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator#getModel()
	 */
	@Override
	public IElement getModel() {
		// TODO Auto-generated method stub
		return null; //m_Observer.get;
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getRequireGui()
	 */
	@Override
	public boolean isGuiRequired() {
		return false;
	}
	
	/**
	* @return marked traces or null if no special markers shall be added for output plug-ins
	*/
	public List<MarkedTrace> getMarkedTraces(){
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs,
			IScopeContext is) {
		return new IEclipsePreferences[] {cs.getNode(s_PLUGIN_ID)};
	}
}
