package local.stalin.plugins.generator.localvariablerenamer;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import local.stalin.access.IObserver;
import local.stalin.ep.interfaces.IGenerator;
import local.stalin.model.GraphType;
import local.stalin.model.IElement;
import local.stalin.model.MarkedTrace;
import local.stalin.model.TokenMap;

/**
 * Main class of Plug-In LocalVariableRenamer.
 * Input of this plugin is an unstructured Boogie program (e.g. output of the
 * BoogiePreprocessor).
 * Output of this plugin is the same Boogie program, where all local variables 
 * have been renamed. The variables are renamed by appending as suffix a
 * separator plus the name of their procedure.
 */
public class LocalVariableRenamer implements IGenerator {

	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	
	private LocalVariableRenamerObserver m_Observer;
	private GraphType m_InputDefinition;
	
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
    	m_Observer = new LocalVariableRenamerObserver();
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

	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ITool#setInputDefinition(local.stalin.model.GraphType)
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
	 * @see local.stalin.ep.interfaces.IModifyingTool#getOutputDefinition()
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
	 * @see local.stalin.ep.interfaces.IGenerator#getModel()
	 */
	@Override
	public IElement getModel() {
		// TODO Auto-generated method stub
		return null;
	}
	
	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ITool#getRequireGui()
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
	public IEclipsePreferences[] getPreferences(IScopeContext cs, IScopeContext is) {
		return null;
	}
}
