package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * Main class of Plug-In RankingFunctions
 * 
 *
 * TODO: refine comments
 * 
 */
public class RankingFunctions implements IGenerator {
	
	public static final boolean s_DEBUG_UNSATCORE = false;

	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	
	private RankingFunctionsObserver m_Observer;
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
    	m_Observer = new RankingFunctionsObserver();
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
		return this.m_Observer.getRoot();
//		return null;
	}
	
	/* (non-Javadoc)
	 * @see local.stalin.ep.interfaces.ITool#getRequireGui()
	 */
	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}
}
