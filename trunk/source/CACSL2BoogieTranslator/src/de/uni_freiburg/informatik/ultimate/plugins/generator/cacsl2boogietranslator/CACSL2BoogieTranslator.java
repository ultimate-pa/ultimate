/**
 * Main class of Plug-In CACSL2BoogieTranslator
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.Collections;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 03.02.2012
 */
public class CACSL2BoogieTranslator implements IGenerator {
	/**
	 * The plugin's name.
	 */
	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	/**
	 * The plugin's ID.
	 */
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	/**
	 * The observer instance.
	 */
	private CACSL2BoogieTranslatorObserver m_Observer;
	/**
	 * Input definition.
	 */
	private GraphType m_InputDefinition;
	/**
	 * The logger instance.
	 */
	public static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getName()
	 */
	@Override
    public String getName() {
        return s_PLUGIN_NAME;
    }

	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getPluginID()
	 */
	@Override
    public String getPluginID() {
        return s_PLUGIN_ID;
    }

	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java.lang.Object)
	 */
	@Override
    public int init(Object param) {
    	m_Observer = new CACSL2BoogieTranslatorObserver();
    	return 0;
    }

	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getQueryKeyword()
	 */
	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getDesiredToolID()
	 */
	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#setTokenMap(de.uni_freiburg.informatik.ultimate.model.TokenMap)
	 */
	@Override
	public void setTokenMap(TokenMap tokenMap) {
		// not required
	}

	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#setInputDefinition(de.uni_freiburg.informatik.ultimate.model.GraphType)
	 */
	@Override
	public void setInputDefinition(GraphType graphType) {
		this.m_InputDefinition = graphType;
	}

	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getObservers()
	 */
	@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList((IObserver) m_Observer);
	}
	
	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IModifyingTool#getOutputDefinition()
	 */
	@Override
	public GraphType getOutputDefinition() {
		return new GraphType(Activator.s_PLUGIN_ID,
				m_InputDefinition.getType(), m_InputDefinition.getFileNames());
	}
	
	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator#getModel()
	 */
	@Override
	public IElement getModel() {
		return this.m_Observer.getRoot();
	}
	
	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getRequireGui()
	 */
	@Override
	public boolean isGuiRequired() {
		return false;
	}
	
	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IModifyingTool#getMarkedTraces()
	 */
	@Override
	public List<MarkedTrace> getMarkedTraces(){
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getPreferences(org.eclipse.core.runtime.preferences.IScopeContext, org.eclipse.core.runtime.preferences.IScopeContext)
	 */
	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs,
			IScopeContext is) {
		return new IEclipsePreferences[] {cs.getNode(s_PLUGIN_ID)};
	}
}
