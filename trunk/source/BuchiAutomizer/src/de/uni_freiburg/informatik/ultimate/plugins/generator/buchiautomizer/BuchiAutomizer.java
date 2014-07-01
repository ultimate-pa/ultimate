package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Collections;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;

/**
 * Main class of Plug-In BuchiAutomizer
 * 
 *
 * TODO: refine comments
 * 
 */
public class BuchiAutomizer implements IGenerator {

	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private BuchiAutomizerObserver m_Observer;
	private GraphType m_InputDefinition;
	
	
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
    public int init() {
    	m_Observer = new BuchiAutomizerObserver();
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
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#setInputDefinition(de.uni_freiburg.informatik.ultimate.model.GraphType)
	 */
	@Override
	public void setInputDefinition(GraphType graphType) {
		this.m_InputDefinition = graphType;
	}

	//@Override
	public List<IObserver> getObservers() {
		if (programContainsErrors()) {
			s_Logger.info("Another Plugin discovered errors, I will "
					+ "not analyze termination");
			return Collections.emptyList();
		} else {
			s_Logger.info("Safety of program was proven or not checked, "
					+ "starting termination analysis");
			return Collections.singletonList((IObserver) m_Observer);
		}
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
		return m_Observer.getModel();
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getRequireGui()
	 */
	@Override
	public boolean isGuiRequired() {
		return false;
	}
	

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}
	
	
	private boolean programContainsErrors() {
		for (Entry<String, List<IResult>> entry : UltimateServices.getInstance().getResultMap().entrySet()) {
			for (IResult resul : entry.getValue()) {
				if (resul instanceof CounterExampleResult) {
					return true;
				}
			}
		}
		return false;
	}
}
