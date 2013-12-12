package de.uni_freiburg.informatik.ultimate.boogie.DSITransformer;

import java.util.Collections;
import java.util.List;


import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.INode;

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


	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}
}
