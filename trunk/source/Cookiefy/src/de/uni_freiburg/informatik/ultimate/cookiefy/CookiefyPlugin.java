package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.cookiefy.Activator;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;

public class CookiefyPlugin implements IGenerator {
	
	private static final String s_PLUGIN_NAME = "Cookiefy";
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;

	private CookiefyAlgorithm m_CookiefyAlgorithm;
	private GraphType m_InputType;
	
	public static Logger logger =
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	@Override
	public GraphType getOutputDefinition() {
		try 
		{
			return new GraphType(getPluginID(), GraphType.Type.AST, m_InputType.getFileNames());
		}
		catch(Exception e) {
			return null;	
		}
	}

	@Override
	public List<MarkedTrace> getMarkedTraces() {
		return null;
	}
	
	@Override
	public IElement getModel() {
		return this.m_CookiefyAlgorithm.getRoot();
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	/**
	 * don't used.
	 */
	@Override
	public void setTokenMap(TokenMap tokenMap) {}

	@Override
	public QueryKeyword getQueryKeyword() {
		return  QueryKeyword.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		// don't need a special tool
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		this.m_InputType = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		//Attention: Every observer here operates on the input
		//model given to the plugin - not the resulting model
		//of the Cookiefy algorithm, even if the observer follows the
		//m_CookiefyAlgorithm observer!
		//If you want to print the AST use the BoogiePrinter in the
		//toolchain.
		observers.add(m_CookiefyAlgorithm);
		return observers;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs,
			IScopeContext is) {
		return null;
		//look how it is done in DSITransformer
		//return new IEclipsePreferences[] {cs.getNode(s_PLUGIN_ID)};
	}

	@Override
	public int init(Object params) {
		m_CookiefyAlgorithm = new CookiefyAlgorithm();
		return 0;
	}

	@Override
	public String getName() {
		return s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}

}
