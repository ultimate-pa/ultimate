package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class CookiefyPlugin implements IGenerator {

	private static final String s_PLUGIN_NAME = "Cookiefy";
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;

	private CookiefyAlgorithm m_CookiefyAlgorithm;
	private GraphType m_InputType;
	private Logger mLogger;

	@Override
	public GraphType getOutputDefinition() {
		try {
			return new GraphType(getPluginID(), GraphType.Type.AST, m_InputType.getFileNames());
		} catch (Exception e) {
			return null;
		}
	}

	@Override
	public IElement getModel() {
		return this.m_CookiefyAlgorithm.getRoot();
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
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
		// Attention: Every observer here operates on the input
		// model given to the plugin - not the resulting model
		// of the Cookiefy algorithm, even if the observer follows the
		// m_CookiefyAlgorithm observer!
		// If you want to print the AST use the BoogiePrinter in the
		// toolchain.
		m_CookiefyAlgorithm = new CookiefyAlgorithm(mLogger);
		observers.add(m_CookiefyAlgorithm);
		return observers;
	}

	@Override
	public int init() {

		return 0;
	}

	@Override
	public String getPluginName() {
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

	@Override
	public void setToolchainStorage(IToolchainStorage services) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(s_PLUGIN_ID);

	}

}
