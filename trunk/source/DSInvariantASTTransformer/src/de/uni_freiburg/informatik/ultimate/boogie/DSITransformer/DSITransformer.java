package de.uni_freiburg.informatik.ultimate.boogie.DSITransformer;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * This Class transforms a Boogie AST into a new one to generate data structure
 * invariants
 * 
 * @author arenis
 * 
 */

public class DSITransformer implements IGenerator {

	private static final String s_PLUGIN_NAME = "DSITransformer";
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;

	private DSITransformerObserver mObserver;
	private GraphType mInputType;
	private IUltimateServiceProvider mServices;

	/**
	 * I don't need a special tool
	 */
	public List<String> getDesiredToolID() {
		return null;
	}

	public IElement getModel() {
		return mObserver.getRoot();
	}

	public String getPluginName() {
		return s_PLUGIN_NAME;
	}

	@Override
	public List<IObserver> getObservers() {
		mObserver = new DSITransformerObserver(mServices.getLoggingService().getLogger(s_PLUGIN_ID));
		return Collections.singletonList((IObserver) mObserver);
	}

	public GraphType getOutputDefinition() {
		try {
			return new GraphType(getPluginID(), GraphType.Type.AST, mInputType.getFileNames());
		} catch (Exception e) {
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

	public void init() {
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	public void setInputDefinition(GraphType graphType) {
		mInputType = graphType;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setToolchainStorage(IToolchainStorage services) {

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}
}
