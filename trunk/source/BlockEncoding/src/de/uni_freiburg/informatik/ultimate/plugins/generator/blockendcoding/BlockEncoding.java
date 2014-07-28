package de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding;

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
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.preferences.PreferenceInitializer;

/**
 * Main class of Plug-In BlockEndcoding
 * 
 * 
 * TODO: refine comments
 * 
 */
public class BlockEncoding implements IGenerator {

	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;

	private MinModelConversionObserver mConversionObserver;
	private BlockEncodingObserver mBlockEncodingObserver;
	private GraphType m_InputDefinition;
	private IUltimateServiceProvider mServices;

	@Override
	public String getPluginName() {
		return s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	@Override
	public int init() {
		Logger logger = mServices.getLoggingService().getLogger(s_PLUGIN_ID);
		mConversionObserver = new MinModelConversionObserver(mServices);
		mBlockEncodingObserver = new BlockEncodingObserver(logger);
		return 0;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		this.m_InputDefinition = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(mBlockEncodingObserver);
		observers.add(mConversionObserver);
		return observers;
	}

	public GraphType getOutputDefinition() {
		if (mConversionObserver.getRoot() == null) {
			return new GraphType("BlockEncodedModel", m_InputDefinition.getType(), m_InputDefinition.getFileNames());
		}
		return new GraphType(Activator.s_PLUGIN_ID, m_InputDefinition.getType(), m_InputDefinition.getFileNames());
	}

	@Override
	public IElement getModel() {
		if (mConversionObserver.getRoot() == null) {
			return mBlockEncodingObserver.getRoot();
		}
		return this.mConversionObserver.getRoot();
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(IToolchainStorage services) {

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
	}
}
