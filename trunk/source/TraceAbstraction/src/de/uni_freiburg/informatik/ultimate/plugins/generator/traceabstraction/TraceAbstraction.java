package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * Main class of Plug-In TraceAbstraction
 * 
 * 
 * TODO: refine comments
 * 
 */
public class TraceAbstraction implements IGenerator {

	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;

	private TraceAbstractionObserver m_Observer;
	private GraphType m_InputDefinition;
	private IToolchainStorage mStorage;
	private IUltimateServiceProvider mServices;
	private RootNodeFilterObserver<RootNode> m_RcfgRootFilter;
	private RootNodeFilterObserver<WitnessNode> m_WitnessRootFilter;

	@Override
	public String getPluginName() {
		return s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	@Override
	public void init() {
		m_RcfgRootFilter = new RootNodeFilterObserver<RootNode>(RootNode.class);
		m_WitnessRootFilter = new RootNodeFilterObserver<WitnessNode>(WitnessNode.class);
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.ALL;
	}

	@Override
	public List<String> getDesiredToolID() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		this.m_InputDefinition = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		m_Observer = new TraceAbstractionObserver(mServices);
		List<IObserver> observers = new ArrayList<IObserver>();
//		observers.add(m_RcfgRootFilter);
//		observers.add(m_WitnessRootFilter);
		observers.add(m_Observer);
		return observers;
	}

	public GraphType getOutputDefinition() {
		/*
		 * TODO This generated method body only assumes a standard case. Adapt
		 * it if necessary. Otherwise remove this todo-tag.
		 */
		return new GraphType(Activator.s_PLUGIN_ID, m_InputDefinition.getType(), m_InputDefinition.getFileNames());
	}

	@Override
	public IElement getModel() {
		return this.m_Observer.getRootOfNewModel();
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new TraceAbstractionPreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		mStorage = storage;

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
