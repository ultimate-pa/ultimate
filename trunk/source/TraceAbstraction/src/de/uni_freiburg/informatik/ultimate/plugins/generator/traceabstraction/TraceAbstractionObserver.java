package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessModelToAutomatonTransformer;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionObserver implements IUnmanagedObserver {

	private final Logger m_Logger;
	private final IUltimateServiceProvider m_Services;
	
	private RootNode m_RcfgRootNode;
	private IElement m_RootOfNewModel;
	private WitnessNode m_WitnessNode;
	private boolean m_LastModel = false;
	private IToolchainStorage m_Storage;


	public TraceAbstractionObserver(IUltimateServiceProvider services, IToolchainStorage storage) {
		m_Services = services;
		m_Storage = storage;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}



	@Override
	public boolean process(IElement root) {
		if (root instanceof RootNode) {
			if (m_RcfgRootNode == null) {
				m_RcfgRootNode = (RootNode) root;
			} else {
				throw new UnsupportedOperationException("two RCFG models");
			}
		}
		if (root instanceof WitnessNode) {
			if (m_WitnessNode == null) {
				m_WitnessNode = (WitnessNode) root;
			} else {
				throw new UnsupportedOperationException("two witness models");
			}
		}
		
		
		return false;
	}

	@Override
	public void finish() {
		if (m_LastModel) {
			if (m_RcfgRootNode == null) {
				throw new UnsupportedOperationException("TraceAbstraction needs an RCFG");
			} else {
				NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton;
				if (m_WitnessNode == null) {
					witnessAutomaton = null;
				} else {
					m_Logger.warn("Found a witness automaton. I will only consider traces that are accepted by the witness automaton");
					witnessAutomaton = (new WitnessModelToAutomatonTransformer(m_WitnessNode, m_Services)).getResult();
				}
				TraceAbstractionStarter tas = new TraceAbstractionStarter(m_Services, m_Storage, m_RcfgRootNode, witnessAutomaton);
				m_RootOfNewModel = tas.getRootOfNewModel();
			}
		}
	}
	
	/**
	 * @return the root of the CFG.
	 */
	public IElement getRootOfNewModel() {
		return m_RootOfNewModel;
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) {
		if (currentModelIndex == numberOfModels -1) {
			m_LastModel = true;
		}
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}



}
