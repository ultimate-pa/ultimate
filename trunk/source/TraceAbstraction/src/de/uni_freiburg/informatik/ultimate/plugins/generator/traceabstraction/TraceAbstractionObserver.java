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
	private RootNode m_BlockEncodedRcfgRootNode;
	private IElement m_RootOfNewModel;
	private WitnessNode m_WitnessNode;
	private boolean m_LastModel = false;
	private IToolchainStorage m_Storage;
	private GraphType m_CurrentGraphType;


	public TraceAbstractionObserver(IUltimateServiceProvider services, IToolchainStorage storage) {
		m_Services = services;
		m_Storage = storage;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}



	@Override
	public boolean process(IElement root) {
		if (root instanceof RootNode) {
			if (isOriginalRcfg(m_CurrentGraphType)) {
				if (m_RcfgRootNode == null) {
					m_RcfgRootNode = (RootNode) root;
				} else {
					throw new UnsupportedOperationException("two RCFG models form same source");
				}
			} 
			if (isBlockEncodingRcfg(m_CurrentGraphType)) {
				if (m_BlockEncodedRcfgRootNode == null) {
					m_BlockEncodedRcfgRootNode = (RootNode) root;
				} else {
					throw new UnsupportedOperationException("two RCFG models form same source");
				}
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

	private boolean isBlockEncodingRcfg(GraphType currentGraphType) {
		return currentGraphType.getCreator().equals("de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding");
	}
	
	private boolean isOriginalRcfg(GraphType currentGraphType) {
		return currentGraphType.getCreator().equals("de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder");
	}



	@Override
	public void finish() {
		if (m_LastModel) {
			final RootNode rcfgRootNode;
			if (m_BlockEncodedRcfgRootNode != null) {
				rcfgRootNode = m_BlockEncodedRcfgRootNode;
			} else {
				rcfgRootNode = m_RcfgRootNode;
			}
			
			if (rcfgRootNode == null) {
				throw new UnsupportedOperationException("TraceAbstraction needs an RCFG");
			} else {
				NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton;
				if (m_WitnessNode == null) {
					witnessAutomaton = null;
				} else {
					m_Logger.warn("Found a witness automaton. I will only consider traces that are accepted by the witness automaton");
					witnessAutomaton = (new WitnessModelToAutomatonTransformer(m_WitnessNode, m_Services)).getResult();
				}
				TraceAbstractionStarter tas = new TraceAbstractionStarter(m_Services, m_Storage, rcfgRootNode, witnessAutomaton);
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
		m_CurrentGraphType = modelType;
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
