/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
