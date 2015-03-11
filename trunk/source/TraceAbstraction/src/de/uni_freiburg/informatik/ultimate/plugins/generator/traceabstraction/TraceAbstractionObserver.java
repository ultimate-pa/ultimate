package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessAutomatonLetter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessModelToAutomatonTransformer;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.InvariantResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.result.ResultUtil;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionObserver implements IUnmanagedObserver {

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	
	private RootNode m_RcfgRootNode;
	private IElement m_RootOfNewModel;
	private WitnessNode m_WitnessNode;
	private boolean m_LastModel = false;


	public TraceAbstractionObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
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
				NestedWordAutomaton<WitnessAutomatonLetter, WitnessNode> witnessAutomaton;
				if (m_WitnessNode == null) {
					witnessAutomaton = null;
				} else {
					mLogger.warn("Found a witness automaton. I will only consider traces that are accepted by the witness automaton");
					witnessAutomaton = (new WitnessModelToAutomatonTransformer(m_WitnessNode, mServices)).getResult();
				}
				TraceAbstractionStarter tas = new TraceAbstractionStarter(mServices, m_RcfgRootNode, witnessAutomaton);
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
