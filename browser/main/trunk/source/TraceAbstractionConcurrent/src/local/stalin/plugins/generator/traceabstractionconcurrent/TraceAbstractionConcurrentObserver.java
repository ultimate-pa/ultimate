package local.stalin.plugins.generator.traceabstractionconcurrent;
import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IElement;
import local.stalin.model.INode;
import local.stalin.plugins.ResultNotifier;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.traceabstraction.Activator;
import local.stalin.plugins.generator.traceabstraction.CegarLoopSequential;
import local.stalin.plugins.generator.traceabstraction.SmtManager;
import local.stalin.plugins.generator.traceabstraction.TAPreferences;
import local.stalin.plugins.generator.traceabstraction.CegarLoop.Result;
import local.stalin.plugins.generator.traceabstraction.preferences.PreferenceValues;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionConcurrentObserver implements IUnmanagedObserver {

	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	/**
     * Root Node of this Stalin model. I use this to store information that
     * should be passed to the next plugin. The Successors of this node exactly
     * the initial nodes of procedures.
	 */
	private static INode m_graphroot = null;
	
	
	@Override
	public boolean process(IElement root) {
		
		TAPreferences taPrefs = new TAPreferences("TraceAbstraction");
		
		RootNode rootNode = (RootNode) root;

		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode("TraceAbstraction");
		String dumphPath = prefs.get(PreferenceValues.NAME_DUMPPATH, PreferenceValues.DEF_DUMPPATH);
		s_Logger.warn(dumphPath);
		
		
		boolean petriNet = true;
		
		SmtManager smtManager = new SmtManager(
					rootNode.getRootAnnot().getBoogieVar2SmtVar(),
					taPrefs.solver(),
					rootNode.getRootAnnot().getGlobalVars(),
					false,
					dumphPath);
	

		CegarLoopSequential cegarLoop;
		
		if(petriNet) {
			cegarLoop = new CegarLoopJulian(
					rootNode, 
					smtManager, 
					taPrefs);
		}
		else {
			cegarLoop = new CegarLoopConcurrentAutomata(
					rootNode, 
					smtManager, 
					taPrefs);
		}
		
		Result result = cegarLoop.iterate();
		s_Logger.info("Statistics - number of theorem prover calls: " +
				smtManager.getNontrivialSatQueries());
		s_Logger.info("Statistics - iterations: " +
				cegarLoop.getIteration());
		s_Logger.info("Statistics - biggest abstraction: " +
				cegarLoop.m_BiggestAbstractionSize + " states");
		s_Logger.info("Statistics - biggest abstraction in iteration: " +
				cegarLoop.m_BiggestAbstractionIteration);
		switch (result) {
		case CORRECT:
			s_Logger.info("Program is correct");
			ResultNotifier.programCorrect();
			break;
		case INCORRECT:
			s_Logger.info("Program is incorrect");
			ResultNotifier.programIncorrect();
			break;
		case TIMEOUT:
			s_Logger.info("Insufficient iterations to proof correctness");
			ResultNotifier.programUnknown("Insufficient iterations to proof correctness");
			break;
		case UNKNOWN:
			s_Logger.info("Program might be incorrect, check conterexample.");
			ResultNotifier.programUnknown("Program might be incorrect, check" +
					" conterexample.");
			break;
		}
		
		m_graphroot = cegarLoop.getArtifact();

		return false;
	}
	

	
	/**
	 * @return the root of the CFG.
	 */
	public INode getRoot(){
		return m_graphroot;
	}	
	
	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

}
