package local.stalin.plugins.generator.traceabstraction;
import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IElement;
import local.stalin.model.INode;
import local.stalin.plugins.ResultNotifier;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.traceabstraction.CegarLoop.Result;

import org.apache.log4j.Logger;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionObserver implements IUnmanagedObserver {
	


	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	/**
     * Root Node of this Stalin model. I use this to store information that
     * should be passed to the next plugin. The Successors of this node exactly
     * the initial nodes of procedures.
	 */
	private static INode m_graphroot = null;
	
	@Override
	public boolean process(IElement root) {
		RootNode rootNode = (RootNode) root;


		TAPreferences taPrefs = new TAPreferences(Activator.s_PLUGIN_ID);

		
		SmtManager smtManager = new SmtManager(
					rootNode.getRootAnnot().getBoogieVar2SmtVar(),
					taPrefs.solver(),
					rootNode.getRootAnnot().getGlobalVars(),
					taPrefs.dumpFormulas(),
					taPrefs.dumpPath());
	
		CegarLoopSequential cegarLoop = new CegarLoopSequential(
				rootNode, 
				smtManager, 
				taPrefs);
		
		s_Logger.info("Used settings are:");
		s_Logger.info("Interprocedural:" +  taPrefs.interprocedural());
		s_Logger.info("Solver: " + taPrefs.solver());
		s_Logger.info("Artifact: " + taPrefs.artifact());
		s_Logger.info("Interpolants for: " + taPrefs.interpolatedLocs());
		
		
		Result result = cegarLoop.iterate();
		String stat = "";
		stat += "Statistics:  ";
		stat += " Iterations " + cegarLoop.m_Iteration + ".";
		stat += " CFG has "; 
		stat +=	cegarLoop.m_InitialAbstractionSize;
		stat +=	" locations,";
		stat +=	cegarLoop.m_NumberOfErrorLocations;
		stat +=	" error locations.";
		stat += " Satisfiability queries: ";
		stat += smtManager.getTrivialSatQueries() + " tivial, ";
		stat += smtManager.getNontrivialSatQueries() + " nontrivial.";
		stat += " Biggest abstraction constructed in iteration "; 
		stat +=	cegarLoop.m_BiggestAbstractionIteration;
		stat +=	" and had ";
		stat +=	cegarLoop.m_BiggestAbstractionSize;
		stat += " states.";
		s_Logger.info(stat);
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
		return TraceAbstractionObserver.m_graphroot;
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
