package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;
import java.text.MessageFormat;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult.Severity;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class BuchiAutomizerObserver implements IUnmanagedObserver {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private IElement m_graphroot;
	private SmtManager smtManager;
	private TAPreferences m_Pref;

	private RootAnnot rootAnnot;
	
	
	

	
	

	
	
	
	@Override
	public boolean process(IElement root) {
		rootAnnot = ((RootNode) root).getRootAnnot();
		TAPreferences taPrefs = rootAnnot.getTaPrefs();
		m_graphroot = root;
		
		String settings = "Automizer settings:";
		settings += " Hoare:"+ taPrefs.computeHoareAnnotation();
		settings += " " + (taPrefs.differenceSenwa() ? "SeNWA" : "NWA");
		settings += " Solver:" + taPrefs.solver();
		settings += " Determinization: " + taPrefs.determinization();
		settings += " Letter:" + taPrefs.letter();
		settings += " Timeout:" + taPrefs.timeout();
		System.out.println(settings);

		smtManager = new SmtManager(rootAnnot.getBoogie2Smt(),
				taPrefs.solver(), rootAnnot.getGlobalVars(), rootAnnot.getModGlobVarManager(),
				taPrefs.dumpFormulas(), taPrefs.dumpPath());

		m_Pref = rootAnnot.getTaPrefs();
		
		BuchiCegarLoop bcl = new BuchiCegarLoop((RootNode) root, smtManager, m_Pref);
		Result result = bcl.iterate();
		
		if (result == Result.TERMINATING) {
			for (String proc : rootAnnot.getEntryNodes().keySet()) {
				ProgramPoint position = rootAnnot.getEntryNodes().get(proc);
				String shortDescr = "Terminating procedure";
				String longDescr = "Procedure " + proc + " is terminating";
				ILocation loc = position.getPayload().getLocation();
				IResult reportRes= new GenericResult<RcfgElement>(position, 
						Activator.s_PLUGIN_ID, 
						UltimateServices.getInstance().getTranslatorSequence(), 
						loc, 
						shortDescr, 
						longDescr, Severity.INFO);
				s_Logger.info(shortDescr + longDescr + " line" + loc.getStartLine());
				reportResult(reportRes);
			}
			s_Logger.info("Ultimate Buchi Automizer: Termination proven.");
		} else if (result == Result.UNKNOWN) {
			NestedLassoRun<CodeBlock, IPredicate> counterexample = bcl.getCounterexample();
			IPredicate hondaPredicate = counterexample.getLoop().getStateAtPosition(0);
			ProgramPoint honda = ((ISLPredicate) hondaPredicate).getProgramPoint();
			String shortDescr = "Program might not terminate.";
			StringBuilder longDescr = new StringBuilder();
			longDescr.append("Maybe this program point can be visited infinitely often. ");
			longDescr.append("Unable to synthesize ranking function for the following lasso. ");
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append("Stem: ");
			longDescr.append(counterexample.getStem().getWord());
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append("Loop: ");
			longDescr.append(counterexample.getLoop().getWord());			
			ILocation loc = honda.getPayload().getLocation();
			IResult reportRes= new GenericResult<RcfgElement>(honda, 
					Activator.s_PLUGIN_ID, 
					UltimateServices.getInstance().getTranslatorSequence(), 
					loc, 
					shortDescr, 
					longDescr.toString(), Severity.ERROR);
			s_Logger.info(shortDescr + longDescr + " line" + loc.getStartLine());
			reportResult(reportRes);
			
			s_Logger.info("Ultimate Buchi Automizer: Unable to prove termination. Nonterminating?");
		} else if (result == Result.TIMEOUT) {
			for (String proc : rootAnnot.getEntryNodes().keySet()) {
				ProgramPoint position = rootAnnot.getEntryNodes().get(proc);
				String longDescr = "Unable to prove termination of procedure" + proc;
				ILocation loc = position.getPayload().getLocation();
				IResult reportRes= new TimeoutResult<RcfgElement>(position, 
						Activator.s_PLUGIN_ID, 
						UltimateServices.getInstance().getTranslatorSequence(), 
						loc, 
						longDescr);
				s_Logger.info(longDescr + " line" + loc.getStartLine());
				reportResult(reportRes);
			}
		} else {
			throw new AssertionError();
		}
		s_Logger.info(MessageFormat.format("Statistics: Counterexamples: {0} infeasible" +
				"  {1} rank without si  {2} rank only with si", 
				bcl.m_Infeasible, bcl.m_RankWithoutSi, bcl.m_RankWithSi));;

//		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
//		Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
//		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
//			errNodesOfAllProc.addAll(errNodeOfProc);
//		}
//
//		long timoutMilliseconds = taPrefs.timeout() * 1000;
//		UltimateServices.getInstance().setDeadline(
//				System.currentTimeMillis() + timoutMilliseconds);
//		
//
//		BuchiIsEmpty<CodeBlock, IPredicate> ec = null;
//
//		NestedLassoRun<CodeBlock, IPredicate> ctx = null;
//		NestedWord<CodeBlock> stem = ctx.getStem().getWord();
//		s_Logger.info("Stem: " + stem);
//		NestedWord<CodeBlock> loop = ctx.getLoop().getWord();
//		s_Logger.info("Loop: " + loop);
//		m_Iteration = 0;
//		LBool feasibility = null;
//		while (feasibility == LBool.UNSAT) {
//
//			try {
//				ec = new BuchiIsEmpty<CodeBlock, IPredicate>(m_Abstraction);
//			} catch (OperationCanceledException e) {
//				s_Logger.info("Statistics: Timout");
//				return false;
//			}
//			ctx = ec.getAcceptingNestedLassoRun();
//			if (ctx == null) {
//				s_Logger.warn("Statistics: Trivially terminating");
//				return false;
//			}
//			stem = ctx.getStem().getWord();
//			s_Logger.info("Stem: " + stem);
//			loop = ctx.getLoop().getWord();
//			s_Logger.info("Loop: " + loop);
//			m_Iteration++;
////			feasibility = checkFeasibility(ctx, rootAnnot);
//		}
//		m_TraceChecker.forgetTrace();


		


		return false;
	}
	
	

	
	static void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
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


	public IElement getModel() {
		return m_graphroot;
	}
	
//	public static TransFormula sequentialComposition(int serialNumber, 
//			Boogie2SMT boogie2smt, TransFormula... transFormulas) {
//		TransFormula result = transFormulas[0];
//		for (int i=1; i<transFormulas.length; i++) {
//			result = TransFormula.sequentialComposition(result, transFormulas[i],  boogie2smt, serialNumber++);
//		}
//		return result;
//	}

}
