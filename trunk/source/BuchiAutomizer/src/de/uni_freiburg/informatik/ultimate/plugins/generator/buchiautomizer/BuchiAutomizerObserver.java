package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;
import java.text.MessageFormat;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionObserver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.result.BackTranslationWorkaround;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult.Severity;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.NonterminatingLassoResult;
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
		TAPreferences taPrefs = new TAPreferences();
		m_graphroot = root;
		
		String settings = "Automizer settings:";
		settings += " Hoare:"+ taPrefs.computeHoareAnnotation();
		settings += " " + (taPrefs.differenceSenwa() ? "SeNWA" : "NWA");
		settings += " Determinization: " + taPrefs.determinization();
		settings += " Timeout:" + taPrefs.timeout();
//		System.out.println(settings);
		TraceAbstractionObserver.setTimeout(taPrefs);

		smtManager = new SmtManager(rootAnnot.getBoogie2SMT(),
				rootAnnot.getGlobalVars(), rootAnnot.getModGlobVarManager());

		m_Pref = taPrefs;
		
		BuchiCegarLoop bcl = new BuchiCegarLoop((RootNode) root, smtManager, m_Pref);
		Result result = bcl.iterate();
		
		if (result == Result.TERMINATING) {
			ProgramPoint position = rootAnnot.getEntryNodes().values().iterator().next();
				String shortDescr = "Buchi Automizer proved that your program is terminating";
				String longDescr = statistics(bcl);
				ILocation loc = position.getPayload().getLocation();
				IResult reportRes= new GenericResult<RcfgElement>(position, 
						Activator.s_PLUGIN_ID, 
						UltimateServices.getInstance().getTranslatorSequence(), 
						loc, 
						shortDescr, 
						longDescr, Severity.INFO);
//				s_Logger.info(shortDescr + longDescr + " line" + loc.getStartLine());
				reportResult(reportRes);
			s_Logger.info(shortDescr);
		} else if (result == Result.UNKNOWN) {
			NestedLassoRun<CodeBlock, IPredicate> counterexample = bcl.getCounterexample();
			IPredicate hondaPredicate = counterexample.getLoop().getStateAtPosition(0);
			ProgramPoint honda = ((ISLPredicate) hondaPredicate).getProgramPoint();
			String shortDescr = "Buchi Automizer was unable to decide termination";
			StringBuilder longDescr = new StringBuilder();
//			longDescr.append("Maybe this program point can be visited infinitely often. ");
			longDescr.append("Maybe your program is nonterminating!?! ");
			longDescr.append("I was unable to synthesize ranking function for the following lasso. ");
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
//			s_Logger.info(shortDescr + longDescr + " line" + loc.getStartLine());
			reportResult(reportRes);
			s_Logger.info(shortDescr);
		} else if (result == Result.TIMEOUT) {
			ProgramPoint position = rootAnnot.getEntryNodes().values().iterator().next();
			String longDescr = "Timeout while trying to prove termination";
			IResult reportRes= new TimeoutResult<RcfgElement>(position, 
					Activator.s_PLUGIN_ID, 
					UltimateServices.getInstance().getTranslatorSequence(), 
					position.getPayload().getLocation(), 
					longDescr);
//			for (String proc : rootAnnot.getEntryNodes().keySet()) {
//				ProgramPoint position = rootAnnot.getEntryNodes().get(proc);
//				String longDescr = "Unable to prove termination of procedure" + proc;
//				ILocation loc = position.getPayload().getLocation();
//				IResult reportRes= new TimeoutResult<RcfgElement>(position, 
//						Activator.s_PLUGIN_ID, 
//						UltimateServices.getInstance().getTranslatorSequence(), 
//						loc, 
//						longDescr);
//				s_Logger.info(longDescr + " line" + loc.getStartLine());
				reportResult(reportRes);
//			}
		} else if (result == Result.NONTERMINATING) {
			NestedLassoRun<CodeBlock, IPredicate> counterexample = bcl.getCounterexample();
			IPredicate hondaPredicate = counterexample.getLoop().getStateAtPosition(0);
			ProgramPoint honda = ((ISLPredicate) hondaPredicate).getProgramPoint();
			NonTerminationArgument nta = bcl.getNonTerminationArgument();
			Map<Integer, ProgramState<Expression>> partialProgramStateMapping = Collections.emptyMap();
			
			RcfgProgramExecution stemPE = new RcfgProgramExecution(
					counterexample.getStem().getWord().lettersAsList(), 
					partialProgramStateMapping, 
					new Map[counterexample.getStem().getLength()]);
			RcfgProgramExecution loopPE = new RcfgProgramExecution(
					counterexample.getLoop().getWord().lettersAsList(), 
					partialProgramStateMapping, 
					new Map[counterexample.getLoop().getLength()]);
			IResult reportRes = new NonterminatingLassoResult<RcfgElement>(
					honda, Activator.s_PLUGIN_ID, 
					UltimateServices.getInstance().getTranslatorSequence(), 
					stemPE, loopPE, honda.getPayload().getLocation());
//			IResult reportRes = new NonTerminationArgumentResult<RcfgElement>(
//					honda, Activator.s_PLUGIN_ID, nta.getStateInit(), 
//					nta.getStateHonda(), nta.getRay(), nta.getLambda(),
//					UltimateServices.getInstance().getTranslatorSequence(), 
//					honda.getPayload().getLocation());
			reportResult(reportRes);
			s_Logger.info(reportRes.getShortDescription());
			s_Logger.info(reportRes.getLongDescription());
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
	

			
			

	
	private String backtranslateExprWorkaround(Expression expr) {
		List<ITranslator<?, ?, ?, ?>> translators = 
				UltimateServices.getInstance().getTranslatorSequence();
		return BackTranslationWorkaround.backtranslate(translators, expr);
	}
	
	

	private String statistics(BuchiCegarLoop bcl) {
//		TreeMap<Integer, Integer> ms = bcl.getModuleSize();
		int modules = bcl.getModuleSizeTrivial().size() + bcl.getModuleSizeDeterministic().size() + bcl.getModuleSizeNondeterministic().size();
		TreeMap<Integer, RankingFunction> rf = bcl.getRankingFunction();
		if (modules == 0) {
			return "Trivially terminating. There is no loop in your program.";
		}
		int modulesWithTrivialRankingFunction = 0;
		int maxNumberOfStatesOfModuleWithTrivialRankingFunction = 0;
		StringBuilder sb = new StringBuilder();
		sb.append("Your program was decomposed into ");
		sb.append(modules);
		sb.append(" modules. ");
		sb.append("(");
		sb.append(bcl.getModuleSizeTrivial().size());
		sb.append(" trivial, ");
		sb.append(bcl.getModuleSizeDeterministic().size());
		sb.append(" deterministic, ");
		sb.append(bcl.getModuleSizeNondeterministic().size());
		sb.append(" nondeterministic)");
		for (Entry<Integer, Integer> entry  : bcl.getModuleSizeDeterministic().entrySet()) {
			if (rf.containsKey(entry.getKey())) {
				sb.append("One deterministic module has ");
				sb.append(prettyPrintRankingFunction(rf.get(entry.getKey())));
				sb.append(" and consists of ");
				sb.append(entry.getValue());
				sb.append(" states. ");
			} else {
				modulesWithTrivialRankingFunction++;
				if (entry.getValue() > maxNumberOfStatesOfModuleWithTrivialRankingFunction) {
					maxNumberOfStatesOfModuleWithTrivialRankingFunction = entry.getValue();
				}
			}
		}
		for (Entry<Integer, Integer> entry  : bcl.getModuleSizeNondeterministic().entrySet()) {
			if (rf.containsKey(entry.getKey())) {
				sb.append("One nondeterministic module has ");
				sb.append(prettyPrintRankingFunction(rf.get(entry.getKey())));
				sb.append(" and consists of ");
				sb.append(entry.getValue());
				sb.append(" states. ");
			} else {
				modulesWithTrivialRankingFunction++;
				if (entry.getValue() > maxNumberOfStatesOfModuleWithTrivialRankingFunction) {
					maxNumberOfStatesOfModuleWithTrivialRankingFunction = entry.getValue();
				}
			}
		}
		sb.append(modulesWithTrivialRankingFunction);
		sb.append(" modules have a trivial ranking function, the largest among these consists of ");
		sb.append(maxNumberOfStatesOfModuleWithTrivialRankingFunction);
		sb.append(" states.");
		return sb.toString();
	}
	
	private String prettyPrintRankingFunction(RankingFunction rf) {
		StringBuilder sb = new StringBuilder();
		sb.append(rf.getClass().getSimpleName());
		sb.append(" ");
		Expression[] lex = rf.asLexExpression(smtManager.getScript(), smtManager.getSmt2Boogie());
		for (Expression expr : lex) {
			sb.append(backtranslateExprWorkaround(expr));
		}
		return sb.toString();
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
