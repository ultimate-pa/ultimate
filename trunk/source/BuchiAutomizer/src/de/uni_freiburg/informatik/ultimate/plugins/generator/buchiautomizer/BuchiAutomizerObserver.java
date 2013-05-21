package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;
import org.omg.PortableInterceptor.SUCCESSFUL;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization.AutomatonTransition.Transition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.RankingFunctionsObserver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.RankingFunctionsSynthesizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.TermIsNotAffineException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.templates.LinearTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.StrongestPostDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.AllIntegers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class BuchiAutomizerObserver implements IUnmanagedObserver {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private IElement m_graphroot;
	private SmtManager smtManager;
	private IPredicate[] m_Interpolants;
	private IRun<CodeBlock, IPredicate> m_Counterexample;
	private IPredicate m_TruePredicate;
	private IPredicate m_FalsePredicate;
	private TAPreferences m_Pref;
	private int m_Iteration;
	private NestedWordAutomaton<CodeBlock, IPredicate> m_InterpolAutomaton;
	private NestedWordAutomaton<CodeBlock, IPredicate> m_Abstraction;
	private TraceChecker m_TraceChecker;
	private PredicateFactoryRefinement m_StateFactoryForRefinement;
	private BinaryStatePredicateManager m_Binarizer;
	
	
	
	private LBool checkFeasibility(NestedLassoRun<CodeBlock, IPredicate> ctx, RootAnnot rootAnnot) {
		NestedRun<CodeBlock, IPredicate> stem = ctx.getStem();
		s_Logger.info("Stem: " + stem);
		NestedRun<CodeBlock, IPredicate> loop = ctx.getLoop();
		s_Logger.info("Loop: " + loop);
		m_Counterexample = stem.concatenate(loop);

		m_TraceChecker = new TraceChecker(smtManager,
				rootAnnot.getModifiedVars(),
				rootAnnot.getEntryNodes(),
				null);
		m_TruePredicate = smtManager.newTruePredicate();
		m_FalsePredicate = smtManager.newFalsePredicate();

		LBool feasibility = m_TraceChecker.checkTrace(
				m_TruePredicate, m_FalsePredicate, m_Counterexample.getWord());
		return feasibility;
	}
	
	
	protected void constructInterpolantAutomaton() {
		InterpolantAutomataBuilder iab = new InterpolantAutomataBuilder(
						m_Counterexample,
						m_TruePredicate,
						m_FalsePredicate,
						m_Interpolants,
						m_Pref.interpolantAutomaton(), m_Pref.edges2True(),
						smtManager, m_Pref,
						m_Iteration, null);
		m_InterpolAutomaton = iab.buildInterpolantAutomaton(
				m_Abstraction, m_Abstraction.getStateFactory());
		
		assert(m_InterpolAutomaton.accepts(m_Counterexample.getWord())) :
			"Interpolant automaton broken!";
		assert (smtManager.checkInductivity(m_InterpolAutomaton, false, true));
	}
	
	
	
	@Override
	public boolean process(IElement root) {
		RootAnnot rootAnnot = ((RootNode) root).getRootAnnot();
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
				taPrefs.solver(), rootAnnot.getGlobalVars(), rootAnnot.getModifiedVars(),
				taPrefs.dumpFormulas(), taPrefs.dumpPath());
		m_Binarizer = new BinaryStatePredicateManager(smtManager);
		m_Pref = rootAnnot.getTaPrefs();
		
		m_StateFactoryForRefinement = new PredicateFactoryRefinement(
				rootAnnot.getProgramPoints(),
				null,
				smtManager,
				m_Pref,
				false,
				null);

		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		long timoutMilliseconds = taPrefs.timeout() * 1000;
		UltimateServices.getInstance().setDeadline(
				System.currentTimeMillis() + timoutMilliseconds);
		
		CFG2NestedWordAutomaton cFG2NestedWordAutomaton = 
				new CFG2NestedWordAutomaton(rootAnnot.getTaPrefs(),smtManager);
			PredicateFactory defaultStateFactory = new PredicateFactory(
					smtManager,
					rootAnnot.getTaPrefs());
		Collection<ProgramPoint> allpp = new HashSet<ProgramPoint>();
		for (Map<String, ProgramPoint> test : rootAnnot.getProgramPoints().values()) {
			allpp.addAll(test.values());
		}
		m_Abstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(
				((RootNode) root), defaultStateFactory, allpp);
		
		BuchiIsEmpty<CodeBlock, IPredicate> ec;
		try {
			ec = new BuchiIsEmpty<CodeBlock, IPredicate>(m_Abstraction);
		} catch (OperationCanceledException e2) {
			s_Logger.info("Statistics: Timout");
			return false;
		}
		NestedLassoRun<CodeBlock, IPredicate> ctx = ec.getAcceptingNestedLassoRun();
		if (ctx == null) {
			s_Logger.warn("Statistics: Trivially terminating");
			return false;
		}
		NestedWord<CodeBlock> stem = ctx.getStem().getWord();
		s_Logger.info("Stem: " + stem);
		NestedWord<CodeBlock> loop = ctx.getLoop().getWord();
		s_Logger.info("Loop: " + loop);
		m_Iteration = 0;
		LBool feasibility = checkFeasibility(ctx, rootAnnot);
		while (feasibility == LBool.UNSAT) {
			AllIntegers allInt = new TraceChecker.AllIntegers();
			m_Interpolants = m_TraceChecker.getInterpolants(allInt);
			constructInterpolantAutomaton();
			StrongestPostDeterminizer spd = new StrongestPostDeterminizer(
					smtManager, m_Pref, m_InterpolAutomaton);
			DifferenceDD<CodeBlock, IPredicate> diff = null;
			try {
				diff = new DifferenceDD<CodeBlock, IPredicate>(
						m_Abstraction, m_InterpolAutomaton, spd, 
						m_StateFactoryForRefinement,
						false, true);
			} catch (AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			try {
				m_Abstraction = (NestedWordAutomaton<CodeBlock, IPredicate>) diff.getResult();
			} catch (OperationCanceledException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			try {
				ec = new BuchiIsEmpty<CodeBlock, IPredicate>(m_Abstraction);
			} catch (OperationCanceledException e) {
				s_Logger.info("Statistics: Timout");
				return false;
			}
			ctx = ec.getAcceptingNestedLassoRun();
			if (ctx == null) {
				s_Logger.warn("Statistics: Trivially terminating");
				return false;
			}
			stem = ctx.getStem().getWord();
			s_Logger.info("Stem: " + stem);
			loop = ctx.getLoop().getWord();
			s_Logger.info("Loop: " + loop);
			m_Iteration++;
			feasibility = checkFeasibility(ctx, rootAnnot);
		}
		m_TraceChecker.forgetTrace();


		
		CodeBlock[] stemCBs = new CodeBlock[stem.length()];
		for (int i=0; i<stem.length(); i++) {
			stemCBs[i] = stem.getSymbol(i);
		}
		CodeBlock[] loopCBs = new CodeBlock[loop.length()];
		for (int i=0; i<loop.length(); i++) {
			loopCBs[i] = loop.getSymbol(i);
		}
		@SuppressWarnings("deprecation")
		TransFormula stemTF = SequentialComposition.getInterproceduralTransFormula(rootAnnot.getBoogie2SMT(), false, stemCBs);
		int stemVars = stemTF.getFormula().getFreeVars().length;

		@SuppressWarnings("deprecation")
		TransFormula loopTF = SequentialComposition.getInterproceduralTransFormula(rootAnnot.getBoogie2SMT(), false, loopCBs);
		int loopVars = loopTF.getFormula().getFreeVars().length;
		s_Logger.info("Statistics: stemVars: " + stemVars + "loopVars: " + loopVars);
		{
			List<CodeBlock> composedCB = new ArrayList<CodeBlock>();
			composedCB.addAll(Arrays.asList(stemCBs));
			composedCB.addAll(Arrays.asList(loopCBs));
//			composedCB.addAll(Arrays.asList(loopCBs));
			TransFormula composed = SequentialComposition.getInterproceduralTransFormula(rootAnnot.getBoogie2SMT(), false, composedCB.toArray(new CodeBlock[0])); 
					//TransFormula.sequentialComposition(10000, rootAnnot.getBoogie2SMT(), stemTF, loopTF);
			if (composed.isInfeasible() == Infeasibility.INFEASIBLE) {
				throw new AssertionError("suddently infeasible");
			}
		}
		NestedWord<CodeBlock> emptyWord = new NestedWord<CodeBlock>();
		boolean withoutStem = synthesize(emptyWord, loop, getDummyTF(), loopTF);
		boolean witStem = synthesize(stem, loop, stemTF, loopTF);
		if (witStem && !withoutStem) {
			s_Logger.info("Statistics: SI IS NECESSARY !!!");
		}

		return false;
	}
	
	
	private boolean synthesize(NestedWord<CodeBlock> stem, NestedWord<CodeBlock> loop, TransFormula stemTF, TransFormula loopTF) {
		RankingFunctionsSynthesizer synthesizer = null;
		try {
			synthesizer = new RankingFunctionsSynthesizer(
					smtManager.getScript(), new_Script(false), stemTF,
					loopTF);
		} catch (Exception e1) {
			e1.printStackTrace();
			throw new AssertionError(e1);
		}
		boolean found = false;
		try {
			found = synthesizer.synthesize(LinearTemplate.class);
			if (found) {
				RankingFunction rf = synthesizer.getRankingFunction();
				assert (rf != null);
				Collection<SupportingInvariant> si_list = synthesizer
						.getSupportingInvariants();
				assert (si_list != null);

				StringBuilder longMessage = new StringBuilder();
				LinearRankingFunction linRf = (LinearRankingFunction) rf;
				Expression rfExp = linRf.asExpression(smtManager.getScript(),
						smtManager.getBoogieVar2SmtVar());
				String rfString = RankingFunctionsObserver
						.backtranslateExprWorkaround(rfExp);
				String siString;

				// if (si_list.size() <= 2) {
				// SupportingInvariant si = si_list.iterator().next();
				// Expression siExp = si.asExpression(smtManager.getScript(),
				// rootAnnot.getBoogie2Smt());
				// siString =
				// RankingFunctionsObserver.backtranslateExprWorkaround(siExp);
				// } else {
				// throw new
				// AssertionError("The linear template should not have more than two supporting invariants.");
				// }
				longMessage.append("Statistics: Found linear ranking function ");
				longMessage.append(rfString);
				longMessage.append(" with linear supporting invariant");
				for (SupportingInvariant si : si_list) {
					Expression siExp = si.asExpression(smtManager.getScript(),
							smtManager.getBoogieVar2SmtVar());
					siString = RankingFunctionsObserver
							.backtranslateExprWorkaround(siExp);
					longMessage.append(" " + siString);
				}
				longMessage.append("  length stem: " + stem.length()
						+ " length loop: " + loop.length());
				s_Logger.info(longMessage);

				for (SupportingInvariant si : si_list) {
					if (stem.length() > 0) {
						assert checkResult(si, stem, loop) : "Wrong supporting invariant "
							+ si;
					}
				}
				boolean correctWithoutSi = checkResult(linRf, loop);
				if (correctWithoutSi) {
					s_Logger.info("Statistics: For this ranking function no si needed");
				} else {
					s_Logger.info("Statistics: We need si for this ranking function");
				}
				assert checkResult(linRf, si_list, loop) : "Wrong ranking function "
						+ rf;

			} else {
				s_Logger.info("Statistics: No ranking function has been found "
						+ "with this template.");
			}
		} catch (SMTLIBException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (TermIsNotAffineException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InstantiationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (AssertionError e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return found;
	}
	
	
	
	private	TransFormula getDummyTF() {
		Term term = smtManager.getScript().term("true");
		Map<BoogieVar,TermVariable> inVars = new HashMap<BoogieVar,TermVariable>();
		Map<BoogieVar,TermVariable> outVars = new HashMap<BoogieVar,TermVariable>();
		Set<TermVariable> auxVars = new HashSet<TermVariable>();
		Set<TermVariable> branchEncoders = new HashSet<TermVariable>();
		Infeasibility infeasibility = Infeasibility.UNPROVEABLE;
		Term closedFormula = term;
		return new TransFormula(term, inVars, outVars, auxVars, branchEncoders, 
				infeasibility, closedFormula);
	}
			
			
	
	
	private boolean checkResult(SupportingInvariant si, NestedWord<CodeBlock> stem, NestedWord<CodeBlock> loop) {
		boolean result = true;
		IPredicate siPred = m_Binarizer.supportingInvariant2Predicate(si);
		LBool stemCheck = m_TraceChecker.checkTrace(m_TruePredicate, siPred, stem);
		m_TraceChecker.forgetTrace();
		if (stemCheck != LBool.UNSAT) {
			result = false;
		}
		LBool loopCheck = m_TraceChecker.checkTrace(siPred, siPred, stem);
		m_TraceChecker.forgetTrace();
		if (loopCheck != LBool.UNSAT) {
			result = false;
		}
		return result;
	}
	
	private boolean checkResult(RankingFunction rf, NestedWord<CodeBlock> loop) {
		boolean result = true;
		IPredicate seedEquality = m_Binarizer.getSeedVarEquality(rf);
		IPredicate rkDecrease = m_Binarizer.getRankDecrease(rf);
		
		LBool stemCheck = m_TraceChecker.checkTrace(seedEquality, rkDecrease, loop);
		m_TraceChecker.forgetTrace();
		if (stemCheck != LBool.UNSAT) {
			result = false;
		}
		return result;
	}

	
	private boolean checkResult(RankingFunction rf,  Iterable<SupportingInvariant> siList, NestedWord<CodeBlock> loop) {
		boolean result = true;
		List<IPredicate> siPreds = new ArrayList<IPredicate>();
		for (SupportingInvariant si : siList) {
			IPredicate siPred = m_Binarizer.supportingInvariant2Predicate(si);
			siPreds.add(siPred);
		}
		TermVarsProc tvp = smtManager.and(siPreds.toArray(new IPredicate[0]));
		IPredicate siConjunction = smtManager.newPredicate(tvp.getFormula(), 
				tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula()); 
		
		IPredicate seedEquality = m_Binarizer.getSeedVarEquality(rf);
		IPredicate rkDecrease = m_Binarizer.getRankDecrease(rf);
		
		final IPredicate siConjunctionAndSeedEquality;
		{
			tvp = smtManager.and(siConjunction, seedEquality);
			siConjunctionAndSeedEquality = smtManager.newPredicate(tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
		}
		
		LBool stemCheck = m_TraceChecker.checkTrace(siConjunctionAndSeedEquality, rkDecrease, loop);
		m_TraceChecker.forgetTrace();
		if (stemCheck != LBool.UNSAT) {
			result = false;
		}
		return result;
	}

	
	Script new_Script(boolean nonlinear) {
		// This code is essentially copied from 
		// de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder
		// since there is no obvious way to implement it as shared code.
		
		TAPreferences taPref = new TAPreferences();
		Logger solverLogger = Logger.getLogger("interpolLogger");
		Script script;
		
		if (taPref.solver() == Solver.SMTInterpol) {
			script = new SMTInterpol(solverLogger,false);
		} else if (taPref.solver() == Solver.Z3) {
			script = new Scriptor("z3 -smt2 -in", solverLogger);
		} else {
			throw new AssertionError();
		}
		
		if (taPref.dumpScript()) {
			String dumpFileName = taPref.dumpPath();
			String fileSep = System.getProperty("file.separator");
			dumpFileName += (dumpFileName.endsWith(fileSep) ? "" : fileSep);
			dumpFileName = dumpFileName + "rankingFunctions.smt2";
			// FIXME: add file name
			try {
				script = new LoggingScript(script, dumpFileName, true);
			} catch (FileNotFoundException e) {
				throw new AssertionError(e);
			}
		}
		
		script.setOption(":produce-unsat-cores", true);
		script.setOption(":produce-models", true);
		if (taPref.solver() == Solver.SMTInterpol) {
			script.setLogic(nonlinear ? "QF_NRA" : "QF_LRA");
		} else if (taPref.solver() == Solver.Z3) {
			script.setLogic(nonlinear ? "QF_NRA" : "QF_LRA");
		} else {
			throw new AssertionError();
		}
		return script;
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
