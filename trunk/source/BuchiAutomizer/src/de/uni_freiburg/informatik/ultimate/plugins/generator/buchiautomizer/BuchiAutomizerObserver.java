package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Difference;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.StrongestPostDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.AllIntegers;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class BuchiAutomizerObserver implements IUnmanagedObserver {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
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
			e2.printStackTrace();
			throw new AssertionError();
		}
		NestedLassoRun<CodeBlock, IPredicate> ctx = ec.getAcceptingNestedLassoRun();
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
			Difference<CodeBlock, IPredicate> diff = null;
			try {
				diff = new Difference<CodeBlock, IPredicate>(
						m_Abstraction, m_InterpolAutomaton, spd, 
						m_StateFactoryForRefinement,
						false, true);
			} catch (OperationCanceledException e) {
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
				e.printStackTrace();
				throw new AssertionError();
			}
			ctx = ec.getAcceptingNestedLassoRun();
			stem = ctx.getStem().getWord();
			s_Logger.info("Stem: " + stem);
			loop = ctx.getLoop().getWord();
			s_Logger.info("Loop: " + loop);
			m_Iteration++;
			feasibility = checkFeasibility(ctx, rootAnnot);
		}


		
		TransFormula[] stemTFs = new TransFormula[stem.length()];
		for (int i=0; i<stem.length(); i++) {
			stemTFs[i] = stem.getSymbol(i).getTransitionFormula();
		}
		TransFormula[] loopTFs = new TransFormula[loop.length()];
		for (int i=0; i<loop.length(); i++) {
			loopTFs[i] = loop.getSymbol(i).getTransitionFormula();
		}
		TransFormula stemTF = TransFormula.sequentialComposition(1000, rootAnnot.getBoogie2SMT(), stemTFs);
		TransFormula loopTF = TransFormula.sequentialComposition(1000+stemTFs.length, rootAnnot.getBoogie2SMT(), loopTFs);
		RankingFunctionsSynthesizer synthesizer = null;
		try {
			synthesizer = new RankingFunctionsSynthesizer(smtManager.getScript(), smtManager.getScript(), stemTF, loopTF);
		} catch (Exception e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

			try {
				if (synthesizer.synthesize(LinearTemplate.class)) {
					RankingFunction rf = synthesizer.getRankingFunction();
					assert(rf != null);
					Collection<SupportingInvariant> si_list =
							synthesizer.getSupportingInvariants();
					assert(si_list != null);

					StringBuilder longMessage = new StringBuilder();
					LinearRankingFunction linRf = (LinearRankingFunction) rf;
					Expression rfExp = linRf.asExpression(smtManager.getScript(), rootAnnot.getBoogie2Smt());
					String rfString = RankingFunctionsObserver.backtranslateExprWorkaround(rfExp);
					String siString;
					if (si_list.size() <= 2) {
						SupportingInvariant si = si_list.iterator().next();
						Expression siExp = si.asExpression(smtManager.getScript(), rootAnnot.getBoogie2Smt());
						siString = RankingFunctionsObserver.backtranslateExprWorkaround(siExp);
					} else {
						throw new AssertionError("The linear template should not have more than two supporting invariants.");
					}
					longMessage.append("Found linear ranking function ");
					longMessage.append(rfString);
					longMessage.append(" with linear supporting invariant ");
					longMessage.append(siString);
					s_Logger.info(longMessage);
				} else {
					s_Logger.info("No ranking function has been found " +
							"with this template.");
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
		
//		m_OverallIterations = 0;
//		OverallBiggestAbstraction = 0;
//		m_OverallResult = Result.SAFE;
//		m_Artifact = null;
		return false;
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
	
//	public static TransFormula sequentialComposition(int serialNumber, 
//			Boogie2SMT boogie2smt, TransFormula... transFormulas) {
//		TransFormula result = transFormulas[0];
//		for (int i=1; i<transFormulas.length; i++) {
//			result = TransFormula.sequentialComposition(result, transFormulas[i],  boogie2smt, serialNumber++);
//		}
//		return result;
//	}

}
