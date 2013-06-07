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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization.AutomatonTransition.Transition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
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
		

		BuchiIsEmpty<CodeBlock, IPredicate> ec = null;

		NestedLassoRun<CodeBlock, IPredicate> ctx = null;
		NestedWord<CodeBlock> stem = ctx.getStem().getWord();
		s_Logger.info("Stem: " + stem);
		NestedWord<CodeBlock> loop = ctx.getLoop().getWord();
		s_Logger.info("Loop: " + loop);
		m_Iteration = 0;
		LBool feasibility = null;
		while (feasibility == LBool.UNSAT) {

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
//			feasibility = checkFeasibility(ctx, rootAnnot);
		}
		m_TraceChecker.forgetTrace();


		


		return false;
	}
	
	

	
	
	

			
			

	

	
	
	private NestedWordAutomaton<CodeBlock, IPredicate> constructBuchiInterpolantAutomaton(
			IPredicate precondition, NestedWord<CodeBlock> stem, IPredicate[] stemInterpolants, 
			IPredicate honda, NestedWord<CodeBlock> loop, IPredicate[] loopInterpolants,
			INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction) {
		NestedWordAutomaton<CodeBlock, IPredicate> result =	
				new NestedWordAutomaton<CodeBlock, IPredicate>(abstraction.getInternalAlphabet(), 
						abstraction.getCallAlphabet(), abstraction.getReturnAlphabet(), 
						abstraction.getStateFactory());
		result.addState(true, false, precondition);
		for (int i=0; i<=stemInterpolants.length-1; i++) {
			addState(stemInterpolants[i], result);
			addTransition(i, precondition, stemInterpolants, honda, stem, result);
		}
		result.addState(false, true, honda);
		for (int i=0; i<=stemInterpolants.length-1; i++) {
			addState(loopInterpolants[i], result);
			addTransition(i, honda, loopInterpolants, honda, loop, result);
		}
		return result;
	}
	
	private void addState(IPredicate pred, NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		if (!nwa.getStates().contains(pred)) {
			nwa.addState(false,false,pred);
		}
	}
	
	private void addTransition(int pos, IPredicate pre, IPredicate[] predicates, IPredicate post, NestedWord<CodeBlock> nw, NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		IPredicate pred = getPredicateAtPosition(pos-1, pre, predicates, post);
		IPredicate succ = getPredicateAtPosition(pos, pre, predicates, post);
		CodeBlock cb = nw.getSymbol(pos);
		if (nw.isInternalPosition(pos)) {
			nwa.addInternalTransition(pred, cb, succ);
		} else if (nw.isCallPosition(pos)) {
			nwa.addCallTransition(pred, cb, succ);
		} else if (nw.isReturnPosition(pos)) {
			assert !nw.isPendingReturn(pos);
			int k = nw.getCallPosition(pos);
			IPredicate hier = getPredicateAtPosition(k, pre, predicates, post);
			nwa.addReturnTransition(pred, hier, cb, succ);
		}
	}
	
	private IPredicate getPredicateAtPosition(int pos, IPredicate before, IPredicate[] predicates, IPredicate after) {
		assert pos >= -1;
		assert pos <= predicates.length;
		if (pos < 0) {
			return before;
		} else if (pos >= predicates.length) {
			return after;
		} else {
			return predicates[pos];
		}
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
