package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiClosureNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKVNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer.BInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.EagerInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;

public class RefineBuchi {
	
	protected final static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	 * Intermediate layer to encapsulate communication with SMT solvers. 
	 */
	private final SmtManager m_SmtManager;
	
	private final boolean m_DumpAutomata;
	private final boolean m_Difference;
	private final PredicateFactory m_StateFactoryInterpolAutom;
	private final PredicateFactoryRefinement m_StateFactoryForRefinement;
	private final boolean m_UseDoubleDeckers;
	private final String m_DumpPath;
	private final INTERPOLATION m_Interpolation;
	private BackwardCoveringInformation m_Bci;
	/**
	 * Interpolant automaton of this iteration.
	 */
	protected INestedWordAutomatonSimple<CodeBlock, IPredicate> m_InterpolAutomatonUsedInRefinement;
	

	

	public RefineBuchi(SmtManager smtManager, 
			boolean dumpAutomata, boolean difference,
			PredicateFactory stateFactoryInterpolAutom,
			PredicateFactoryRefinement stateFactoryForRefinement,
			boolean useDoubleDeckers, String dumpPath,
			INTERPOLATION interpolation) {
		super();
		m_SmtManager = smtManager;
		m_DumpAutomata = dumpAutomata;
		m_Difference = difference;
		m_StateFactoryInterpolAutom = stateFactoryInterpolAutom;
		m_StateFactoryForRefinement = stateFactoryForRefinement;
		m_UseDoubleDeckers = useDoubleDeckers;
		m_DumpPath = dumpPath;
		m_Interpolation = interpolation;
	}

	class RefinementSetting {
		private final BInterpolantAutomaton m_InterpolantAutomaton;
		private final boolean m_BouncerStem;
		private final boolean m_BouncerLoop;
		private final boolean m_ScroogeNondeterminismStem;
		private final boolean m_ScroogeNondeterminismLoop;
		private final boolean m_CannibalizeLoop;
		public RefinementSetting(BInterpolantAutomaton interpolantAutomaton,
				boolean bouncerStem, boolean bouncerLoop,
				boolean scroogeNondeterminismStem,
				boolean scroogeNondeterminismLoop,
				boolean cannibalizeLoop) {
			super();
			m_InterpolantAutomaton = interpolantAutomaton;
			m_BouncerStem = bouncerStem;
			m_BouncerLoop = bouncerLoop;
			m_ScroogeNondeterminismStem = scroogeNondeterminismStem;
			m_ScroogeNondeterminismLoop = scroogeNondeterminismLoop;
			m_CannibalizeLoop = cannibalizeLoop;
		}
		public BInterpolantAutomaton getInterpolantAutomaton() {
			return m_InterpolantAutomaton;
		}
		public boolean isBouncerStem() {
			return m_BouncerStem;
		}
		public boolean isBouncerLoop() {
			return m_BouncerLoop;
		}
		public boolean isScroogeNondeterminismStem() {
			return m_ScroogeNondeterminismStem;
		}
		public boolean isScroogeNondeterminismLoop() {
			return m_ScroogeNondeterminismLoop;
		}
		public boolean cannibalizeLoop() {
			return m_CannibalizeLoop;
		}
		@Override
		public String toString() {
			return "RefinementSetting [m_InterpolantAutomaton="
					+ m_InterpolantAutomaton + ", m_BouncerStem="
					+ m_BouncerStem + ", m_BouncerLoop=" + m_BouncerLoop
					+ ", m_ScroogeNondeterminismStem="
					+ m_ScroogeNondeterminismStem
					+ ", m_ScroogeNondeterminismLoop="
					+ m_ScroogeNondeterminismLoop + ", m_CannibalizeLoop="
					+ m_CannibalizeLoop + "]";
		}
	}
	
	
	
	
	public INestedWordAutomatonSimple<CodeBlock, IPredicate> getInterpolAutomatonUsedInRefinement() {
		return m_InterpolAutomatonUsedInRefinement;
	}
	

	public BackwardCoveringInformation getBci() {
		return m_Bci;
	}

	INestedWordAutomatonOldApi<CodeBlock, IPredicate> refineBuchi(
			INestedWordAutomaton<CodeBlock, IPredicate> m_Abstraction, 
			NestedLassoRun<CodeBlock, IPredicate> m_Counterexample, 
			int m_Iteration,
			RefinementSetting setting,
			BinaryStatePredicateManager bspm,
			BuchiModGlobalVarManager buchiModGlobalVarManager, 
			INTERPOLATION interpolation, 
			BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) throws AutomataLibraryException {
		NestedWord<CodeBlock> stem = m_Counterexample.getStem().getWord();
//		if (emptyStem(m_Counterexample)) {
//			stem = m_Counterexample.getLoop().getWord();
//		} else {
//			stem = m_Counterexample.getStem().getWord();
//		}
		NestedWord<CodeBlock> loop = m_Counterexample.getLoop().getWord();
		
		IPredicate falsePredicate = m_SmtManager.newFalsePredicate();
		assert !bspm.getStemPrecondition().getFormula().toString().equals("false");
		assert !bspm.getHondaPredicate().getFormula().toString().equals("false");
		assert !bspm.getRankEqAndSi().getFormula().toString().equals("false");
		PredicateUnifier pu = new PredicateUnifier(m_SmtManager, 
				bspm.getStemPrecondition(), bspm.getHondaPredicate(), bspm.getRankEqAndSi(), bspm.getStemPostcondition(), falsePredicate);
		IPredicate[] stemInterpolants;
		TraceChecker traceChecker;
		if (BuchiCegarLoop.emptyStem(m_Counterexample)) {
			stemInterpolants = null;
		} else {
			
			traceChecker = constructTraceChecker(bspm.getStemPrecondition(), 
					bspm.getStemPostcondition(), null, stem, m_SmtManager,
					buchiModGlobalVarManager);
			LBool stemCheck = traceChecker.isCorrect();
			if (stemCheck == LBool.UNSAT) {
				traceChecker.computeInterpolants(new TraceChecker.AllIntegers(), pu, m_Interpolation);
				stemInterpolants = traceChecker.getInterpolants();
			} else {
				throw new AssertionError("wrong predicates");
			}
		}

		traceChecker = constructTraceChecker(bspm.getRankEqAndSi(), 
				bspm.getHondaPredicate(), null, loop, m_SmtManager,
				buchiModGlobalVarManager);
		LBool loopCheck = traceChecker.isCorrect();
		IPredicate[] loopInterpolants;
		if (loopCheck == LBool.UNSAT) {
			traceChecker.computeInterpolants(new TraceChecker.AllIntegers(), pu, m_Interpolation);
			loopInterpolants = traceChecker.getInterpolants();
		} else {
			throw new AssertionError();
		}
		m_Bci = TraceCheckerUtils.computeCoverageCapability(traceChecker);
		
		NestedWordAutomaton<CodeBlock, IPredicate> m_InterpolAutomaton = constructBuchiInterpolantAutomaton(
				bspm.getStemPrecondition(), stem, stemInterpolants, bspm.getHondaPredicate(), 
				loop, loopInterpolants, m_Abstraction);
		if (m_DumpAutomata) {
			String filename = "InterpolantAutomatonBuchi"+m_Iteration;
			BuchiCegarLoop.writeAutomatonToFile(m_InterpolAutomaton, m_DumpPath, filename);
		}
		BuchiEdgeChecker ec = new BuchiEdgeChecker(m_SmtManager, buchiModGlobalVarManager);
		ec.putDecreaseEqualPair(bspm.getHondaPredicate(), bspm.getRankEqAndSi());
		assert (new InductivityCheck(m_InterpolAutomaton, ec, false, true)).getResult();
		assert (new BuchiAccepts<CodeBlock, IPredicate>(m_InterpolAutomaton,m_Counterexample.getNestedLassoWord())).getResult();
		switch (setting.getInterpolantAutomaton()) {
		case LassoAutomaton:
			m_InterpolAutomatonUsedInRefinement = m_InterpolAutomaton;
			break;
		case EagerNondeterminism:

			m_InterpolAutomatonUsedInRefinement = 
				new EagerInterpolantAutomaton(ec, m_InterpolAutomaton);
			break;
		case ScroogeNondeterminism:
		case Deterministic:
			Set<IPredicate> stemInterpolantsForRefinement;
			if (BuchiCegarLoop.emptyStem(m_Counterexample)) {
				stemInterpolantsForRefinement = Collections.emptySet();
			} else {
				if (setting.cannibalizeLoop()) {
					stemInterpolantsForRefinement = pu.cannibalizeAll(stemInterpolants);
				} else {
					stemInterpolantsForRefinement = new HashSet<IPredicate>(Arrays.asList(stemInterpolants));
				}
			}
			Set<IPredicate> loopInterpolantsForRefinement;
			if (setting.cannibalizeLoop()) {
			loopInterpolantsForRefinement = pu.cannibalizeAll(loopInterpolants);
			loopInterpolantsForRefinement.addAll(pu.cannibalize(bspm.getRankEqAndSi().getFormula()));
			
				LoopCannibalizer lc = new LoopCannibalizer(m_Counterexample, 
						loopInterpolantsForRefinement, bspm, pu, m_SmtManager, 
						buchiModGlobalVarManager, interpolation);
				loopInterpolantsForRefinement = lc.getResult();
			} else {
				loopInterpolantsForRefinement = new HashSet<IPredicate>(Arrays.asList(loopInterpolants));
				loopInterpolantsForRefinement.add(bspm.getRankEqAndSi());
			}

			m_InterpolAutomatonUsedInRefinement = new BuchiInterpolantAutomatonBouncer(
					m_SmtManager, bspm, ec, BuchiCegarLoop.emptyStem(m_Counterexample),
					stemInterpolantsForRefinement, 
					loopInterpolantsForRefinement, 
					BuchiCegarLoop.emptyStem(m_Counterexample) ? null : stem.getSymbol(stem.length()-1), 
					loop.getSymbol(loop.length()-1), m_Abstraction, 
					setting.isScroogeNondeterminismStem(), setting.isScroogeNondeterminismLoop(), 
					setting.isBouncerStem(), setting.isBouncerLoop(), m_StateFactoryInterpolAutom, pu, pu, falsePredicate);
			break;
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
		IStateDeterminizer<CodeBlock, IPredicate> stateDeterminizer = 
				new PowersetDeterminizer<CodeBlock, IPredicate>(m_InterpolAutomatonUsedInRefinement, m_UseDoubleDeckers, m_StateFactoryInterpolAutom);
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction;
		if (m_Difference) {
			BuchiDifferenceFKV<CodeBlock, IPredicate> diff = 
					new BuchiDifferenceFKV<CodeBlock, IPredicate>(
							m_Abstraction, m_InterpolAutomatonUsedInRefinement, 
							stateDeterminizer, m_StateFactoryForRefinement);
			finishComputation(m_InterpolAutomatonUsedInRefinement,setting);
			
			assert diff.checkResult(m_StateFactoryInterpolAutom);
			
//			s_Logger.warn("START: minimization test");
//			BuchiComplementFKVNwa<CodeBlock, IPredicate> compl1 = diff.getSndComplemented();
//			INestedWordAutomatonOldApi<CodeBlock, IPredicate> compl = (new RemoveNonLiveStates<CodeBlock, IPredicate>(compl1)).getResult();
//			BuchiClosureNwa<CodeBlock, IPredicate> bc = (new BuchiClosureNwa<CodeBlock, IPredicate>(compl));
//			MinimizeSevpa<CodeBlock, IPredicate> minimizeOp = 
//					new MinimizeSevpa<CodeBlock, IPredicate>(bc,null,false,false,m_StateFactoryInterpolAutom);
//			s_Logger.warn("END: minimization test");
//			INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimizedOp = minimizeOp.getResult();
//			
//			BuchiIntersect<CodeBlock, IPredicate> newDiff = 
//					new BuchiIntersect<CodeBlock, IPredicate>(
//							m_Abstraction, minimizedOp, m_StateFactoryForRefinement);
//			s_Logger.warn("oldDiff size" + diff.getResult().sizeInformation());
//			s_Logger.warn("newDiff size" + (newDiff.getResult()).sizeInformation());
			
			
			newAbstraction = diff.getResult();
		} else {
			BuchiComplementFKV<CodeBlock, IPredicate> complNwa = 
					new BuchiComplementFKV<CodeBlock, IPredicate>(m_InterpolAutomatonUsedInRefinement, stateDeterminizer);
			finishComputation(m_InterpolAutomatonUsedInRefinement,setting);
			assert(complNwa.checkResult(m_StateFactoryInterpolAutom));
			INestedWordAutomatonOldApi<CodeBlock, IPredicate>  complement = 
					complNwa.getResult();
			assert !(new BuchiAccepts<CodeBlock, IPredicate>(complement,m_Counterexample.getNestedLassoWord())).getResult();
			BuchiIntersect<CodeBlock, IPredicate> interNwa = 
					new BuchiIntersect<CodeBlock, IPredicate>(m_Abstraction, complement,m_StateFactoryForRefinement);
			assert(interNwa.checkResult(m_StateFactoryInterpolAutom));
			newAbstraction = interNwa.getResult();
		}
//		INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldApi = (new RemoveUnreachable<CodeBlock, IPredicate>(m_InterpolAutomatonUsedInRefinement)).getResult();
		benchmarkGenerator.addEdgeCheckerData(ec.getEdgeCheckerBenchmark());
		m_InterpolAutomaton = null;
		boolean isUseful = isUsefulInterpolantAutomaton(m_InterpolAutomatonUsedInRefinement, m_Counterexample);
		if (!isUseful) {
			return null;
		}
		
		//assert (new BuchiAccepts<CodeBlock, IPredicate>(oldApi,m_Counterexample.getNestedLassoWord())).getResult() : "interpolant automaton does not accept lasso.";
		//assert !(new BuchiAccepts<CodeBlock, IPredicate>(newAbstraction,m_Counterexample.getNestedLassoWord())).getResult()  : "no progress";
		if (m_DumpAutomata) {
			String filename = "interpolBuchiAutomatonUsedInRefinement"+m_Iteration+"after";
			BuchiCegarLoop.writeAutomatonToFile(m_InterpolAutomatonUsedInRefinement, m_DumpPath, filename);
		}
		return newAbstraction;
	}
	
	private TraceChecker constructTraceChecker(IPredicate precond,
			IPredicate postcond, Object object,
			NestedWord<CodeBlock> word, SmtManager smtManager,
			BuchiModGlobalVarManager buchiModGlobalVarManager) {
		switch (m_Interpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			return new TraceChecker(precond, postcond, 
					new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(word),m_SmtManager,
					buchiModGlobalVarManager, /* TODO: When Matthias introduced this parameter he set the argument to false. Check if you want to set this to true.  */ false);
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
			return new TraceCheckerSpWp(precond, postcond, 
					null, NestedWord.nestedWord(word),m_SmtManager,
					buchiModGlobalVarManager, /* TODO: When Matthias introduced this parameter he set the argument to false. Check if you want to set this to true.  */ false);
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
	}

	private boolean isUsefulInterpolantAutomaton(
			INestedWordAutomatonSimple<CodeBlock, IPredicate> interpolAutomatonUsedInRefinement,
			NestedLassoRun<CodeBlock, IPredicate> counterexample) throws OperationCanceledException {
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldApi;
		oldApi = (new RemoveUnreachable<CodeBlock, IPredicate>(interpolAutomatonUsedInRefinement)).getResult();
		NestedWord<CodeBlock> stem = counterexample.getStem().getWord();
		NestedWord<CodeBlock> loop = counterexample.getLoop().getWord();
		NestedWord<CodeBlock> stemAndLoop = stem.concatenate(loop);
		NestedLassoWord<CodeBlock> stemExtension = new NestedLassoWord<CodeBlock>(stemAndLoop, loop);
		NestedWord<CodeBlock> loopAndLoop = loop.concatenate(loop);
		NestedLassoWord<CodeBlock> loopExtension = new NestedLassoWord<CodeBlock>(stem, loopAndLoop);
		boolean wordAccepted = (new BuchiAccepts<CodeBlock, IPredicate>(oldApi, counterexample.getNestedLassoWord())).getResult();
		if (!wordAccepted) {
			s_Logger.info("Bad chosen interpolant automaton: word not accepted");
			return false;
		}
		boolean stemExtensionAccepted = (new BuchiAccepts<CodeBlock, IPredicate>(oldApi, stemExtension)).getResult();
		if (!stemExtensionAccepted) {
			s_Logger.info("Bad chosen interpolant automaton: stem extension not accepted");
			return false;
		}
		boolean loopExtensionAccepted = (new BuchiAccepts<CodeBlock, IPredicate>(oldApi, loopExtension)).getResult();
		if (!loopExtensionAccepted) {
			s_Logger.info("Bad chosen interpolant automaton: loop extension not accepted");
			return false;
		}
		return true;
	}
	
	private void finishComputation(INestedWordAutomatonSimple<CodeBlock, IPredicate> interpolantAutomaton, RefinementSetting setting) {
		switch (setting.getInterpolantAutomaton()) {
		case LassoAutomaton:
			// do nothing
			break;
		case EagerNondeterminism:
			((EagerInterpolantAutomaton) interpolantAutomaton).finishConstruction();
			break;
		case ScroogeNondeterminism:
		case Deterministic:
			((BuchiInterpolantAutomatonBouncer) interpolantAutomaton).finishConstruction();
			break;
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
	}
	

	private NestedWordAutomaton<CodeBlock, IPredicate> constructBuchiInterpolantAutomaton(
			IPredicate precondition, NestedWord<CodeBlock> stem, IPredicate[] stemInterpolants, 
			IPredicate honda, NestedWord<CodeBlock> loop, IPredicate[] loopInterpolants,
			INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction) {
		NestedWordAutomaton<CodeBlock, IPredicate> result =	
				new NestedWordAutomaton<CodeBlock, IPredicate>(abstraction.getInternalAlphabet(), 
						abstraction.getCallAlphabet(), abstraction.getReturnAlphabet(), 
						abstraction.getStateFactory());
		boolean emptyStem = stem.length() == 0;
		if (emptyStem) {
			result.addState(true, true, honda);
		} else {
			result.addState(true, false, precondition);
			for (int i=0; i<stemInterpolants.length; i++) {
				addState(stemInterpolants[i], result);
				addTransition(i, precondition, stemInterpolants, honda, stem, result);
			}
			result.addState(false, true, honda);
			addTransition(stemInterpolants.length, precondition, stemInterpolants, honda, stem, result);
		}
		for (int i=0; i<loopInterpolants.length; i++) {
			addState(loopInterpolants[i], result);
			addTransition(i, honda, loopInterpolants, honda, loop, result);
		}
		addTransition(loopInterpolants.length, honda, loopInterpolants, honda, loop, result);
		return result;
	}
	
	private void addState(IPredicate pred, NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		if (!nwa.getStates().contains(pred)) {
			nwa.addState(false,false,pred);
		}
	}
	
	private void addTransition(int pos, IPredicate pre, IPredicate[] predicates, 
			IPredicate post, NestedWord<CodeBlock> nw, NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
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
			IPredicate hier = getPredicateAtPosition(k-1, pre, predicates, post);
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
	
	
}
