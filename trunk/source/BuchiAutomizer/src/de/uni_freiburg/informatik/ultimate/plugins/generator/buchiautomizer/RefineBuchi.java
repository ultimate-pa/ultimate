package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer.BInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.EagerInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.PreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

public class RefineBuchi {
	
	protected final static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	 * Intermediate layer to encapsulate communication with SMT solvers. 
	 */
	private final SmtManager m_SmtManager;
	
	private final BinaryStatePredicateManager m_Bspm;
	private final BuchiModGlobalVarManager m_BuchiModGlobalVarManager;
	private final boolean m_DumpAutomata;
	private final boolean m_Difference;
	private final PredicateFactory m_StateFactory;
	private final  PredicateFactoryRefinement m_StateFactoryForRefinement;
	private final boolean m_UseDoubleDeckers;
	private final String m_DumpPath;
	/**
	 * Interpolant automaton of this iteration.
	 */
	protected INestedWordAutomatonSimple<CodeBlock, IPredicate> m_InterpolAutomatonUsedInRefinement;
	

	

	public RefineBuchi(SmtManager smtManager, BinaryStatePredicateManager bspm,
			BuchiModGlobalVarManager buchiModGlobalVarManager,
			boolean dumpAutomata, boolean difference,
			PredicateFactory stateFactory,
			PredicateFactoryRefinement stateFactoryForRefinement,
			boolean useDoubleDeckers, String dumpPath) {
		super();
		m_SmtManager = smtManager;
		m_Bspm = bspm;
		m_BuchiModGlobalVarManager = buchiModGlobalVarManager;
		m_DumpAutomata = dumpAutomata;
		m_Difference = difference;
		m_StateFactory = stateFactory;
		m_StateFactoryForRefinement = stateFactoryForRefinement;
		m_UseDoubleDeckers = useDoubleDeckers;
		m_DumpPath = dumpPath;
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

	INestedWordAutomatonOldApi<CodeBlock, IPredicate> refineBuchi(INestedWordAutomaton<CodeBlock, IPredicate> m_Abstraction, 
			NestedLassoRun<CodeBlock, IPredicate> m_Counterexample, 
			int m_Iteration,
			RefinementSetting setting) throws AutomataLibraryException {
		NestedWord<CodeBlock> stem = m_Counterexample.getStem().getWord();
//		if (emptyStem(m_Counterexample)) {
//			stem = m_Counterexample.getLoop().getWord();
//		} else {
//			stem = m_Counterexample.getStem().getWord();
//		}
		NestedWord<CodeBlock> loop = m_Counterexample.getLoop().getWord();
		
		PredicateUnifier pu = new PredicateUnifier(m_SmtManager, 
				m_Bspm.getStemPrecondition(), m_Bspm.getHondaPredicate(), m_Bspm.getRankEqAndSi(), m_Bspm.getStemPostcondition());
		IPredicate[] stemInterpolants;
		TraceChecker m_TraceChecker;
		if (BuchiCegarLoop.emptyStem(m_Counterexample)) {
			stemInterpolants = null;
		} else {
			m_TraceChecker = new TraceChecker(m_Bspm.getStemPrecondition(), 
					m_Bspm.getStemPostcondition(), null, stem, m_SmtManager,
					m_BuchiModGlobalVarManager);
			LBool stemCheck = m_TraceChecker.isCorrect();
			if (stemCheck == LBool.UNSAT) {
				m_TraceChecker.computeInterpolants(new TraceChecker.AllIntegers(), pu, INTERPOLATION.Craig_TreeInterpolation);
				stemInterpolants = m_TraceChecker.getInterpolants();
			} else {
				throw new AssertionError("wrong predicates");
			}
		}

		m_TraceChecker = new TraceChecker(m_Bspm.getRankEqAndSi(), 
				m_Bspm.getHondaPredicate(), null, loop, m_SmtManager,
				m_BuchiModGlobalVarManager);
		LBool loopCheck = m_TraceChecker.isCorrect();
		IPredicate[] loopInterpolants;
		if (loopCheck == LBool.UNSAT) {
			m_TraceChecker.computeInterpolants(new TraceChecker.AllIntegers(), pu, INTERPOLATION.Craig_TreeInterpolation);
			loopInterpolants = m_TraceChecker.getInterpolants();
		} else {
			throw new AssertionError();
		}
		
		NestedWordAutomaton<CodeBlock, IPredicate> m_InterpolAutomaton = constructBuchiInterpolantAutomaton(
				m_Bspm.getStemPrecondition(), stem, stemInterpolants, m_Bspm.getHondaPredicate(), 
				loop, loopInterpolants, m_Abstraction);
		if (m_DumpAutomata) {
			String filename = "InterpolantAutomatonBuchi"+m_Iteration;
			BuchiCegarLoop.writeAutomatonToFile(m_InterpolAutomaton, m_DumpPath, filename);
		}
		EdgeChecker ec = new BuchiEdgeChecker(m_SmtManager, m_BuchiModGlobalVarManager,
				m_Bspm.getHondaPredicate(), m_Bspm.getRankEqAndSi(), 
				m_Bspm.getUnseededVariable(), m_Bspm.getOldRankVariable());
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
			loopInterpolantsForRefinement.addAll(pu.cannibalize(m_Bspm.getRankEqAndSi().getFormula()));
			
				LoopCannibalizer lc = new LoopCannibalizer(m_Counterexample, 
						loopInterpolantsForRefinement, m_Bspm, pu, m_SmtManager, m_BuchiModGlobalVarManager);
				loopInterpolantsForRefinement = lc.getResult();
			} else {
				loopInterpolantsForRefinement = new HashSet<IPredicate>(Arrays.asList(loopInterpolants));
				loopInterpolantsForRefinement.add(m_Bspm.getRankEqAndSi());
			}
			m_InterpolAutomatonUsedInRefinement = new BuchiInterpolantAutomaton(
					m_SmtManager, ec,  BuchiCegarLoop.emptyStem(m_Counterexample),
					m_Bspm.getStemPrecondition(), 
					stemInterpolantsForRefinement, m_Bspm.getHondaPredicate(), 
					loopInterpolantsForRefinement, 
					BuchiCegarLoop.emptyStem(m_Counterexample) ? null : stem.getSymbol(stem.length()-1), 
					loop.getSymbol(loop.length()-1), m_Abstraction, 
					setting.isScroogeNondeterminismStem(), setting.isScroogeNondeterminismLoop(), 
					setting.isBouncerStem(), setting.isBouncerLoop());
			break;
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
		IStateDeterminizer<CodeBlock, IPredicate> stateDeterminizer = 
				new PowersetDeterminizer<CodeBlock, IPredicate>(m_InterpolAutomatonUsedInRefinement, m_UseDoubleDeckers);
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction;
		if (m_Difference) {
			BuchiDifferenceFKV<CodeBlock, IPredicate> diff = 
					new BuchiDifferenceFKV<CodeBlock, IPredicate>(
							m_Abstraction, m_InterpolAutomatonUsedInRefinement, 
							stateDeterminizer, m_StateFactoryForRefinement);
			finishComputation(m_InterpolAutomatonUsedInRefinement,setting);
			assert diff.checkResult(m_StateFactory);
			newAbstraction = diff.getResult();
		} else {
			BuchiComplementFKV<CodeBlock, IPredicate> complNwa = 
					new BuchiComplementFKV<CodeBlock, IPredicate>(m_InterpolAutomatonUsedInRefinement, stateDeterminizer);
			finishComputation(m_InterpolAutomatonUsedInRefinement,setting);
			assert(complNwa.checkResult(m_StateFactory));
			INestedWordAutomatonOldApi<CodeBlock, IPredicate>  complement = 
					complNwa.getResult();
			assert !(new BuchiAccepts<CodeBlock, IPredicate>(complement,m_Counterexample.getNestedLassoWord())).getResult();
			BuchiIntersect<CodeBlock, IPredicate> interNwa = 
					new BuchiIntersect<CodeBlock, IPredicate>(m_Abstraction, complement,m_StateFactoryForRefinement);
			assert(interNwa.checkResult(m_StateFactory));
			newAbstraction = interNwa.getResult();
		}
//		INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldApi = (new RemoveUnreachable<CodeBlock, IPredicate>(m_InterpolAutomatonUsedInRefinement)).getResult();
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
	
	private boolean isUsefulInterpolantAutomaton(
			INestedWordAutomatonSimple<CodeBlock, IPredicate> interpolAutomatonUsedInRefinement,
			NestedLassoRun<CodeBlock, IPredicate> counterexample) {
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldApi;
		try {
			oldApi = (new RemoveUnreachable<CodeBlock, IPredicate>(interpolAutomatonUsedInRefinement)).getResult();
		} catch (OperationCanceledException e) {
			throw new AssertionError();
		}
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
			((BuchiInterpolantAutomaton) interpolantAutomaton).finishConstruction();
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
