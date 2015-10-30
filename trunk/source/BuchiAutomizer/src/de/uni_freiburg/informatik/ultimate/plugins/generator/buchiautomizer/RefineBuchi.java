/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiDifferenceNCSB;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.TightLevelRankingStateGeneratorBuilder;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.TightLevelRankingStateGeneratorBuilder.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsSemiDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer.BInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

public class RefineBuchi {

	protected final Logger mLogger;

	/**
	 * Intermediate layer to encapsulate communication with SMT solvers.
	 */
	private final SmtManager m_SmtManager;
	
	private final RootNode m_RootNode;

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

	private final IUltimateServiceProvider m_Services;

	public RefineBuchi(RootNode rootNode, SmtManager smtManager, boolean dumpAutomata, boolean difference,
			PredicateFactory stateFactoryInterpolAutom, PredicateFactoryRefinement stateFactoryForRefinement,
			boolean useDoubleDeckers, String dumpPath, INTERPOLATION interpolation, IUltimateServiceProvider services,
			Logger logger) {
		super();
		m_Services = services;
		mLogger = logger;
		m_RootNode = rootNode;
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
		private final int m_UsedDefinedMaxRank;

		public RefinementSetting(BInterpolantAutomaton interpolantAutomaton, boolean bouncerStem, boolean bouncerLoop,
				boolean scroogeNondeterminismStem, boolean scroogeNondeterminismLoop, boolean cannibalizeLoop, int userDefinedMaxRank) {
			super();
			m_InterpolantAutomaton = interpolantAutomaton;
			m_BouncerStem = bouncerStem;
			m_BouncerLoop = bouncerLoop;
			m_ScroogeNondeterminismStem = scroogeNondeterminismStem;
			m_ScroogeNondeterminismLoop = scroogeNondeterminismLoop;
			m_CannibalizeLoop = cannibalizeLoop;
			m_UsedDefinedMaxRank = userDefinedMaxRank;
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
		
		public int getUsedDefinedMaxRank() {
			return m_UsedDefinedMaxRank;
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
					+ m_CannibalizeLoop + ", m_UsedDefinedMaxRank="
					+ m_UsedDefinedMaxRank + "]";
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
			NestedLassoRun<CodeBlock, IPredicate> m_Counterexample, int m_Iteration, RefinementSetting setting,
			BinaryStatePredicateManager bspm, BuchiModGlobalVarManager buchiModGlobalVarManager,
			INTERPOLATION interpolation, BuchiCegarLoopBenchmarkGenerator benchmarkGenerator)
			throws AutomataLibraryException {
		NestedWord<CodeBlock> stem = m_Counterexample.getStem().getWord();
		// if (emptyStem(m_Counterexample)) {
		// stem = m_Counterexample.getLoop().getWord();
		// } else {
		// stem = m_Counterexample.getStem().getWord();
		// }
		NestedWord<CodeBlock> loop = m_Counterexample.getLoop().getWord();

		assert !bspm.getStemPrecondition().getFormula().toString().equals("false");
		assert !bspm.getHondaPredicate().getFormula().toString().equals("false");
		assert !bspm.getRankEqAndSi().getFormula().toString().equals("false");
		PredicateUnifier pu = new PredicateUnifier(m_Services, m_SmtManager, bspm.getStemPrecondition(),
				bspm.getHondaPredicate(), bspm.getRankEqAndSi(), bspm.getStemPostcondition());
		IPredicate[] stemInterpolants;
		InterpolatingTraceChecker traceChecker;
		if (BuchiCegarLoop.emptyStem(m_Counterexample)) {
			stemInterpolants = null;
		} else {

			traceChecker = constructTraceChecker(bspm.getStemPrecondition(), bspm.getStemPostcondition(), stem,
					m_SmtManager, buchiModGlobalVarManager, pu, m_Interpolation);
			LBool stemCheck = traceChecker.isCorrect();
			if (stemCheck == LBool.UNSAT) {
				stemInterpolants = traceChecker.getInterpolants();
			} else {
				throw new AssertionError("incorrect predicates - stem");
			}
		}

		traceChecker = constructTraceChecker(bspm.getRankEqAndSi(), bspm.getHondaPredicate(), loop, m_SmtManager,
				buchiModGlobalVarManager, pu, m_Interpolation);
		LBool loopCheck = traceChecker.isCorrect();
		IPredicate[] loopInterpolants;
		if (loopCheck == LBool.UNSAT) {
			loopInterpolants = traceChecker.getInterpolants();
		} else {
			throw new AssertionError("incorrect predicates - loop");
		}
		m_Bci = TraceCheckerUtils.computeCoverageCapability(m_Services, traceChecker, mLogger);

		NestedWordAutomaton<CodeBlock, IPredicate> m_InterpolAutomaton = constructBuchiInterpolantAutomaton(
				bspm.getStemPrecondition(), stem, stemInterpolants, bspm.getHondaPredicate(), loop, loopInterpolants,
				m_Abstraction);
		if (m_DumpAutomata) {
			
			String filename = m_RootNode.getFilename() + "_" + "InterpolantAutomatonBuchi" + m_Iteration;
			String message = setting.toString();
			BuchiCegarLoop.writeAutomatonToFile(m_Services, m_InterpolAutomaton, m_DumpPath, filename, message);
		}

//		BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(new MonolithicHoareTripleChecker(m_SmtManager));
		BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(new IncrementalHoareTripleChecker(m_SmtManager, buchiModGlobalVarManager));
		bhtc.putDecreaseEqualPair(bspm.getHondaPredicate(), bspm.getRankEqAndSi());
		assert (new InductivityCheck(m_Services, m_InterpolAutomaton, false, true, bhtc)).getResult();
		assert (new BuchiAccepts<CodeBlock, IPredicate>(m_Services, m_InterpolAutomaton, m_Counterexample.getNestedLassoWord()))
				.getResult();
		switch (setting.getInterpolantAutomaton()) {
		case LassoAutomaton:
			m_InterpolAutomatonUsedInRefinement = m_InterpolAutomaton;
			break;
		case EagerNondeterminism:
			if (!m_InterpolAutomaton.getStates().contains(pu.getTruePredicate())) {
				m_InterpolAutomaton.addState(false, false, pu.getTruePredicate());
			}
			if (!m_InterpolAutomaton.getStates().contains(pu.getFalsePredicate())) {
				m_InterpolAutomaton.addState(false, true, pu.getFalsePredicate());
			}
			m_InterpolAutomatonUsedInRefinement = new NondeterministicInterpolantAutomaton(m_Services, m_SmtManager, 
					buchiModGlobalVarManager, bhtc, m_Abstraction, m_InterpolAutomaton, pu, mLogger, false, true);
			break;
		case ScroogeNondeterminism:
		case Deterministic:
			Set<IPredicate> stemInterpolantsForRefinement;
			if (BuchiCegarLoop.emptyStem(m_Counterexample)) {
				stemInterpolantsForRefinement = Collections.emptySet();
			} else {
				if (setting.cannibalizeLoop()) {
					stemInterpolantsForRefinement = pu.cannibalizeAll(false, stemInterpolants);
				} else {
					stemInterpolantsForRefinement = new HashSet<IPredicate>(Arrays.asList(stemInterpolants));
				}
			}
			Set<IPredicate> loopInterpolantsForRefinement;
			if (setting.cannibalizeLoop()) {
				try {
					loopInterpolantsForRefinement = pu.cannibalizeAll(false, loopInterpolants);
					loopInterpolantsForRefinement.addAll(pu.cannibalize(false, bspm.getRankEqAndSi().getFormula()));

					LoopCannibalizer lc = new LoopCannibalizer(m_Counterexample, loopInterpolantsForRefinement, bspm, pu,
							m_SmtManager, buchiModGlobalVarManager, interpolation, m_Services);
					loopInterpolantsForRefinement = lc.getResult();
				} catch (ToolchainCanceledException tce) {
					String taskMessage = "loop cannibalization: ";
					if (tce.getRunningTaskInfo() != null) {
						taskMessage += tce.getRunningTaskInfo();
					}
					throw new ToolchainCanceledException(getClass(), taskMessage);
				}
			} else {
				loopInterpolantsForRefinement = new HashSet<IPredicate>(Arrays.asList(loopInterpolants));
				loopInterpolantsForRefinement.add(bspm.getRankEqAndSi());
			}

			m_InterpolAutomatonUsedInRefinement = new BuchiInterpolantAutomatonBouncer(m_SmtManager, bspm, bhtc,
					BuchiCegarLoop.emptyStem(m_Counterexample), stemInterpolantsForRefinement,
					loopInterpolantsForRefinement, BuchiCegarLoop.emptyStem(m_Counterexample) ? null
							: stem.getSymbol(stem.length() - 1), loop.getSymbol(loop.length() - 1), m_Abstraction,
					setting.isScroogeNondeterminismStem(), setting.isScroogeNondeterminismLoop(),
					setting.isBouncerStem(), setting.isBouncerLoop(), m_StateFactoryInterpolAutom, pu, pu,
					pu.getFalsePredicate(), m_Services);
			break;
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
		IStateDeterminizer<CodeBlock, IPredicate> stateDeterminizer = new PowersetDeterminizer<CodeBlock, IPredicate>(
				m_InterpolAutomatonUsedInRefinement, m_UseDoubleDeckers, m_StateFactoryInterpolAutom);
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction;
		if (m_Difference) {
			if (setting.getUsedDefinedMaxRank() == -3) {
				BuchiDifferenceNCSB<CodeBlock, IPredicate> diff = new BuchiDifferenceNCSB<CodeBlock, IPredicate>(m_Services, 
						m_StateFactoryForRefinement, m_Abstraction, m_InterpolAutomatonUsedInRefinement);
				finishComputation(m_InterpolAutomatonUsedInRefinement, setting);
				benchmarkGenerator.reportHighestRank(3);
				assert diff.checkResult(m_StateFactoryInterpolAutom);
				newAbstraction = diff.getResult();
			} else { 
				BuchiDifferenceFKV<CodeBlock, IPredicate> diff = new BuchiDifferenceFKV<CodeBlock, IPredicate>(m_Services, 
						m_Abstraction, m_InterpolAutomatonUsedInRefinement, stateDeterminizer, m_StateFactoryForRefinement,
						FkvOptimization.HeiMat2.toString(),
						setting.getUsedDefinedMaxRank());
				finishComputation(m_InterpolAutomatonUsedInRefinement, setting);
				benchmarkGenerator.reportHighestRank(diff.getHighestRank());
				assert diff.checkResult(m_StateFactoryInterpolAutom);
				newAbstraction = diff.getResult();
			}

			// s_Logger.warn("START: minimization test");
			// BuchiComplementFKVNwa<CodeBlock, IPredicate> compl1 =
			// diff.getSndComplemented();
			// INestedWordAutomatonOldApi<CodeBlock, IPredicate> compl = (new
			// RemoveNonLiveStates<CodeBlock, IPredicate>(compl1)).getResult();
			// BuchiClosureNwa<CodeBlock, IPredicate> bc = (new
			// BuchiClosureNwa<CodeBlock, IPredicate>(compl));
			// MinimizeSevpa<CodeBlock, IPredicate> minimizeOp =
			// new MinimizeSevpa<CodeBlock,
			// IPredicate>(bc,null,false,false,m_StateFactoryInterpolAutom);
			// s_Logger.warn("END: minimization test");
			// INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimizedOp =
			// minimizeOp.getResult();
			//
			// BuchiIntersect<CodeBlock, IPredicate> newDiff =
			// new BuchiIntersect<CodeBlock, IPredicate>(
			// m_Abstraction, minimizedOp, m_StateFactoryForRefinement);
			// s_Logger.warn("oldDiff size" +
			// diff.getResult().sizeInformation());
			// s_Logger.warn("newDiff size" +
			// (newDiff.getResult()).sizeInformation());

			
		} else {
			BuchiComplementFKV<CodeBlock, IPredicate> complNwa = new BuchiComplementFKV<CodeBlock, IPredicate>(
					m_Services, 
					m_InterpolAutomatonUsedInRefinement, stateDeterminizer);
			finishComputation(m_InterpolAutomatonUsedInRefinement, setting);
			benchmarkGenerator.reportHighestRank(complNwa.getHighestRank());
			assert (complNwa.checkResult(m_StateFactoryInterpolAutom));
			INestedWordAutomatonOldApi<CodeBlock, IPredicate> complement = complNwa.getResult();
			assert !(new BuchiAccepts<CodeBlock, IPredicate>(m_Services, complement, m_Counterexample.getNestedLassoWord()))
					.getResult();
			BuchiIntersect<CodeBlock, IPredicate> interNwa = new BuchiIntersect<CodeBlock, IPredicate>(m_Services, m_Abstraction,
					complement, m_StateFactoryForRefinement);
			assert (interNwa.checkResult(m_StateFactoryInterpolAutom));
			newAbstraction = interNwa.getResult();
		}
		// INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldApi = (new
		// RemoveUnreachable<CodeBlock,
		// IPredicate>(m_InterpolAutomatonUsedInRefinement)).getResult();
		benchmarkGenerator.addEdgeCheckerData(bhtc.getEdgeCheckerBenchmark());
		m_InterpolAutomaton = null;
		boolean isUseful = isUsefulInterpolantAutomaton(m_InterpolAutomatonUsedInRefinement, m_Counterexample);
		if (!isUseful) {
			return null;
		}

		// assert (new BuchiAccepts<CodeBlock,
		// IPredicate>(oldApi,m_Counterexample.getNestedLassoWord())).getResult()
		// : "interpolant automaton does not accept lasso.";
		// assert !(new BuchiAccepts<CodeBlock,
		// IPredicate>(newAbstraction,m_Counterexample.getNestedLassoWord())).getResult()
		// : "no progress";
		if (m_DumpAutomata) {
			final String automatonString;
			if (m_InterpolAutomatonUsedInRefinement.getCallAlphabet().isEmpty()) {
				automatonString = "interpolBuchiAutomatonUsedInRefinement";
			} else {
				automatonString = "interpolBuchiNestedWordAutomatonUsedInRefinement";
			}
			String filename = m_RootNode.getFilename() + "_" + automatonString + m_Iteration + "after";
			String message = setting.toString();
			BuchiCegarLoop.writeAutomatonToFile(m_Services, m_InterpolAutomatonUsedInRefinement, m_DumpPath, filename, message);
		}
		boolean tacasDump = false;
		if (tacasDump){
			final String determinicity;
			boolean isSemiDeterministic = (new IsSemiDeterministic<CodeBlock, IPredicate>(m_Services, m_InterpolAutomatonUsedInRefinement)).getResult();
			boolean isDeterministic = (new IsDeterministic<CodeBlock, IPredicate>(m_Services, m_InterpolAutomatonUsedInRefinement)).getResult();
			if (isDeterministic) {
				determinicity = "deterministic";
				assert isSemiDeterministic : "but semi deterministic";
			} else if (isSemiDeterministic) {
				determinicity = "semideterministic";
			} else {
				determinicity = "nondeterministic";
			}
			final String automatonString;
			if (m_InterpolAutomatonUsedInRefinement.getCallAlphabet().isEmpty()) {
				automatonString = "interpolBuchiAutomatonUsedInRefinement";
			} else {
				automatonString = "interpolBuchiNestedWordAutomatonUsedInRefinement";
			}
			String filename = m_RootNode.getFilename() + "_" + determinicity + automatonString + m_Iteration + "after";
			String message = setting.toString();
			BuchiCegarLoop.writeAutomatonToFile(m_Services, m_InterpolAutomatonUsedInRefinement, m_DumpPath, filename, message);

		}
		return newAbstraction;
	}

	private InterpolatingTraceChecker constructTraceChecker(IPredicate precond, IPredicate postcond,
			NestedWord<CodeBlock> word, SmtManager smtManager, BuchiModGlobalVarManager buchiModGlobalVarManager, 
			PredicateUnifier pu, INTERPOLATION interpolation) {
		final InterpolatingTraceChecker itc;
		switch (m_Interpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation: {
			itc = new InterpolatingTraceCheckerCraig(precond, postcond, new TreeMap<Integer, IPredicate>(), word,
					m_SmtManager, buchiModGlobalVarManager,
					/*
					 * TODO: When Matthias
					 * introduced this parameter he
					 * set the argument to AssertCodeBlockOrder.NOT_INCREMENTALLY.
					 * Check if you want to set this
					 * to a different value.
					 */AssertCodeBlockOrder.NOT_INCREMENTALLY, m_Services, false, pu, interpolation);
			break;
		}
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP: {
			itc = new TraceCheckerSpWp(precond, postcond, new TreeMap<Integer, IPredicate>(),
					word, m_SmtManager, buchiModGlobalVarManager,
					/*
					 * TODO: When Matthias
					 * introduced this parameter he
					 * set the argument to AssertCodeBlockOrder.NOT_INCREMENTALLY.
					 * Check if you want to set this
					 * to a different value.
					 */AssertCodeBlockOrder.NOT_INCREMENTALLY,
					 UnsatCores.CONJUNCT_LEVEL, true, m_Services, false, pu, interpolation, m_SmtManager);
			break;
		}
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		if (itc.getToolchainCancelledExpection() != null) {
			throw itc.getToolchainCancelledExpection();
		}
		return itc;
	}

	private boolean isUsefulInterpolantAutomaton(
			INestedWordAutomatonSimple<CodeBlock, IPredicate> interpolAutomatonUsedInRefinement,
			NestedLassoRun<CodeBlock, IPredicate> counterexample) throws AutomataLibraryException {
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldApi;
		oldApi = (new RemoveUnreachable<CodeBlock, IPredicate>(m_Services, interpolAutomatonUsedInRefinement)).getResult();
		NestedWord<CodeBlock> stem = counterexample.getStem().getWord();
		NestedWord<CodeBlock> loop = counterexample.getLoop().getWord();
		NestedWord<CodeBlock> stemAndLoop = stem.concatenate(loop);
		NestedLassoWord<CodeBlock> stemExtension = new NestedLassoWord<CodeBlock>(stemAndLoop, loop);
		NestedWord<CodeBlock> loopAndLoop = loop.concatenate(loop);
		NestedLassoWord<CodeBlock> loopExtension = new NestedLassoWord<CodeBlock>(stem, loopAndLoop);
		boolean wordAccepted = (new BuchiAccepts<CodeBlock, IPredicate>(m_Services, oldApi, counterexample.getNestedLassoWord()))
				.getResult();
		if (!wordAccepted) {
			mLogger.info("Bad chosen interpolant automaton: word not accepted");
			return false;
		}
		// 2015-01-14 Matthias: word, stemExtension, and loopExtension are only
		// different representations of the same word. The following lines
		// do not make any sense (but might be helpful to reveal a bug.
		boolean stemExtensionAccepted = (new BuchiAccepts<CodeBlock, IPredicate>(m_Services, oldApi, stemExtension)).getResult();
		if (!stemExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: stem extension not accepted");
//			mLogger.info("Bad chosen interpolant automaton: stem extension not accepted");
//			return false;
		}
		boolean loopExtensionAccepted = (new BuchiAccepts<CodeBlock, IPredicate>(m_Services, oldApi, loopExtension)).getResult();
		if (!loopExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: loop extension not accepted");
//			mLogger.info("Bad chosen interpolant automaton: loop extension not accepted");
//			return false;
		}
		return true;
	}

	private void finishComputation(INestedWordAutomatonSimple<CodeBlock, IPredicate> interpolantAutomaton,
			RefinementSetting setting) {
		switch (setting.getInterpolantAutomaton()) {
		case LassoAutomaton:
			// do nothing
			break;
		case EagerNondeterminism:
			((NondeterministicInterpolantAutomaton) interpolantAutomaton).switchToReadonlyMode();
			break;
		case ScroogeNondeterminism:
		case Deterministic:
			((BuchiInterpolantAutomatonBouncer) interpolantAutomaton).switchToReadonlyMode();
			break;
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> constructBuchiInterpolantAutomaton(IPredicate precondition,
			NestedWord<CodeBlock> stem, IPredicate[] stemInterpolants, IPredicate honda, NestedWord<CodeBlock> loop,
			IPredicate[] loopInterpolants, INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction) {
		NestedWordAutomaton<CodeBlock, IPredicate> result = new NestedWordAutomaton<CodeBlock, IPredicate>(
				m_Services, 
				abstraction.getInternalAlphabet(), abstraction.getCallAlphabet(), abstraction.getReturnAlphabet(),
				abstraction.getStateFactory());
		boolean emptyStem = stem.length() == 0;
		if (emptyStem) {
			result.addState(true, true, honda);
		} else {
			result.addState(true, false, precondition);
			for (int i = 0; i < stemInterpolants.length; i++) {
				addState(stemInterpolants[i], result);
				addTransition(i, precondition, stemInterpolants, honda, stem, result);
			}
			result.addState(false, true, honda);
			addTransition(stemInterpolants.length, precondition, stemInterpolants, honda, stem, result);
		}
		for (int i = 0; i < loopInterpolants.length; i++) {
			addState(loopInterpolants[i], result);
			addTransition(i, honda, loopInterpolants, honda, loop, result);
		}
		addTransition(loopInterpolants.length, honda, loopInterpolants, honda, loop, result);
		return result;
	}

	private void addState(IPredicate pred, NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		if (!nwa.getStates().contains(pred)) {
			nwa.addState(false, false, pred);
		}
	}

	private void addTransition(int pos, IPredicate pre, IPredicate[] predicates, IPredicate post,
			NestedWord<CodeBlock> nw, NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		IPredicate pred = getPredicateAtPosition(pos - 1, pre, predicates, post);
		IPredicate succ = getPredicateAtPosition(pos, pre, predicates, post);
		CodeBlock cb = nw.getSymbol(pos);
		if (nw.isInternalPosition(pos)) {
			nwa.addInternalTransition(pred, cb, succ);
		} else if (nw.isCallPosition(pos)) {
			nwa.addCallTransition(pred, cb, succ);
		} else if (nw.isReturnPosition(pos)) {
			assert !nw.isPendingReturn(pos);
			int k = nw.getCallPosition(pos);
			IPredicate hier = getPredicateAtPosition(k - 1, pre, predicates, post);
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
