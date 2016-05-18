/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstractionConcurrent plug-in.
 * 
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

public class CegarLoopConcurrentAutomata extends BasicCegarLoop {

	public CegarLoopConcurrentAutomata(String name, RootNode rootNode, SmtManager smtManager,
			TraceAbstractionBenchmarks timingStatistics, TAPreferences taPrefs, Collection<ProgramPoint> errorLocs,
			IUltimateServiceProvider services, IToolchainStorage storage) {
		super(name, rootNode, smtManager, taPrefs, errorLocs, INTERPOLATION.Craig_TreeInterpolation, false, services, storage);
		// m_ContentFactory = new TaConcurContentFactory(
		// rootNode.getRootAnnot().getLocNodes(),
		// this,
		// super.m_SmtManager.getTheory(),
		// super.m_HoareAnnotation,
		// false);
	}

	@Override
	protected void constructInterpolantAutomaton() throws OperationCanceledException {
		m_CegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString());
		StraightLineInterpolantAutomatonBuilder iab = new StraightLineInterpolantAutomatonBuilder(
				m_Services, new InCaReAlphabet<CodeBlock>(m_Abstraction), m_InterpolantGenerator, m_PredicateFactoryInterpolantAutomata);
		m_InterpolAutomaton = iab.getResult();
		mLogger.info("Interpolatants " + m_InterpolAutomaton.getStates());

		m_CegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString());
		assert (accepts(m_Services, m_InterpolAutomaton, m_Counterexample.getWord())) : "Interpolant automaton broken!";
		assert (new InductivityCheck(m_Services, m_InterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(m_RootNode.getRootAnnot().getManagedScript(), m_ModGlobVarManager, m_SmtManager.getBoogie2Smt()))).getResult() : "Not inductive";
	}

	@Override
	protected void getInitialAbstraction() {
		StateFactory<IPredicate> predicateFactory = new PredicateFactoryForInterpolantAutomata(super.m_SmtManager, m_Pref);
		CFG2Automaton cFG2NestedWordAutomaton = new Cfg2Nwa(m_RootNode, predicateFactory, m_SmtManager, m_Services);
		m_Abstraction = (NestedWordAutomaton<CodeBlock, IPredicate>) cFG2NestedWordAutomaton.getResult();

		if (m_Iteration <= m_Pref.watchIteration()
				&& (m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref.artifact() == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
	}

	@Override
	protected Collection<Set<IPredicate>> computePartition(INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton) {
		mLogger.info("Start computation of initial partition.");
		Collection<IPredicate> states = automaton.getStates();
		Map<Set<ProgramPoint>, Set<IPredicate>> pp2p = new HashMap<Set<ProgramPoint>, Set<IPredicate>>();
		for (IPredicate p : states) {
			IMLPredicate mp = (IMLPredicate) p;
			pigeonHole(pp2p, mp);
		}
		Collection<Set<IPredicate>> partition = new ArrayList<Set<IPredicate>>();
		for (Set<ProgramPoint> pps : pp2p.keySet()) {
			Set<IPredicate> statesWithSamePP = pp2p.get(pps);
			partition.add(statesWithSamePP);
		}
		mLogger.info("Finished computation of initial partition.");
		return partition;
	}

	/**
	 * Pigeon-hole (german: einsortieren) predicates according to their
	 * ProgramPoint
	 */
	protected void pigeonHole(Map<Set<ProgramPoint>, Set<IPredicate>> pp2p, IMLPredicate mp) {
		Set<IPredicate> statesWithSamePPs = pp2p.get(asHashSet(mp.getProgramPoints()));
		if (statesWithSamePPs == null) {
			statesWithSamePPs = new HashSet<IPredicate>();
			pp2p.put(asHashSet(mp.getProgramPoints()), statesWithSamePPs);
		}
		statesWithSamePPs.add(mp);
	}

	private static <E> Set<E> asHashSet(E[] array) {
		return new HashSet<E>(Arrays.asList(array));
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		m_StateFactoryForRefinement.setIteration(super.m_Iteration);
		// howDifferentAreInterpolants(m_InterpolAutomaton.getStates());

		m_CegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		boolean explointSigmaStarConcatOfIA = !m_ComputeHoareAnnotation;

		PredicateFactoryForInterpolantAutomata predicateFactory = (PredicateFactoryForInterpolantAutomata) m_Abstraction.getStateFactory();

		INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldAbstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		Map<IPredicate, Set<IPredicate>> removedDoubleDeckers = null;
		Map<IPredicate, IPredicate> context2entry = null;
		IHoareTripleChecker htc = getEfficientHoareTripleChecker(m_Services, m_Pref.getHoareTripleChecks(), 
				m_SmtManager, m_ModGlobVarManager, m_InterpolantGenerator.getPredicateUnifier());
		mLogger.debug("Start constructing difference");
//		assert (oldAbstraction.getStateFactory() == m_InterpolAutomaton.getStateFactory());

		IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;

		DeterministicInterpolantAutomaton determinized = new DeterministicInterpolantAutomaton(
				m_Services, m_SmtManager, m_ModGlobVarManager, htc, oldAbstraction, m_InterpolAutomaton,
				m_InterpolantGenerator.getPredicateUnifier(), mLogger, false, false);
		// ComplementDeterministicNwa<CodeBlock, IPredicate>
		// cdnwa = new ComplementDeterministicNwa<>(dia);
		PowersetDeterminizer<CodeBlock, IPredicate> psd2 = new PowersetDeterminizer<CodeBlock, IPredicate>(
				determinized, false, m_PredicateFactoryInterpolantAutomata);

		if (m_Pref.differenceSenwa()) {
			diff = new DifferenceSenwa<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), oldAbstraction, (INestedWordAutomaton<CodeBlock, IPredicate>) determinized, psd2, false);
		} else {
			diff = new Difference<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), oldAbstraction, determinized, psd2,
					m_StateFactoryForRefinement, explointSigmaStarConcatOfIA);
		}
		determinized.switchToReadonlyMode();
		assert !m_SmtManager.isLocked();
		assert (new InductivityCheck(m_Services, m_InterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(m_RootNode.getRootAnnot().getManagedScript(), m_ModGlobVarManager, m_SmtManager.getBoogie2Smt()))).getResult();
		// do the following check only to obtain logger messages of
		// checkInductivity

		if (REMOVE_DEAD_ENDS) {
			if (m_ComputeHoareAnnotation) {
				Difference<CodeBlock, IPredicate> difference = (Difference<CodeBlock, IPredicate>) diff;
				m_Haf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
			}
			diff.removeDeadEnds();
			if (m_ComputeHoareAnnotation) {
				m_Haf.addDeadEndDoubleDeckers(diff);
			}
		}

		m_Abstraction = (IAutomaton<CodeBlock, IPredicate>) diff.getResult();
		// m_DeadEndRemovalTime = diff.getDeadEndRemovalTime();
		if (m_Pref.dumpAutomata()) {
			String filename = "InterpolantAutomaton_Iteration" + m_Iteration;
			super.writeAutomatonToFile(m_InterpolAutomaton, filename);
		}

		m_CegarLoopBenchmark.addEdgeCheckerData(htc.getEdgeCheckerBenchmark());
		m_CegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());

		Minimization minimization = m_Pref.minimize();
		switch (minimization) {
		case NONE:
			break;
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
			minimizeAbstraction(m_StateFactoryForRefinement, m_PredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}

		boolean stillAccepted = (new Accepts<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), 
				(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction,
				(NestedWord<CodeBlock>) m_Counterexample.getWord())).getResult();
		if (stillAccepted) {
			return false;
		} else {
			return true;
		}
	}
}
