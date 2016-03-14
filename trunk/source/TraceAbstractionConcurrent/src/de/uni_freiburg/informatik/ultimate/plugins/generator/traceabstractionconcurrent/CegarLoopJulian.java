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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.DifferenceBlackAndWhite;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.FinitePrefix2PetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder.order;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;

public class CegarLoopJulian extends BasicCegarLoop {

	private BranchingProcess<CodeBlock, IPredicate> m_Unfolding;
	public int m_CoRelationQueries = 0;
	public int m_BiggestAbstractionTransitions;

	public CegarLoopJulian(String name, RootNode rootNode, SmtManager smtManager,
			TraceAbstractionBenchmarks timingStatistics, TAPreferences taPrefs, Collection<ProgramPoint> errorLocs,
			IUltimateServiceProvider services, IToolchainStorage storage) {
		super(name, rootNode, smtManager, taPrefs, errorLocs, INTERPOLATION.Craig_TreeInterpolation, false, services, storage);
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		TaConcurContentFactory contentFactory = new TaConcurContentFactory(
				m_RootNode.getRootAnnot().getProgramPoints(), this, super.m_SmtManager, super.m_Pref,
				m_Pref.computeHoareAnnotation(), false);
		Cfg2NetJulian cFG2Automaton = new Cfg2NetJulian(m_RootNode, contentFactory, m_SmtManager, m_Services);
		m_Abstraction = cFG2Automaton.getResult();

		if (m_Iteration <= m_Pref.watchIteration()
				&& (m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref.artifact() == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
		if (m_Pref.dumpAutomata()) {
			String filename = "Abstraction" + m_Iteration;
			writeAutomatonToFile(m_Abstraction, filename);
		}
	}

	@Override
	protected void constructInterpolantAutomaton() throws OperationCanceledException {
		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime);
		StraightLineInterpolantAutomatonBuilder iab = new StraightLineInterpolantAutomatonBuilder(
				m_Services, new InCaReAlphabet<CodeBlock>(m_Abstraction), m_InterpolantGenerator, m_PredicateFactoryInterpolantAutomata);
		m_InterpolAutomaton = iab.getResult();
		mLogger.info("Interpolatants " + m_InterpolAutomaton.getStates());

		m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime);
		assert (accepts(m_Services, m_InterpolAutomaton, m_Counterexample.getWord())) : "Interpolant automaton broken!";
		assert (new InductivityCheck(m_Services, m_InterpolAutomaton, false, true,
				new IncrementalHoareTripleChecker(m_RootNode.getRootAnnot().getManagedScript(), m_ModGlobVarManager, m_SmtManager.getBoogie2Smt()))).getResult() : "Not inductive";
	}

	@Override
	protected boolean isAbstractionCorrect() throws OperationCanceledException {
		PetriNetJulian<CodeBlock, IPredicate> abstraction = (PetriNetJulian<CodeBlock, IPredicate>) m_Abstraction;
		String orderString = m_Pref.order();
		boolean cutOffSameTrans = m_Pref.cutOffRequiresSameTransition();
		order ord;
		if (orderString.equals(order.KMM.getDescription())) {
			ord = order.KMM;
		} else if (orderString.equals(order.ERV.getDescription())) {
			ord = order.ERV;
		} else if (orderString.equals(order.ERV_MARK.getDescription())) {
			ord = order.ERV_MARK;
		} else {
			throw new IllegalArgumentException();
		}

		PetriNetUnfolder<CodeBlock, IPredicate> unf = new PetriNetUnfolder<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), abstraction, ord,
				cutOffSameTrans, !m_Pref.unfoldingToNet());
		m_Unfolding = unf.getFinitePrefix();
		m_CoRelationQueries += m_Unfolding.getCoRelationQueries();

		m_Counterexample = unf.getAcceptingRun();
		if (m_Counterexample == null) {
			return true;
		} else {
			if (m_Pref.dumpAutomata()) {
				dumpNestedRun(m_Counterexample, m_IterationPW, mLogger);
			}
			return false;
		}
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		PetriNetJulian<CodeBlock, IPredicate> abstraction = (PetriNetJulian<CodeBlock, IPredicate>) m_Abstraction;
		if (m_Pref.unfoldingToNet()) {
			abstraction = (new FinitePrefix2PetriNet<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), m_Unfolding)).getResult();
		}

		// Determinize the interpolant automaton
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> dia = determinizeInterpolantAutomaton(m_InterpolAutomaton);

		// Complement the interpolant automaton
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> nia = (new ComplementDD<CodeBlock, IPredicate>(
				new AutomataLibraryServices(m_Services), m_PredicateFactoryInterpolantAutomata, dia)).getResult();
		assert (!accepts(m_Services, nia, m_Counterexample.getWord())) : "Complementation broken!";
		mLogger.info("Complemented interpolant automaton has " + nia.getStates().size() + " states");

		if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
			m_ArtifactAutomaton = (NestedWordAutomaton<CodeBlock, IPredicate>) nia;
		}
		m_Abstraction = (new DifferenceBlackAndWhite<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), abstraction,
				(NestedWordAutomaton<CodeBlock, IPredicate>) dia)).getResult();

		m_CegarLoopBenchmark.reportAbstractionSize(m_Abstraction.size(), m_Iteration);
		// if (m_BiggestAbstractionSize < m_Abstraction.size()){
		// m_BiggestAbstractionSize = m_Abstraction.size();
		// m_BiggestAbstractionTransitions =
		// abstraction.getTransitions().size();
		// m_BiggestAbstractionIteration = m_Iteration;
		// }

		assert (!acceptsPetriViaFA(m_Services, m_Abstraction, m_Counterexample.getWord())) : "Intersection broken!";

		// int[] statistic = m_Abstraction.transitions();
		// s_Logger.debug("Abstraction has " +
		// m_Abstraction.getAllStates().size() + "states, " +
		// statistic[0] + " internal transitions " + statistic[1] +
		// "call transitions " + statistic[2]+ " return transitions ");

		if (m_Iteration <= m_Pref.watchIteration()
				&& (m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref.artifact() == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
		if (m_Pref.dumpAutomata()) {
			String filename = "Abstraction" + m_Iteration;
			writeAutomatonToFile(m_Abstraction, filename);
		}
		return true;
	}

	@Override
	protected void computeCFGHoareAnnotation() {
		throw new UnsupportedOperationException();
	}

	private static boolean acceptsPetriViaFA(IUltimateServiceProvider services, IAutomaton<CodeBlock, IPredicate> automaton, Word<CodeBlock> word)
			throws OperationCanceledException {
		NestedWord<CodeBlock> nw = NestedWord.nestedWord(word);
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> petriNetAsFA = (new PetriNet2FiniteAutomaton<CodeBlock, IPredicate>(
				new AutomataLibraryServices(services), (IPetriNet<CodeBlock, IPredicate>) automaton)).getResult();
		return BasicCegarLoop.accepts(services, petriNetAsFA, nw);

	}

}
