/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker plug-in.
 * 
 * The ULTIMATE LassoRanker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryResultChecking;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


/**
 * Extract stem and loop (given as NestedWords) from a RCFG.
 * Therefore
 * - we transform the RCFG into a Büchi automaton (each state is accepting)
 * - we (try to) obtain a lasso via an emptiness check
 * - we return this stem and loop of this lasso
 * - furthermore we have to check if the input was indeed a lasso program
 * - therefore we construct an automaton that has the shape of the found lasso
 * and check if the language of the RCFG-Büchi-automaton is already included
 * in the lasso automaton (via constructing difference and checking emptiness).    
 * @author Matthias Heizmann
 */
public class LassoExtractorBuchi extends AbstractLassoExtractor {
	
	private final IUltimateServiceProvider m_Services;	
	private final INestedWordAutomaton<CodeBlock, IPredicate> m_CfgAutomaton;
	private NestedWordAutomaton<CodeBlock, IPredicate> m_LassoAutomaton;
	private final StateFactory<IPredicate> m_PredicateFactory;
	private final SmtManager m_SmtManager;
	private final ILogger mLogger;
	
	public LassoExtractorBuchi(IUltimateServiceProvider services, RootNode rootNode, SmtManager smtManager, ILogger logger) 
			throws AutomataLibraryException {
		m_Services = services;
		mLogger = logger;
		m_PredicateFactory = new PredicateFactoryResultChecking(smtManager);
		m_CfgAutomaton = constructCfgAutomaton(rootNode, smtManager);
		m_SmtManager = smtManager;
		NestedLassoRun<CodeBlock, IPredicate> run = 
				(new BuchiIsEmpty<>(new AutomataLibraryServices(m_Services), m_CfgAutomaton)).getAcceptingNestedLassoRun();

		if (run == null) {
			m_LassoFound = false;
			m_SomeNoneForErrorReport = extractSomeNodeForErrorReport(rootNode);
		} else {
			NestedLassoWord<CodeBlock> nlw = run.getNestedLassoWord();
			InCaReAlphabet<CodeBlock> alphabet = new InCaReAlphabet<>(m_CfgAutomaton);
			m_LassoAutomaton = (new LassoAutomatonBuilder(alphabet, 
					m_PredicateFactory, nlw.getStem(), nlw.getLoop())).getResult();
			INestedWordAutomaton<CodeBlock, IPredicate> difference = 
					(new BuchiDifferenceFKV<>(new AutomataLibraryServices(m_Services), m_PredicateFactory, 
							m_CfgAutomaton, m_LassoAutomaton)).getResult();
			boolean isEmpty = (new BuchiIsEmpty<>(new AutomataLibraryServices(m_Services), difference)).getResult();
			if (isEmpty) {
				m_LassoFound = true;
				m_Honda = extractHonda(run);
				m_Stem = run.getNestedLassoWord().getStem();
				m_Loop = run.getNestedLassoWord().getLoop();
			} else {
				m_LassoFound = false;
				m_SomeNoneForErrorReport = extractSomeNodeForErrorReport(rootNode);
			}
		}
	}

	
	private RCFGNode extractSomeNodeForErrorReport(RootNode rootNode) {
		return rootNode.getOutgoingNodes().iterator().next();
	}
	
	
	private ProgramPoint extractHonda(NestedLassoRun<CodeBlock, IPredicate> run) {
		return ((ISLPredicate) run.getLoop().getStateAtPosition(0)).getProgramPoint();
	}
	

	private INestedWordAutomaton<CodeBlock, IPredicate> constructCfgAutomaton(
			RootNode rootNode, SmtManager smtManager) {
		CFG2NestedWordAutomaton cFG2NestedWordAutomaton = 
				new CFG2NestedWordAutomaton(m_Services, true ,smtManager, mLogger);
		Collection<ProgramPoint> allNodes = new HashSet<ProgramPoint>();
		for (Map<String, ProgramPoint> prog2pp : 
						rootNode.getRootAnnot().getProgramPoints().values()) {
			allNodes.addAll(prog2pp.values());
		}
		return cFG2NestedWordAutomaton.getNestedWordAutomaton(
				rootNode, m_PredicateFactory, allNodes);
	}

	
	public class LassoAutomatonBuilder {
		
		private final NestedWordAutomaton<CodeBlock, IPredicate> m_Result;
		
		public LassoAutomatonBuilder(
				InCaReAlphabet<CodeBlock> alphabet,
				StateFactory<IPredicate> predicateFactory,
				NestedWord<CodeBlock> stem,
				NestedWord<CodeBlock> loop) throws AutomataOperationCanceledException {
			m_Result =	new NestedWordAutomaton<CodeBlock, IPredicate>(
					new AutomataLibraryServices(m_Services),
							alphabet.getInternalAlphabet(),
							alphabet.getCallAlphabet(),
							alphabet.getReturnAlphabet(),
							predicateFactory);
			List<IPredicate> stemStates = constructListOfDontCarePredicates(stem.length());
			List<IPredicate> loopStates = constructListOfDontCarePredicates(loop.length());
			IPredicate initialState;
			if (stem.length() == 0) {
				initialState = loopStates.get(0);
				m_Result.addState(true, true, initialState);
			} else {
				initialState = stemStates.get(0);
				m_Result.addState(true, false, initialState);
			}
			IPredicate hondaState = loopStates.get(0);
			if (stem.length() > 0) {
				m_Result.addState(false, true, hondaState);
			}
			stemStates.add(hondaState);
			loopStates.add(hondaState);
			addSequenceOfStatesButFirstAndLast(stemStates);
			m_Result.addTransitions(stem, stemStates);
			addSequenceOfStatesButFirstAndLast(loopStates);
			m_Result.addTransitions(loop, loopStates);
			try {
				assert (new BuchiAccepts<>(new AutomataLibraryServices(m_Services), m_Result, new NestedLassoWord<>(stem, loop)).getResult());
			} catch (AutomataLibraryException e) {
				throw new AssertionError(e);
			}
		}
		
		private List<IPredicate> constructListOfDontCarePredicates(int length) {
			ArrayList<IPredicate> result = new ArrayList<IPredicate>(length);
			for (int i=0; i<length; i++) {
				result.add(m_SmtManager.getPredicateFactory().newDontCarePredicate(null));
			}
			return result;
		}
		
		private void addSequenceOfStatesButFirstAndLast(List<IPredicate> states) {
			for (int i=1; i<states.size()-1; i++) {
				m_Result.addState(false, false, states.get(i));
			}
		}

		public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
			return m_Result;
		}
	}
}
