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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryResultChecking;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;


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
	
	private final IUltimateServiceProvider mServices;
	private final INestedWordAutomatonSimple<CodeBlock, IPredicate> mCfgAutomaton;
	private INestedWordAutomatonSimple<CodeBlock, IPredicate> mLassoAutomaton;
	private final IStateFactory<IPredicate> mPredicateFactoryRc;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;
	private final ILogger mLogger;
	
	public LassoExtractorBuchi(final IUltimateServiceProvider services, final RootNode rootNode, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final ILogger logger)
			throws AutomataLibraryException {
		mServices = services;
		mLogger = logger;
		mPredicateFactoryRc = new PredicateFactoryResultChecking(predicateFactory);
		mCfgAutomaton = constructCfgAutomaton(rootNode, csToolkit);
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
		final NestedLassoRun<CodeBlock, IPredicate> run =
				(new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), mCfgAutomaton)).getAcceptingNestedLassoRun();

		if (run == null) {
			mLassoFound = false;
			mSomeNoneForErrorReport = extractSomeNodeForErrorReport(rootNode);
		} else {
			final NestedLassoWord<CodeBlock> nlw = run.getNestedLassoWord();
			final InCaReAlphabet<CodeBlock> alphabet = new InCaReAlphabet<>(mCfgAutomaton);
			mLassoAutomaton = (new LassoAutomatonBuilder(alphabet,
					mPredicateFactoryRc, nlw.getStem(), nlw.getLoop())).getResult();
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> difference =
					(new BuchiDifferenceFKV<>(new AutomataLibraryServices(mServices), mPredicateFactoryRc,
							mCfgAutomaton, mLassoAutomaton)).getResult();
			final boolean isEmpty = (new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), difference)).getResult();
			if (isEmpty) {
				mLassoFound = true;
				mHonda = extractHonda(run);
				mStem = run.getNestedLassoWord().getStem();
				mLoop = run.getNestedLassoWord().getLoop();
			} else {
				mLassoFound = false;
				mSomeNoneForErrorReport = extractSomeNodeForErrorReport(rootNode);
			}
		}
	}

	
	private IcfgLocation extractSomeNodeForErrorReport(final RootNode rootNode) {
		return rootNode.getOutgoingNodes().iterator().next();
	}
	
	
	private BoogieIcfgLocation extractHonda(final NestedLassoRun<CodeBlock, IPredicate> run) {
		return ((ISLPredicate) run.getLoop().getStateAtPosition(0)).getProgramPoint();
	}
	

	private INestedWordAutomatonSimple<CodeBlock, IPredicate> constructCfgAutomaton(
			final RootNode rootNode, final CfgSmtToolkit csToolkit) {
		final CFG2NestedWordAutomaton cFG2NestedWordAutomaton =
				new CFG2NestedWordAutomaton(mServices, true ,csToolkit, mPredicateFactory, mLogger);
		final Collection<BoogieIcfgLocation> allNodes = new HashSet<BoogieIcfgLocation>();
		for (final Map<String, BoogieIcfgLocation> prog2pp :
						rootNode.getRootAnnot().getProgramPoints().values()) {
			allNodes.addAll(prog2pp.values());
		}
		return cFG2NestedWordAutomaton.getNestedWordAutomaton(
				rootNode, mPredicateFactoryRc, allNodes);
	}

	
	public class LassoAutomatonBuilder {
		
		private final NestedWordAutomaton<CodeBlock, IPredicate> mResult;
		
		public LassoAutomatonBuilder(
				final InCaReAlphabet<CodeBlock> alphabet,
				final IStateFactory<IPredicate> predicateFactory,
				final NestedWord<CodeBlock> stem,
				final NestedWord<CodeBlock> loop) throws AutomataOperationCanceledException {
			mResult =	new NestedWordAutomaton<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices),
							alphabet.getInternalAlphabet(),
							alphabet.getCallAlphabet(),
							alphabet.getReturnAlphabet(),
							predicateFactory);
			final List<IPredicate> stemStates = constructListOfDontCarePredicates(stem.length());
			final List<IPredicate> loopStates = constructListOfDontCarePredicates(loop.length());
			IPredicate initialState;
			if (stem.length() == 0) {
				initialState = loopStates.get(0);
				mResult.addState(true, true, initialState);
			} else {
				initialState = stemStates.get(0);
				mResult.addState(true, false, initialState);
			}
			final IPredicate hondaState = loopStates.get(0);
			if (stem.length() > 0) {
				mResult.addState(false, true, hondaState);
			}
			stemStates.add(hondaState);
			loopStates.add(hondaState);
			addSequenceOfStatesButFirstAndLast(stemStates);
			mResult.addTransitions(stem, stemStates);
			addSequenceOfStatesButFirstAndLast(loopStates);
			mResult.addTransitions(loop, loopStates);
			try {
				assert (new BuchiAccepts<>(new AutomataLibraryServices(mServices), mResult, new NestedLassoWord<>(stem, loop)).getResult());
			} catch (final AutomataLibraryException e) {
				throw new AssertionError(e);
			}
		}
		
		private List<IPredicate> constructListOfDontCarePredicates(final int length) {
			final ArrayList<IPredicate> result = new ArrayList<IPredicate>(length);
			for (int i=0; i<length; i++) {
				result.add(mPredicateFactory.newDontCarePredicate(null));
			}
			return result;
		}
		
		private void addSequenceOfStatesButFirstAndLast(final List<IPredicate> states) {
			for (int i=1; i<states.size()-1; i++) {
				mResult.addState(false, false, states.get(i));
			}
		}

		public INestedWordAutomatonSimple<CodeBlock, IPredicate> getResult() {
			return mResult;
		}
	}
}
