/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;

/**
 * Subclass of {@link BasicCegarLoop} in which we initially subtract from the
 * abstraction a set of given Floyd-Hoare automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class EagerReuseCegarLoop<LETTER extends IIcfgTransition<?>> extends BasicCegarLoop<LETTER> {


	private enum MinimizeInitially { NEVER, AFTER_EACH_DIFFERENCE, ONCE_AT_END };
	private final MinimizeInitially mMinimize = MinimizeInitially.AFTER_EACH_DIFFERENCE;
	
	private final List<AbstractInterpolantAutomaton<LETTER>> mFloydHoareAutomataFromOtherErrorLocations;
	private final List<NestedWordAutomaton<String, String>> mRawFloydHoareAutomataFromFile;

	/**
	 * The following can be costly. Enable only for debugging or analyzing our
	 * algorithm 
	 */
	private static final boolean IDENTIFY_USELESS_FLOYDHOARE_AUTOMATA = false;

	

	public EagerReuseCegarLoop(final String name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs, final Collection<? extends IcfgLocation> errorLocs,
			final InterpolationTechnique interpolation, final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final List<AbstractInterpolantAutomaton<LETTER>> floydHoareAutomataFromOtherLocations, 
			final List<NestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation, services,
				storage);
		mFloydHoareAutomataFromOtherErrorLocations = floydHoareAutomataFromOtherLocations;
		mRawFloydHoareAutomataFromFile = rawFloydHoareAutomataFromFile;
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		super.getInitialAbstraction();
		
		final List<INestedWordAutomaton<LETTER, IPredicate>> floydHoareAutomataFromFiles = interpretAutomata(
				mRawFloydHoareAutomataFromFile, (INestedWordAutomaton<LETTER, IPredicate>) mAbstraction, mCsToolkit, mPredicateFactoryInterpolantAutomata);
		
		mLogger.info("Reusing " + mFloydHoareAutomataFromOtherErrorLocations.size() + " Floyd-Hoare automata.");
		for (int i=0; i<mFloydHoareAutomataFromOtherErrorLocations.size(); i++) {
			final AbstractInterpolantAutomaton<LETTER> ai = mFloydHoareAutomataFromOtherErrorLocations.get(i);
			final int internalTransitionsBeforeDifference = ai.computeNumberOfInternalTransitions();
			ai.switchToOnDemandConstructionMode();
			final PowersetDeterminizer<LETTER, IPredicate> psd =
					new PowersetDeterminizer<>(ai, true, mPredicateFactoryInterpolantAutomata);
			IOpWithDelayedDeadEndRemoval<LETTER, IPredicate> diff;
			final boolean explointSigmaStarConcatOfIA = true;
			diff = new Difference<LETTER, IPredicate>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, ai, psd,
					explointSigmaStarConcatOfIA);
			ai.switchToReadonlyMode();
			final int internalTransitionsAfterDifference = ai.computeNumberOfInternalTransitions();
			mLogger.info("Floyd-Hoare automaton" + i + " had " + internalTransitionsAfterDifference + 
					" internal transitions before reuse, on-demand computation of difference added " + 
					(internalTransitionsAfterDifference - internalTransitionsBeforeDifference) + " more.");
			if (REMOVE_DEAD_ENDS) {
				if (mComputeHoareAnnotation) {
					final Difference<LETTER, IPredicate> difference = (Difference<LETTER, IPredicate>) diff;
					mHaf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
				}
				diff.removeDeadEnds();
				if (mComputeHoareAnnotation) {
					mHaf.addDeadEndDoubleDeckers(diff);
				}
			}
			if (IDENTIFY_USELESS_FLOYDHOARE_AUTOMATA) {
				final AutomataLibraryServices als = new AutomataLibraryServices(mServices);
				final Boolean noTraceExcluded = new IsIncluded<>(als, mPredicateFactoryResultChecking,
						(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, diff.getResult())
								.getResult();
				if (noTraceExcluded) {
					mLogger.warn("Floyd-Hoare automaton" + i
							+ " did not remove an error trace from abstraction and was hence useless for this error location.");
				} else {
					mLogger.info("Floyd-Hoare automaton" + i + " removed at least one error trace from the abstraction.");
				}
				
			}
			mAbstraction = diff.getResult();
			
			if (mAbstraction.size() == 0) {
				// stop to compute differences if abstraction is already empty
				break;
			}
			
			if (mMinimize == MinimizeInitially.AFTER_EACH_DIFFERENCE) {
				minimizeAbstractionIfEnabled();
			}
		}
		if (mMinimize == MinimizeInitially.ONCE_AT_END) {
			minimizeAbstractionIfEnabled();
		}
	}

	private List<INestedWordAutomaton<LETTER, IPredicate>> interpretAutomata(
			final List<NestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction, final CfgSmtToolkit csToolkit,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata) {
		
		List<INestedWordAutomaton<LETTER, IPredicate>> res = new ArrayList<INestedWordAutomaton<LETTER,IPredicate>>();
		
		for (final NestedWordAutomaton<String,String> rawAutomatonFromFile : rawFloydHoareAutomataFromFile) {
			//Create map from strings to "new" letters (abstraction letters)
			HashMap<String, LETTER> mapStringToLetter = new HashMap<String, LETTER>();
			VpAlphabet<LETTER> abstractionAlphabet = abstraction.getVpAlphabet();
			for (final LETTER letter : (abstractionAlphabet.getCallAlphabet())) {
				if (!mapStringToLetter.containsKey(letter.toString())){
					mapStringToLetter.put(letter.toString(), letter);
				}
			}
			for (final LETTER letter : (abstractionAlphabet.getInternalAlphabet())) {
				if (!mapStringToLetter.containsKey(letter.toString())){
					mapStringToLetter.put(letter.toString(), letter);
				}
			}
			for (final LETTER letter : (abstractionAlphabet.getReturnAlphabet())) {
				if (!mapStringToLetter.containsKey(letter.toString())){
					mapStringToLetter.put(letter.toString(), letter);
				}
			}
			//Create empty automaton with same alphabet
			final NestedWordAutomaton<LETTER, IPredicate> resAutomaton = new NestedWordAutomaton<>(
					new AutomataLibraryServices(mServices), abstractionAlphabet,
					mPredicateFactoryInterpolantAutomata);
			//Add states 
			Set<String> statesOfRawAutomaton = rawAutomatonFromFile.getStates();
			HashMap<String,IPredicate> mapStringToFreshState = new HashMap<>();
			for (final String stringState : statesOfRawAutomaton) {
				IPredicate predicateState = mPredicateFactory.newDebugPredicate(stringState);
				mapStringToFreshState.put(stringState, predicateState);
				final boolean isInitial = rawAutomatonFromFile.isInitial(stringState);
				final boolean isFinal = rawAutomatonFromFile.isFinal(stringState);
				resAutomaton.addState(isInitial, isFinal, predicateState);
			}
			//Add transitions
			for (final IPredicate predicateState : resAutomaton.getStates()) {
				String stringState = predicateState.toString();
				for (OutgoingCallTransition<String, String> callTransition : rawAutomatonFromFile.callSuccessors(stringState)) {
					String transitionLetter = callTransition.getLetter();
					String transitionSuccString = callTransition.getSucc();
					if (mapStringToLetter.containsKey(transitionLetter)) {
						LETTER letter = mapStringToLetter.get(transitionLetter);
						IPredicate succState = mapStringToFreshState.get(transitionSuccString);
						resAutomaton.addCallTransition(predicateState, letter, succState);
					}
				}
				for (OutgoingInternalTransition<String, String> internalTransition : rawAutomatonFromFile.internalSuccessors(stringState)) {
					String transitionLetter = internalTransition.getLetter();
					String transitionSuccString = internalTransition.getSucc();
					if (mapStringToLetter.containsKey(transitionLetter)) {
						LETTER letter = mapStringToLetter.get(transitionLetter);
						IPredicate succState = mapStringToFreshState.get(transitionSuccString);
						resAutomaton.addInternalTransition(predicateState, letter, succState);
					}
				}
				for (OutgoingReturnTransition<String, String> returnTransition : rawAutomatonFromFile.returnSuccessors(stringState)) {
					String transitionLetter = returnTransition.getLetter();
					String transitionSuccString = returnTransition.getSucc();
					String transitionHeirPredString = returnTransition.getHierPred();
					if (mapStringToLetter.containsKey(transitionLetter)) {
						LETTER letter = mapStringToLetter.get(transitionLetter);
						IPredicate succState = mapStringToFreshState.get(transitionSuccString);
						IPredicate heirPredState = mapStringToFreshState.get(transitionHeirPredString);
						resAutomaton.addReturnTransition(predicateState, heirPredState, letter, succState);
					}
				}
			}
			
			//Add new automaton to list
			res.add(resAutomaton);
		}
		
		return res;
	}
	
	

}
