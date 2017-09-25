package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

/**
 * Provides auxiliary methods for reusing Floyd-Hoare automata from ats files.
 * @author Bat-Chen Rothenberg (batcheni89@gmail.com)
 *
 */
public class AutomataReuseUtils {
	
	static final <LETTER extends IIcfgTransition<?>> List<INestedWordAutomaton<LETTER, IPredicate>> interpretAutomata(
			final List<NestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction, 
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata, 
			final IUltimateServiceProvider services, final PredicateFactory predicateFactory, final ILogger logger) {

		Boolean debugOn = false;
		List<INestedWordAutomaton<LETTER, IPredicate>> res = new ArrayList<INestedWordAutomaton<LETTER, IPredicate>>();

		for (final NestedWordAutomaton<String, String> rawAutomatonFromFile : rawFloydHoareAutomataFromFile) {
			// Create map from strings to "new" letters (abstraction letters)
			HashMap<String, LETTER> mapStringToLetter = new HashMap<String, LETTER>();
			VpAlphabet<LETTER> abstractionAlphabet = abstraction.getVpAlphabet();
			for (final LETTER letter : (abstractionAlphabet.getCallAlphabet())) {
				if (!mapStringToLetter.containsKey(letter.toString())) {
					mapStringToLetter.put(letter.toString(), letter);
				}
			}
			for (final LETTER letter : (abstractionAlphabet.getInternalAlphabet())) {
				if (!mapStringToLetter.containsKey(letter.toString())) {
					mapStringToLetter.put(letter.toString(), letter);
				}
			}
			for (final LETTER letter : (abstractionAlphabet.getReturnAlphabet())) {
				if (!mapStringToLetter.containsKey(letter.toString())) {
					mapStringToLetter.put(letter.toString(), letter);
				}
			}
			if (debugOn) {
				// Create Debug information for letters
				int removedLetters = 0;
				int reusedLetters = 0;
				for (String strLetter : rawAutomatonFromFile.getVpAlphabet().getCallAlphabet()) {
					if (!mapStringToLetter.containsKey(strLetter)) {
						removedLetters++;
					} else {
						reusedLetters++;
					}
				}
				for (String strLetter : rawAutomatonFromFile.getVpAlphabet().getInternalAlphabet()) {
					if (!mapStringToLetter.containsKey(strLetter)) {
						removedLetters++;
					} else {
						reusedLetters++;
					}
				}
				for (String strLetter : rawAutomatonFromFile.getVpAlphabet().getReturnAlphabet()) {
					if (!mapStringToLetter.containsKey(strLetter)) {
						removedLetters++;
					} else {
						reusedLetters++;
					}
				}
				int totalLetters = removedLetters + reusedLetters;
				logger.info("Reusing " + reusedLetters + "/" + totalLetters
						+ " letters when constructing automaton from file.");
			}
			// Create empty automaton with same alphabet
			final NestedWordAutomaton<LETTER, IPredicate> resAutomaton = new NestedWordAutomaton<>(
					new AutomataLibraryServices(services), abstractionAlphabet, predicateFactoryInterpolantAutomata);
			// Add states
			Set<String> statesOfRawAutomaton = rawAutomatonFromFile.getStates();
			HashMap<String, IPredicate> mapStringToFreshState = new HashMap<>();
			for (final String stringState : statesOfRawAutomaton) {
				IPredicate predicateState = predicateFactory.newDebugPredicate(stringState);
				mapStringToFreshState.put(stringState, predicateState);
				final boolean isInitial = rawAutomatonFromFile.isInitial(stringState);
				final boolean isFinal = rawAutomatonFromFile.isFinal(stringState);
				resAutomaton.addState(isInitial, isFinal, predicateState);
			}
			// Add transitions
			int removedTransitions = 0;
			int reusedTransitions = 0;
			for (final IPredicate predicateState : resAutomaton.getStates()) {
				String stringState = predicateState.toString();
				for (OutgoingCallTransition<String, String> callTransition : rawAutomatonFromFile
						.callSuccessors(stringState)) {
					String transitionLetter = callTransition.getLetter();
					String transitionSuccString = callTransition.getSucc();
					if (mapStringToLetter.containsKey(transitionLetter)) {
						LETTER letter = mapStringToLetter.get(transitionLetter);
						IPredicate succState = mapStringToFreshState.get(transitionSuccString);
						resAutomaton.addCallTransition(predicateState, letter, succState);
						reusedTransitions++;
					} else {
						removedTransitions++;
					}
				}
				for (OutgoingInternalTransition<String, String> internalTransition : rawAutomatonFromFile
						.internalSuccessors(stringState)) {
					String transitionLetter = internalTransition.getLetter();
					String transitionSuccString = internalTransition.getSucc();
					if (mapStringToLetter.containsKey(transitionLetter)) {
						LETTER letter = mapStringToLetter.get(transitionLetter);
						IPredicate succState = mapStringToFreshState.get(transitionSuccString);
						resAutomaton.addInternalTransition(predicateState, letter, succState);
						reusedTransitions++;
					} else {
						removedTransitions++;
					}
				}
				for (OutgoingReturnTransition<String, String> returnTransition : rawAutomatonFromFile
						.returnSuccessors(stringState)) {
					String transitionLetter = returnTransition.getLetter();
					String transitionSuccString = returnTransition.getSucc();
					String transitionHeirPredString = returnTransition.getHierPred();
					if (mapStringToLetter.containsKey(transitionLetter)) {
						LETTER letter = mapStringToLetter.get(transitionLetter);
						IPredicate succState = mapStringToFreshState.get(transitionSuccString);
						IPredicate heirPredState = mapStringToFreshState.get(transitionHeirPredString);
						resAutomaton.addReturnTransition(predicateState, heirPredState, letter, succState);
						reusedTransitions++;
					} else {
						removedTransitions++;
					}
				}
			}
			int totalTransitions = removedTransitions + reusedTransitions;
			if (debugOn) {
				logger.info("Reusing " + reusedTransitions + "/" + totalTransitions
						+ " transitions when constructing automaton from file.");
			}
			// Add new automaton to list
			res.add(resAutomaton);
		}

		return res;
	}
	
}