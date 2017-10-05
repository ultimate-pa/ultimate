package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;

/**
 * Provides auxiliary methods for reusing Floyd-Hoare automata from ats files.
 * 
 * @author Bat-Chen Rothenberg (batcheni89@gmail.com)
 *
 */
public class AutomataReuseUtils {

	static final <LETTER extends IIcfgTransition<?>> List<INestedWordAutomaton<LETTER, IPredicate>> interpretAutomata(
			final List<NestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final IUltimateServiceProvider services, final PredicateFactory predicateFactory, final ILogger logger,
			final CfgSmtToolkit csToolkit) {
		
		final PredicateParsingWrapperScript ppws = new PredicateParsingWrapperScript(csToolkit);

		final Boolean debugOn = true;
		final List<INestedWordAutomaton<LETTER, IPredicate>> res = new ArrayList<INestedWordAutomaton<LETTER, IPredicate>>();

		for (final NestedWordAutomaton<String, String> rawAutomatonFromFile : rawFloydHoareAutomataFromFile) {
			final PredicateUnifier pu = new PredicateUnifier(services, csToolkit.getManagedScript(), predicateFactory,
					csToolkit.getSymbolTable(), SimplificationTechnique.SIMPLIFY_DDA,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
			
			// Create map from strings to all equivalent "new" letters (abstraction letters)
			final HashMap<String, Set<LETTER>> mapStringToLetter = new HashMap<String, Set<LETTER>>();
			final VpAlphabet<LETTER> abstractionAlphabet = abstraction.getVpAlphabet();
			addLettersToStringMap(mapStringToLetter, abstractionAlphabet.getCallAlphabet());
			addLettersToStringMap(mapStringToLetter, abstractionAlphabet.getInternalAlphabet());
			addLettersToStringMap(mapStringToLetter, abstractionAlphabet.getReturnAlphabet());
			//Print debug information for letters
			if (debugOn) {
				countReusedAndRemovedLetters(rawAutomatonFromFile.getVpAlphabet(),
						mapStringToLetter, logger);
			}
			// Create empty automaton with same alphabet
			final NestedWordAutomaton<LETTER, IPredicate> resAutomaton = new NestedWordAutomaton<>(
					new AutomataLibraryServices(services), abstractionAlphabet, predicateFactoryInterpolantAutomata);
			// Add states
			final Set<String> statesOfRawAutomaton = rawAutomatonFromFile.getStates();
			final HashMap<String, IPredicate> mapStringToFreshState = new HashMap<>();
			for (final String stringState : statesOfRawAutomaton) {
				final IPredicate predicateState = getPredicateFromString(predicateFactory, stringState);
				mapStringToFreshState.put(stringState, predicateState);
				final boolean isInitial = rawAutomatonFromFile.isInitial(stringState);
				final boolean isFinal = rawAutomatonFromFile.isFinal(stringState);
				resAutomaton.addState(isInitial, isFinal, predicateState);
			}
			// Add transitions
			addTransitionsFromRawAutomaton(resAutomaton, rawAutomatonFromFile, mapStringToLetter, mapStringToFreshState, 
					debugOn, logger);
			// Add new automaton to list
			res.add(resAutomaton);
		}

		return res;
	}

	private static final IPredicate getPredicateFromString(final PredicateFactory predicateFactory, final String str) {
		return predicateFactory.newDebugPredicate(str);
	}

	private static final <LETTER> void addLettersToStringMap(HashMap<String, Set<LETTER>> map,
			final Set<LETTER> letters) {
		for (LETTER letter : letters) {
			if (!map.containsKey(letter.toString())) {
				Set<LETTER> equivalentLetters = new HashSet<LETTER>();
				equivalentLetters.add(letter);
				map.put(letter.toString(), equivalentLetters);
			} else {
				Set<LETTER> equivalentLetters = map.get(letter.toString());
				equivalentLetters.add(letter);
				map.put(letter.toString(), equivalentLetters); // needed? Will through exception?
			}
		}
	}

	/*
	 * Counts the number of letters of the original alphabet (of type String) that were matched to objects of type 
	 * LETTER in the new alphabet (reused letters), and those that were not matched to any object (removed letters).
	 * These two numbers are printed to the provided log.
	 * This function should only be used for debugging purposes.
	 */
	private static final <LETTER> void countReusedAndRemovedLetters(final VpAlphabet<String> orgAlphabet,
			final HashMap<String, Set<LETTER>> map, final ILogger logger) {
		int removedLetters = 0;
		int reusedLetters = 0;
		Set<String> letters = new HashSet<String>();
		letters.addAll(orgAlphabet.getInternalAlphabet());
		letters.addAll(orgAlphabet.getReturnAlphabet());
		letters.addAll(orgAlphabet.getCallAlphabet());
		for (String strLetter : letters) {
			if (!map.containsKey(strLetter)) {
				removedLetters++;
			} else {
				reusedLetters++;
			}
		}
		int totalLetters = removedLetters + reusedLetters;
		logger.info(
				"Reusing " + reusedLetters + "/" + totalLetters + " letters when constructing automaton from file.");
	}

	private static final <LETTER> void addTransitionsFromRawAutomaton(NestedWordAutomaton<LETTER, IPredicate> resAutomaton,
			final NestedWordAutomaton<String, String> rawAutomatonFromFile, 
			final HashMap<String, Set<LETTER>> mapStringToLetter,
			final HashMap<String, IPredicate> mapStringToFreshState, final Boolean debugOn, final ILogger logger) {
		int[] reusedAndRemoved = {0,0}; //Index 0 is for Reused, index 1 is for removed
		for (final IPredicate predicateState : resAutomaton.getStates()) {
			String stringState = predicateState.toString();
			addTransitionsFromState(rawAutomatonFromFile.callSuccessors(stringState), mapStringToLetter, mapStringToFreshState, resAutomaton, predicateState, reusedAndRemoved);
			addTransitionsFromState(rawAutomatonFromFile.internalSuccessors(stringState), mapStringToLetter, mapStringToFreshState, resAutomaton, predicateState, reusedAndRemoved);
			addTransitionsFromState(rawAutomatonFromFile.returnSuccessors(stringState), mapStringToLetter, mapStringToFreshState, resAutomaton, predicateState, reusedAndRemoved);
		}
		int totalTransitions = reusedAndRemoved[0]+reusedAndRemoved[1];
		if (debugOn) {
			logger.info("Reusing " + reusedAndRemoved[0] + "/" + totalTransitions
					+ " transitions when constructing automaton from file.");
		}
	}
	
	private static final <LETTER, E extends IOutgoingTransitionlet<String, String>> void addTransitionsFromState(
			Iterable<E> transitionsIterator,HashMap<String, Set<LETTER>> mapStringToLetter,
			HashMap<String, IPredicate> mapStringToFreshState, NestedWordAutomaton<LETTER, IPredicate> resAutomaton, 
			IPredicate predicateState, int[] reusedAndRemovedTransitions) {
		for (E transition : transitionsIterator) {
			String transitionLetter = transition.getLetter();
			String transitionSuccString = transition.getSucc();
			String transitionHeirPredString = "";
			if (transition instanceof OutgoingReturnTransition<?,?>) {
				transitionHeirPredString = ((OutgoingReturnTransition<String,String>)transition).getHierPred();
			}
			if (mapStringToLetter.containsKey(transitionLetter)) {
				IPredicate succState = mapStringToFreshState.get(transitionSuccString);
				IPredicate heirPredState = null;
				if (transition instanceof OutgoingReturnTransition<?,?>) {
					heirPredState = mapStringToFreshState.get(transitionHeirPredString);
				}
				for (LETTER letter : mapStringToLetter.get(transitionLetter)) {
					if (transition instanceof OutgoingReturnTransition<?,?>) {
						resAutomaton.addReturnTransition(predicateState, heirPredState, letter, succState);
					} else if (transition instanceof OutgoingCallTransition<?,?>) {
						resAutomaton.addCallTransition(predicateState, letter, succState);
					} else if (transition instanceof OutgoingInternalTransition<?,?>) {
						resAutomaton.addInternalTransition(predicateState, letter, succState);
					}
				}
				reusedAndRemovedTransitions[0]++;
			} else {
				reusedAndRemovedTransitions[1]++;
			}
		}
	}

	private IPredicate parsePredicate(final PredicateParsingWrapperScript ppws, final PredicateUnifier pu, final String rawString) {
		final Term termString = removeSerialNumber(rawString);
		final Term term;
		try {
			term = TermParseUtils.parseTerm(ppws, rawString);
		} catch (final SMTLIBException ex) {
			if (ex.getMessage().startsWith("Undeclared function symbol (")) {
				throw new UnsupportedOperationException("Automaton probably uses unknown variables. We should think how we can continue in this case.");
			}
			throw ex;
		}
		return pu.getOrConstructPredicate(term);
	}

	private Term removeSerialNumber(final String rawString) {
		// TODO implement this
		return null;
	}
	
}