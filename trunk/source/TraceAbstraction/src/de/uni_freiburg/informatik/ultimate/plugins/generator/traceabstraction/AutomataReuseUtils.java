package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;

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
	
		final Boolean debugOn = true;
		final List<INestedWordAutomaton<LETTER, IPredicate>> res = new ArrayList<INestedWordAutomaton<LETTER, IPredicate>>();

		for (final NestedWordAutomaton<String, String> rawAutomatonFromFile : rawFloydHoareAutomataFromFile) {
			
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
			final HashMap<String, IPredicate> mapStringToState = new HashMap<>();
			final HashMap<IPredicate, String> mapStateToString = new HashMap<>();
			int reusedStates = 0;
			int removedStates = 0;
			for (final String stringState : statesOfRawAutomaton) {
				AtomicBoolean parsingResult = new AtomicBoolean(false);
				final IPredicate predicateState = getPredicateFromString(predicateFactory, stringState, csToolkit, services, parsingResult, logger);
				if (parsingResult.get()) {
					reusedStates++;
				} else {
					removedStates++;
				}
				mapStringToState.put(stringState, predicateState);
				mapStateToString.put(predicateState, stringState);
				final boolean isInitial = rawAutomatonFromFile.isInitial(stringState);
				final boolean isFinal = rawAutomatonFromFile.isFinal(stringState);
				resAutomaton.addState(isInitial, isFinal, predicateState);
			}
			int totalStates = removedStates + reusedStates;
			assert(totalStates==resAutomaton.size());
			logger.info(
					"Reusing " + reusedStates + "/" + totalStates + " states when constructing automaton from file.");
			// Add transitions
			addTransitionsFromRawAutomaton(resAutomaton, rawAutomatonFromFile, mapStringToLetter, mapStringToState, 
					mapStateToString, debugOn, logger);
			// Add new automaton to list
			res.add(resAutomaton);
		}

		return res;
	}

	private static final IPredicate getPredicateFromString(final PredicateFactory predicateFactory, final String str,
			final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services, AtomicBoolean parsingSuccesful,
			ILogger logger) {
		final PredicateParsingWrapperScript ppws = new PredicateParsingWrapperScript(csToolkit);
		final PredicateUnifier pu = new PredicateUnifier(services, csToolkit.getManagedScript(), predicateFactory,
				csToolkit.getSymbolTable(), SimplificationTechnique.SIMPLIFY_DDA,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		IPredicate res = null;
		try {
			res = parsePredicate(ppws, pu, str, logger);
			parsingSuccesful.set(true);
		} catch (final UnsupportedOperationException ex) {
			res = predicateFactory.newDebugPredicate(str);
			parsingSuccesful.set(false);
		}
		return res;
		//return predicateFactory.newDebugPredicate(str);
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
			final HashMap<String, IPredicate> mapStringToState, final HashMap<IPredicate, String> mapStateToString,
			final Boolean debugOn, final ILogger logger) {
		int[] reusedAndRemoved = {0,0}; //Index 0 is for Reused, index 1 is for removed
		for (final IPredicate predicateState : resAutomaton.getStates()) {
			String stringState = mapStateToString.get(predicateState);
			addTransitionsFromState(rawAutomatonFromFile.callSuccessors(stringState), mapStringToLetter, mapStringToState, resAutomaton, predicateState, reusedAndRemoved);
			addTransitionsFromState(rawAutomatonFromFile.internalSuccessors(stringState), mapStringToLetter, mapStringToState, resAutomaton, predicateState, reusedAndRemoved);
			addTransitionsFromState(rawAutomatonFromFile.returnSuccessors(stringState), mapStringToLetter, mapStringToState, resAutomaton, predicateState, reusedAndRemoved);
		}
		int totalTransitions = reusedAndRemoved[0]+reusedAndRemoved[1];
		if (debugOn) {
			logger.info("Reusing " + reusedAndRemoved[0] + "/" + totalTransitions
					+ " transitions when constructing automaton from file.");
		}
	}
	
	private static final <LETTER, E extends IOutgoingTransitionlet<String, String>> void addTransitionsFromState(
			final Iterable<E> transitionsIterator, final HashMap<String, Set<LETTER>> mapStringToLetter,
			final HashMap<String, IPredicate> mapStringToFreshState, NestedWordAutomaton<LETTER, IPredicate> resAutomaton, 
			final IPredicate predicateState, int[] reusedAndRemovedTransitions) {
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

	private static IPredicate parsePredicate(final PredicateParsingWrapperScript ppws, final PredicateUnifier pu, 
			final String rawString, final ILogger logger) {
		final String termString = removeSerialNumber(rawString,logger);
		final Term term;
		try {
			term = TermParseUtils.parseTerm(ppws, termString);
		} catch (final SMTLIBException ex) {
			if (ex.getMessage().startsWith("Undeclared function symbol (")) {
				throw new UnsupportedOperationException("Automaton probably uses unknown variables. We should think how we can continue in this case.");
			}
			throw ex;
		}
		return pu.getOrConstructPredicate(term);
	}

	private static String removeSerialNumber(final String rawString, final ILogger logger) {
		String[] res = rawString.split("#",2);
		if (res.length == 1){
			logger.warn("String "+rawString+" doesn't have a # symbol in it. Kepping entire string.");
			return res[0];
		} else if (res.length == 2) { //res[0] is the serial number, res[1] is the string
			return res[1];
		} else {
			logger.warn("Unexpected result from String's split function. String parsing failed.");
			return null;
		}
	}
	
}