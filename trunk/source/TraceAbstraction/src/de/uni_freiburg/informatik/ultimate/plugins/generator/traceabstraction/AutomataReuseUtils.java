package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
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
			for (final LETTER letter : (abstractionAlphabet.getCallAlphabet())) {
				if (!mapStringToLetter.containsKey(letter.toString())) {
					final Set<LETTER> equivalentLetters = new HashSet<LETTER>();
					equivalentLetters.add(letter);
					mapStringToLetter.put(letter.toString(), equivalentLetters);
				} else {
					final Set<LETTER> equivalentLetters = mapStringToLetter.get(letter.toString());
					equivalentLetters.add(letter);
					mapStringToLetter.put(letter.toString(), equivalentLetters); //needed? Will through exception?
				}
			}
			for (final LETTER letter : (abstractionAlphabet.getInternalAlphabet())) {
				if (!mapStringToLetter.containsKey(letter.toString())) {
					final Set<LETTER> equivalentLetters = new HashSet<LETTER>();
					equivalentLetters.add(letter);
					mapStringToLetter.put(letter.toString(), equivalentLetters);
				} else {
					final Set<LETTER> equivalentLetters = mapStringToLetter.get(letter.toString());
					equivalentLetters.add(letter);
					mapStringToLetter.put(letter.toString(), equivalentLetters); //needed? Will through exception?
				}
			}
			for (final LETTER letter : (abstractionAlphabet.getReturnAlphabet())) {
				if (!mapStringToLetter.containsKey(letter.toString())) {
					final Set<LETTER> equivalentLetters = new HashSet<LETTER>();
					equivalentLetters.add(letter);
					mapStringToLetter.put(letter.toString(), equivalentLetters);
				} else {
					final Set<LETTER> equivalentLetters = mapStringToLetter.get(letter.toString());
					equivalentLetters.add(letter);
					mapStringToLetter.put(letter.toString(), equivalentLetters); //needed? Will through exception?
				}
			}
			if (debugOn) {
				// Create Debug information for letters
				int removedLetters = 0;
				int reusedLetters = 0;
				for (final String strLetter : rawAutomatonFromFile.getVpAlphabet().getCallAlphabet()) {
					if (!mapStringToLetter.containsKey(strLetter)) {
						removedLetters++;
					} else {
						reusedLetters++;
					}
				}
				for (final String strLetter : rawAutomatonFromFile.getVpAlphabet().getInternalAlphabet()) {
					if (!mapStringToLetter.containsKey(strLetter)) {
						removedLetters++;
					} else {
						reusedLetters++;
					}
				}
				for (final String strLetter : rawAutomatonFromFile.getVpAlphabet().getReturnAlphabet()) {
					if (!mapStringToLetter.containsKey(strLetter)) {
						removedLetters++;
					} else {
						reusedLetters++;
					}
				}
				final int totalLetters = removedLetters + reusedLetters;
				logger.info("Reusing " + reusedLetters + "/" + totalLetters
						+ " letters when constructing automaton from file.");
			}
			// Create empty automaton with same alphabet
			final NestedWordAutomaton<LETTER, IPredicate> resAutomaton = new NestedWordAutomaton<>(
					new AutomataLibraryServices(services), abstractionAlphabet, predicateFactoryInterpolantAutomata);
			// Add states
			final Set<String> statesOfRawAutomaton = rawAutomatonFromFile.getStates();
			final HashMap<String, IPredicate> mapStringToFreshState = new HashMap<>();
			for (final String stringState : statesOfRawAutomaton) {
				final IPredicate predicateState = predicateFactory.newDebugPredicate(stringState);
				mapStringToFreshState.put(stringState, predicateState);
				final boolean isInitial = rawAutomatonFromFile.isInitial(stringState);
				final boolean isFinal = rawAutomatonFromFile.isFinal(stringState);
				resAutomaton.addState(isInitial, isFinal, predicateState);
			}
			// Add transitions
			int removedTransitions = 0;
			int reusedTransitions = 0;
			for (final IPredicate predicateState : resAutomaton.getStates()) {
				final String stringState = predicateState.toString();
				for (final OutgoingCallTransition<String, String> callTransition : rawAutomatonFromFile
						.callSuccessors(stringState)) {
					final String transitionLetter = callTransition.getLetter();
					final String transitionSuccString = callTransition.getSucc();
					if (mapStringToLetter.containsKey(transitionLetter)) {
						final IPredicate succState = mapStringToFreshState.get(transitionSuccString);
						for (final LETTER letter : mapStringToLetter.get(transitionLetter)) {
							resAutomaton.addCallTransition(predicateState, letter, succState);
						}
						reusedTransitions++;
					} else {
						removedTransitions++;
					}
				}
				for (final OutgoingInternalTransition<String, String> internalTransition : rawAutomatonFromFile
						.internalSuccessors(stringState)) {
					final String transitionLetter = internalTransition.getLetter();
					final String transitionSuccString = internalTransition.getSucc();
					if (mapStringToLetter.containsKey(transitionLetter)) {
						final IPredicate succState = mapStringToFreshState.get(transitionSuccString);
						for (final LETTER letter : mapStringToLetter.get(transitionLetter)) {
							resAutomaton.addInternalTransition(predicateState, letter, succState);
						}
						reusedTransitions++;
					} else {
						removedTransitions++;
					}
				}
				for (final OutgoingReturnTransition<String, String> returnTransition : rawAutomatonFromFile
						.returnSuccessors(stringState)) {
					final String transitionLetter = returnTransition.getLetter();
					final String transitionSuccString = returnTransition.getSucc();
					final String transitionHeirPredString = returnTransition.getHierPred();
					if (mapStringToLetter.containsKey(transitionLetter)) {
						final IPredicate succState = mapStringToFreshState.get(transitionSuccString);
						final IPredicate heirPredState = mapStringToFreshState.get(transitionHeirPredString);
						for (final LETTER letter : mapStringToLetter.get(transitionLetter)) {
							resAutomaton.addReturnTransition(predicateState, heirPredState, letter, succState);
						}
						reusedTransitions++;
					} else {
						removedTransitions++;
					}
				}
			}
			final int totalTransitions = removedTransitions + reusedTransitions;
			if (debugOn) {
				logger.info("Reusing " + reusedTransitions + "/" + totalTransitions
						+ " transitions when constructing automaton from file.");
			}
			// Add new automaton to list
			res.add(resAutomaton);
		}

		return res;
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