/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AutomataScriptInterpreter plug-in.
 *
 * The ULTIMATE AutomataScriptInterpreter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AutomataScriptInterpreter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptInterpreter plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptInterpreter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptInterpreter plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 *
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.alternating.BooleanExpression;
import de.uni_freiburg.informatik.ultimate.automata.counting.CountingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.CountingAutomatonDataStructure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.EpsilonNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.StringRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.TestFileInterpreter.LoggerSeverity;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AbstractNestedwordAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AlternatingAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitionsAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.CountingAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.EpsilonNestedwordAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedwordAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.PetriNetAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.PetriNetTransitionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.RankedAlphabetEntryAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TreeAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TreeAutomatonRankedAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TreeAutomatonTransitionAST;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Responsible for interpretation of automata definitions.
 *
 * @author musab@informatik.uni-freiburg.de
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class AutomataDefinitionInterpreter {
	private static final String UNDEFINED_PLACE = "undefined place: ";
	private static final String LINE_SEPARATOR = System.getProperty("line.separator");
	private static final String EXCEPTION_THROWN = "Exception thrown";

	/**
	 * Enable/disable unification of objects in the automata.
	 * <p>
	 * The parser creates fresh objects every time it reads a string, even if
	 * two strings are identical. With unification activated we make sure that
	 * there is only one object per string in the automaton (e.g., all
	 * transitions to some state {@code q} point to the same object).
	 * <p>
	 * TODO Christian 2017-03-19 Currently only nested word automata are
	 * unified.
	 */
	private static final boolean UNIFY_OBJECTS = false;

	/**
	 * A map from automaton name to automaton object, which contains for each
	 * automaton, that was defined in the automata definitions an entry.
	 */
	private final Map<String, Object> mAutomata;
	/**
	 * Contains the location of current interpreting automaton.
	 */
	private ILocation mErrorLocation;
	private final IMessagePrinter mMessagePrinter;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final NestedMap2<String, Integer, StringRankedLetter> mLetterToRank;

	/**
	 * @param printer
	 *            Message printer.
	 * @param logger
	 *            logger
	 * @param services
	 *            Ultimate services
	 */
	public AutomataDefinitionInterpreter(final IMessagePrinter printer, final ILogger logger,
			final IUltimateServiceProvider services) {
		mAutomata = new HashMap<>();
		mMessagePrinter = printer;
		mLogger = logger;
		mServices = services;
		mLetterToRank = new NestedMap2<>();
	}

	/**
	 * @param automata
	 *            The automata definitions.
	 */
	public void interpret(final AutomataDefinitionsAST automata) {
		final List<? extends AtsASTNode> children = automata.getListOfAutomataDefinitions();
		for (final AtsASTNode n : children) {
			try {
				if (n instanceof NestedwordAutomatonAST) {
					interpret((NestedwordAutomatonAST) n);
				} else if (n instanceof EpsilonNestedwordAutomatonAST) {
					interpret((EpsilonNestedwordAutomatonAST) n);
				} else if (n instanceof PetriNetAutomatonAST) {
					interpret((PetriNetAutomatonAST) n);
				} else if (n instanceof AlternatingAutomatonAST) {
					interpret((AlternatingAutomatonAST) n);
				} else if (n instanceof TreeAutomatonAST) {
					interpret((TreeAutomatonAST) n);
				} else if (n instanceof TreeAutomatonRankedAST) {
					interpret((TreeAutomatonRankedAST) n);
				} else if (n instanceof CountingAutomatonAST) {
					interpret((CountingAutomatonAST) n);
				} else {
					throw new AssertionError("unsupported kind of automaton " + n);
				}
			} catch (final Exception e) {
				mMessagePrinter.printMessage(Severity.ERROR, LoggerSeverity.DEBUG,
						e.getMessage() + LINE_SEPARATOR + e.getStackTrace(), EXCEPTION_THROWN, n);
			}
		}
	}

	/**
	 * @param astNode
	 *            AST node.
	 */
	public void interpret(final AlternatingAutomatonAST astNode) {
		mErrorLocation = astNode.getLocation();
		final HashSet<String> alphabet = new HashSet<>(astNode.getAlphabet());
		final AlternatingAutomaton<String, String> alternatingAutomaton = new AlternatingAutomaton<>(alphabet);
		// States
		final List<String> states = astNode.getStates();
		final List<String> finalStates = astNode.getFinalStates();
		for (final String state : states) {
			alternatingAutomaton.addState(state);
			if (finalStates.contains(state)) {
				alternatingAutomaton.setStateFinal(state);
			}
		}
		// Transitions
		for (final Entry<Pair<String, String>, Set<String>> entry : astNode.getTransitions().entrySet()) {
			final String expression = entry.getValue().iterator().next();
			final LinkedList<BooleanExpression> booleanExpressions = parseBooleanExpressions(alternatingAutomaton,
					expression);
			for (final BooleanExpression booleanExpression : booleanExpressions) {
				alternatingAutomaton.addTransition(entry.getKey().getSecond(), entry.getKey().getFirst(),
						booleanExpression);
			}
		}
		// Accepting Function
		final LinkedList<BooleanExpression> acceptingBooleanExpressions = parseBooleanExpressions(alternatingAutomaton,
				astNode.getAcceptingFunction());
		for (final BooleanExpression booleanExpression : acceptingBooleanExpressions) {
			alternatingAutomaton.addAcceptingConjunction(booleanExpression);
		}
		alternatingAutomaton.setReversed(astNode.isReversed());
		mAutomata.put(astNode.getName(), alternatingAutomaton);
	}

	/**
	 * @param astNode
	 *            AST node.
	 */
	public void interpret(final TreeAutomatonAST astNode) {
		mErrorLocation = astNode.getLocation();

		final TreeAutomatonBU<StringRankedLetter, String> treeAutomaton = new TreeAutomatonBU<>();

		for (final String s : astNode.getStates()) {
			treeAutomaton.addState(s);
		}

		// for (final String is : astNode.getInitialStates()) {
		// treeAutomaton.addInitialState(is);
		// }

		for (final String fs : astNode.getFinalStates()) {
			treeAutomaton.addFinalState(fs);
		}

		for (final TreeAutomatonTransitionAST trans : astNode.getTransitions()) {
			// if (trans.getSourceStates().isEmpty()) {
			// throw new UnsupportedOperationException("The TreeAutomaton format
			// with initial states "
			// + "(and implicit symbol ranks) does not allow nullary rules,
			// i.e.,"
			// + "rules where the source state list is empty");
			// }

			// determine the rank of the letter according to the rule's source
			// states
			final StringRankedLetter letter = getOrConstructStringRankedLetter(trans.getSymbol(),
					trans.getSourceStates().size());

			treeAutomaton.addRule(new TreeAutomatonRule<>(letter, trans.getSourceStates(), trans.getTargetState()));
		}

		for (final String ltr : astNode.getAlphabet()) {
			final Map<Integer, StringRankedLetter> letters = mLetterToRank.get(ltr);
			if (letters == null || letters.isEmpty()) {
				// letter occurs only in the alphabet, not in any rule --
				// assigning it rank -1
				treeAutomaton.addLetter(new StringRankedLetter(ltr, -1));
			} else {
				for (final Entry<Integer, StringRankedLetter> en : letters.entrySet()) {
					treeAutomaton.addLetter(en.getValue());
				}
			}
		}

		mAutomata.put(astNode.getName(), treeAutomaton);
	}

	private StringRankedLetter getStringRankedLetter(final String symbol, final int rank) {
		assert mLetterToRank.get(symbol, rank) != null;
		return mLetterToRank.get(symbol, rank);
	}

	private StringRankedLetter getOrConstructStringRankedLetter(final String symbol, final int letterRank) {
		final String letterString = symbol;
		// assert mLetterToRank.get(letterString) == null ||
		// mLetterToRank.get(letterString).getRank() == letterRank : "we don't
		// allow letter with more than one"
		// + "rank, right?";
		StringRankedLetter letter = mLetterToRank.get(letterString, letterRank);
		if (letter == null) {
			letter = new StringRankedLetter(letterString, letterRank);
			mLetterToRank.put(symbol, letterRank, letter);
		}
		return letter;
	}

	/**
	 * @param astNode
	 *            AST node.
	 */
	public void interpret(final TreeAutomatonRankedAST astNode) {
		mErrorLocation = astNode.getLocation();

		final TreeAutomatonBU<StringRankedLetter, String> treeAutomaton = new TreeAutomatonBU<>();
		final String nullaryString = "elim0arySymbol_";

		final List<RankedAlphabetEntryAST> ra = astNode.getRankedAlphabet();
		for (final RankedAlphabetEntryAST rae : ra) {
			for (final String ltr : rae.getAlphabet()) {
				treeAutomaton.addLetter(getOrConstructStringRankedLetter(ltr, Integer.parseInt(rae.getRank())));
				// if (Integer.parseInt(rae.getRank()) == 0) {
				// // our tree automata don't have 0-ary symbols right now
				// // (they use 1-ary, initial states, and adapted rules
				// instead)
				// // this converts 0-ary symbols accordingly
				// final String inState = nullaryString + ltr;
				// treeAutomaton.addState(inState);
				// treeAutomaton.addInitialState(inState);
				// }
			}
		}

		for (final String s : astNode.getStates()) {
			treeAutomaton.addState(s);
		}

		for (final String fs : astNode.getFinalStates()) {
			treeAutomaton.addFinalState(fs);
		}

		for (final TreeAutomatonTransitionAST trans : astNode.getTransitions()) {
			if (trans.getSourceStates().isEmpty()) {
				treeAutomaton.addRule(new TreeAutomatonRule<>(
						getStringRankedLetter(trans.getSymbol(), trans.getSourceStates().size()),
						Collections.singletonList(nullaryString + trans.getSymbol()), trans.getTargetState()));
			} else {
				treeAutomaton.addRule(new TreeAutomatonRule<>(
						getStringRankedLetter(trans.getSymbol(), trans.getSourceStates().size()),
						trans.getSourceStates(), trans.getTargetState()));
			}
		}
		mAutomata.put(astNode.getName(), treeAutomaton);
	}

	/**
	 * @param nwa
	 *            AST node.
	 */
	public void interpret(final NestedwordAutomatonAST nwa) {
		mErrorLocation = nwa.getLocation();

		final NestedWordAutomaton<String, String> result = constructNestedWordAutomaton(nwa, mServices);

		mAutomata.put(nwa.getName(), result);
	}

	private void interpret(final EpsilonNestedwordAutomatonAST nwa) {
		mErrorLocation = nwa.getLocation();

		final EpsilonNestedWordAutomaton<String, String, NestedWordAutomaton<String, String>> result = constructEpsilonNestedWordAutomaton(
				nwa, mServices);

		mAutomata.put(nwa.getName(), result);
	}

	public static EpsilonNestedWordAutomaton<String, String, NestedWordAutomaton<String, String>> constructEpsilonNestedWordAutomaton(
			final EpsilonNestedwordAutomatonAST enwa, final IUltimateServiceProvider services) {
		final NestedWordAutomaton<String, String> nwa = constructNestedWordAutomaton(enwa, services);
		final EpsilonNestedWordAutomaton<String, String, NestedWordAutomaton<String, String>> result = new EpsilonNestedWordAutomaton<String, String, NestedWordAutomaton<String, String>>(
				nwa, enwa.getEpsilonTransitions());
		return result;
	}

	public static NestedWordAutomaton<String, String> constructNestedWordAutomaton(
			final AbstractNestedwordAutomatonAST nwa, final IUltimateServiceProvider services) {
		{
			final String duplicateState = checkForDuplicate(nwa.getStates());
			if (duplicateState != null) {
				throw new IllegalArgumentException("State " + duplicateState + " contained twice in states.");
			}
		}
		{
			final String duplicateState = checkForDuplicate(nwa.getInitialStates());
			if (duplicateState != null) {
				throw new IllegalArgumentException("State " + duplicateState + " contained twice in initial states.");
			}
		}
		{
			final String duplicateState = checkForDuplicate(nwa.getFinalStates());
			if (duplicateState != null) {
				throw new IllegalArgumentException("State " + duplicateState + " contained twice in final states.");
			}
		}


		checkThatInitialAndFinalStatesExist(nwa);

		final Set<String> initStatesAsSet = new HashSet<>(nwa.getInitialStates());
		final Set<String> finalStatesAsSet = new HashSet<>(nwa.getFinalStates());

		// data structures for unification
		final Map<String, String> mUnifyLettersInternal;
		final Map<String, String> mUnifyLettersCall;
		final Map<String, String> mUnifyLettersReturn;
		final Map<String, String> mUnifyStates;
		if (UNIFY_OBJECTS) {
			mUnifyLettersInternal = new HashMap<>();
			mUnifyLettersCall = new HashMap<>();
			mUnifyLettersReturn = new HashMap<>();
			mUnifyStates = new HashMap<>();
		} else {
			mUnifyLettersInternal = null;
			mUnifyLettersCall = null;
			mUnifyLettersReturn = null;
			mUnifyStates = null;
		}

		// create automaton
		final Set<String> internalAlphabet = Collections.unmodifiableSet(new HashSet<>(nwa.getInternalAlphabet()));
		final Set<String> callAlphabet = Collections.unmodifiableSet(new HashSet<>(nwa.getCallAlphabet()));
		final Set<String> returnAlphabet = Collections.unmodifiableSet(new HashSet<>(nwa.getReturnAlphabet()));
		if (UNIFY_OBJECTS) {
			for (final String letter : nwa.getInternalAlphabet()) {
				mUnifyLettersInternal.put(letter, letter);
			}
			for (final String letter : nwa.getCallAlphabet()) {
				mUnifyLettersCall.put(letter, letter);
			}
			for (final String letter : nwa.getReturnAlphabet()) {
				mUnifyLettersReturn.put(letter, letter);
			}
		}

		final NestedWordAutomaton<String, String> nw = new NestedWordAutomaton<>(new AutomataLibraryServices(services),
				new VpAlphabet<String>(internalAlphabet, callAlphabet, returnAlphabet), new StringFactory());

		// add the states
		for (final String state : nwa.getStates()) {
			nw.addState(initStatesAsSet.contains(state), finalStatesAsSet.contains(state), state);
			if (UNIFY_OBJECTS) {
				mUnifyStates.put(state, state);
			}
		}

		// add the transitions
		for (final Entry<Pair<String, String>, Set<String>> entry : nwa.getInternalTransitions().entrySet()) {
			final String pred = unifyIfNeeded(entry.getKey().getFirst(), mUnifyStates);
			for (final String succRaw : entry.getValue()) {
				final String succ = unifyIfNeeded(succRaw, mUnifyStates);
				final String letter = unifyIfNeeded(entry.getKey().getSecond(), mUnifyLettersInternal);
				if (!internalAlphabet.contains(letter)) {
					throw new IllegalArgumentException("Letter " + letter + " not in internal alphabet");
				}
				nw.addInternalTransition(pred, letter, succ);
			}
		}

		for (final Entry<Pair<String, String>, Set<String>> entry : nwa.getCallTransitions().entrySet()) {
			final String pred = unifyIfNeeded(entry.getKey().getFirst(), mUnifyStates);
			for (final String succRaw : entry.getValue()) {
				final String succ = unifyIfNeeded(succRaw, mUnifyStates);
				final String letter = unifyIfNeeded(entry.getKey().getSecond(), mUnifyLettersCall);
				if (!callAlphabet.contains(letter)) {
					throw new IllegalArgumentException("Letter " + letter + " not in call alphabet");
				}
				nw.addCallTransition(pred, letter, succ);
			}
		}

		for (final String linPredRaw : nwa.getReturnTransitions().keySet()) {
			final String linPred = unifyIfNeeded(linPredRaw, mUnifyStates);
			for (final String hierPredRaw : nwa.getReturnTransitions().get(linPred).keySet()) {
				final String hierPred = unifyIfNeeded(hierPredRaw, mUnifyStates);
				for (final Entry<String, Set<String>> entry : nwa.getReturnTransitions().get(linPred).get(hierPred)
						.entrySet()) {
					final String letter = unifyIfNeeded(entry.getKey(), mUnifyLettersReturn);
					if (!returnAlphabet.contains(letter)) {
						throw new IllegalArgumentException("Letter " + letter + " not in return alphabet");
					}
					for (final String succRaw : entry.getValue()) {
						final String succ = unifyIfNeeded(succRaw, mUnifyStates);
						nw.addReturnTransition(linPred, hierPred, letter, succ);
					}
				}
			}
		}
		return nw;
	}

	private void interpret(final CountingAutomatonAST caAst) throws InterpreterException {
		final CountingAutomatonDataStructure<String, String> countingAutomatonDataStructure = CountingAutomataUtils
				.constructCountingAutomaton(mServices, caAst);
		final CountingAutomaton<String, String> ca = CountingAutomataUtils.translateDataStructureToAutomaton(mServices,
				countingAutomatonDataStructure);
		Objects.nonNull(ca);
		mAutomata.put(caAst.getName(), ca);
	}

	/**
	 *
	 * @return The first element that occurs twice in list, returns null if no such
	 *         element exists.
	 */
	public static <E> E checkForDuplicate(final List<E> list) {
		final Set<E> listAsSet = new HashSet<>();
		for (final E elem : list) {
			final boolean alreadycontained = listAsSet.add(elem);
			if (!alreadycontained) {
				return elem;
			}
		}
		return null;
	}

	/**
	 * Throw exception if initial state does not exists in set of states.
	 * Throw exception if finalstate does not exists in set of states.
	 */
	private static void checkThatInitialAndFinalStatesExist(final AbstractNestedwordAutomatonAST nwa) {
		final Set<String> allStates = new HashSet<>(nwa.getStates());
		final List<String> initStates = nwa.getInitialStates();
		for (final String init : initStates) {
			if (!allStates.contains(init)) {
				throw new IllegalArgumentException("Initial state " + init + " not in set of states");
			}
		}
		final List<String> finalStates = nwa.getFinalStates();
		for (final String fin : finalStates) {
			if (!allStates.contains(fin)) {
				throw new IllegalArgumentException("Final state " + fin + " not in set of states");
			}
		}
	}

	/**
	 * @param pna
	 *            AST node.
	 */
	public void interpret(final PetriNetAutomatonAST pna) {
		mErrorLocation = pna.getLocation();
		final BoundedPetriNet<String, String> net = new BoundedPetriNet<>(new AutomataLibraryServices(mServices),
				new HashSet<>(pna.getAlphabet()), false);
		final Map<String, String> name2places = new HashMap<>();

		// add the places
		for (final String p : pna.getPlaces()) {
			final boolean newlyAdded = net.addPlace(p, pna.getInitialMarkings().containsPlace(p),
					pna.getAcceptingPlaces().contains(p));
			if (!newlyAdded) {
				throw new AssertionError(
						"Petri net must not contain place twice: " + p);
			}
			name2places.put(p, p);
		}

		// add the transitions
		for (final PetriNetTransitionAST ptrans : pna.getTransitions()) {
			final Set<String> preds = new HashSet<>();
			for (final String pred : ptrans.getPreds()) {
				if (!name2places.containsKey(pred)) {
					throw new IllegalArgumentException(UNDEFINED_PLACE + pred);
				}
				preds.add(name2places.get(pred));
			}
			final Set<String> succs = new HashSet<>();
			for (final String succ : ptrans.getSuccs()) {
				if (!name2places.containsKey(succ)) {
					throw new IllegalArgumentException(UNDEFINED_PLACE + succ);
				}
				succs.add(name2places.get(succ));
			}
			net.addTransition(ptrans.getSymbol(), preds, succs);
		}

		mAutomata.put(pna.getName(), net);
	}

	private static String unifyIfNeeded(final String object, final Map<String, String> unifier) {
		if (!UNIFY_OBJECTS) {
			return object;
		}
		return unifier.get(object);
	}

	private static LinkedList<BooleanExpression> parseBooleanExpressions(
			final AlternatingAutomaton<String, String> alternatingAutomaton, final String expression) {
		final LinkedList<BooleanExpression> booleanExpressions = new LinkedList<>();
		if ("true".equals(expression)) {
			booleanExpressions.add(new BooleanExpression(new BitSet(), new BitSet()));
		} else if ("false".equals(expression)) {
			// Not supported yet
		} else {
			final String[] disjunctiveExpressions = expression.split("\\|");
			for (final String disjunctiveExpression : disjunctiveExpressions) {
				final String[] stateExpressions = disjunctiveExpression.split("&");
				final LinkedList<String> resultStates = new LinkedList<>();
				final LinkedList<String> negatedResultStates = new LinkedList<>();
				for (final String stateExpression : stateExpressions) {
					if (stateExpression.startsWith("~")) {
						negatedResultStates.add(stateExpression.substring(1));
					} else {
						resultStates.add(stateExpression);
					}
				}
				final BooleanExpression booleanExpression = alternatingAutomaton.generateCube(
						resultStates.toArray(new String[resultStates.size()]),
						negatedResultStates.toArray(new String[negatedResultStates.size()]));
				booleanExpressions.add(booleanExpression);
			}
		}
		return booleanExpressions;
	}

	public Map<String, Object> getAutomata() {
		return mAutomata;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("AutomataDefinitionInterpreter [");
		if (mAutomata != null) {
			builder.append("#AutomataDefinitions: ");
			builder.append(mAutomata.size());
		}
		builder.append("]");
		return builder.toString();
	}

	public ILocation getErrorLocation() {
		return mErrorLocation;
	}
}
