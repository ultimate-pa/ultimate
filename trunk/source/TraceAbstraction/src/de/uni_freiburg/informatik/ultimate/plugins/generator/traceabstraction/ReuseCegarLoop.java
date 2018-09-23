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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IEpsilonNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleCheckerMap;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EfficientIgnoringHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuseEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

/**
 * Subclass of {@link BasicCegarLoop} in which we initially subtract from the abstraction a set of given Floyd-Hoare
 * automata.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ReuseCegarLoop<LETTER extends IIcfgTransition<?>> extends BasicCegarLoop<LETTER> {

	public static boolean USE_AUTOMATA_WITH_UNMATCHED_PREDICATES = false;

	protected final List<Pair<AbstractInterpolantAutomaton<LETTER>, IPredicateUnifier>> mFloydHoareAutomataFromOtherErrorLocations;
	protected final List<INestedWordAutomaton<String, String>> mRawFloydHoareAutomataFromFile;
	protected List<ReuseAutomaton> mFloydHoareAutomataFromFile;

	protected final ReuseStatisticsGenerator mReuseStats;
	private boolean mStatsAlreadyAggregated = false;

	public ReuseCegarLoop(final DebugIdentifier name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final List<Pair<AbstractInterpolantAutomaton<LETTER>, IPredicateUnifier>> floydHoareAutomataFromOtherLocations,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation,
				services, storage);
		mFloydHoareAutomataFromOtherErrorLocations = floydHoareAutomataFromOtherLocations;
		mRawFloydHoareAutomataFromFile = rawFloydHoareAutomataFromFile;
		mFloydHoareAutomataFromFile = new ArrayList<>();
		mReuseStats = new ReuseStatisticsGenerator();
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		super.getInitialAbstraction();

		mLogger.info(
				"Constructing FH automata from " + mRawFloydHoareAutomataFromFile.size() + " parsed reuse automata");
		mReuseStats.continueTime();

		final PredicateParsingWrapperScript ppws = new PredicateParsingWrapperScript(mCsToolkit);

		for (final INestedWordAutomaton<String, String> rawAutomatonFromFile : mRawFloydHoareAutomataFromFile) {
			if (rawAutomatonFromFile.getFinalStates().isEmpty()) {
				throw new AssertionError("A Floyd-Hoare automaton without accepting states is useless.");
			}
			buildFloydHoareAutomaton(ppws, rawAutomatonFromFile);
		}

		mReuseStats.addAutomataFromPreviousErrorLocation(mFloydHoareAutomataFromOtherErrorLocations.size());
		mReuseStats.stopTime();
	}

	private void buildFloydHoareAutomaton(final PredicateParsingWrapperScript ppws,
			final INestedWordAutomaton<String, String> rawAutomatonFromFile) {
		// Create map from strings to all equivalent "new" letters (abstraction letters)
		final Map<String, Set<LETTER>> mapStringToLetter = new HashMap<>();
		final VpAlphabet<LETTER> abstractionAlphabet =
				((INestedWordAutomaton<LETTER, IPredicate>) mAbstraction).getVpAlphabet();
		addLettersToStringMap(mapStringToLetter, abstractionAlphabet.getCallAlphabet());
		addLettersToStringMap(mapStringToLetter, abstractionAlphabet.getInternalAlphabet());
		addLettersToStringMap(mapStringToLetter, abstractionAlphabet.getReturnAlphabet());
		// compute stats for letters
		countReusedAndRemovedLetters(rawAutomatonFromFile.getVpAlphabet(), mapStringToLetter);
		// Create empty automaton with same alphabet
		final NestedWordAutomaton<LETTER, IPredicate> resAutomaton = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), abstractionAlphabet, mPredicateFactoryInterpolantAutomata);
		final IPredicateUnifier predicateUnifier = new PredicateUnifier(mLogger, mServices,
				mCsToolkit.getManagedScript(), mPredicateFactory, mCsToolkit.getSymbolTable(),
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final boolean implicationInformationProvided = rawAutomatonFromFile instanceof IEpsilonNestedWordAutomaton;
		final Pair<HashRelation<String, String>, HashRelation<String, String>> impliesExpliesStringRelations;
		if (implicationInformationProvided) {
			final IEpsilonNestedWordAutomaton<String, String> rawEpsilon =
					(IEpsilonNestedWordAutomaton<String, String>) rawAutomatonFromFile;
			impliesExpliesStringRelations = constructImpliesExpliesStrings(rawEpsilon);
		} else {
			impliesExpliesStringRelations = null;
		}

		// Add states
		final Set<String> statesOfRawAutomaton = rawAutomatonFromFile.getStates();
		final HashMap<String, Term> mapStringToTerm = new HashMap<>();
		final HashMap<Term, String> mapTermToString = new HashMap<>();
		for (final String stringState : statesOfRawAutomaton) {
			final Term term = parseTerm(ppws, stringState);
			if (term != null) {
				mapStringToTerm.put(stringState, term);
				mapTermToString.put(term, stringState);
			}
		}
		final int reusedStates = mapTermToString.size();
		final int removedStates = statesOfRawAutomaton.size() - reusedStates;

		final HashMap<String, IPredicate> mapStringToState = new HashMap<>();
		final HashMap<IPredicate, String> mapStateToString = new HashMap<>();
		{
			// add 'true' predicate
			final IPredicate predicate = predicateUnifier.getTruePredicate();
			final String string = mapTermToString.get(predicate.getFormula());
			addState(rawAutomatonFromFile, resAutomaton, mapStringToState, mapStateToString, predicate, string);
		}
		{
			// add 'false' predicate
			final IPredicate predicate = predicateUnifier.getFalsePredicate();
			final String string = mapTermToString.get(predicate.getFormula());
			addState(rawAutomatonFromFile, resAutomaton, mapStringToState, mapStateToString, predicate, string);
		}

		// add other predicates
		for (final Entry<Term, String> entry : mapTermToString.entrySet()) {
			final String string = entry.getValue();
			final Term term = entry.getKey();
			if (term == predicateUnifier.getTruePredicate().getFormula()
					|| term == predicateUnifier.getFalsePredicate().getFormula()) {
				continue;
			}

			final IPredicate predicate;
			if (implicationInformationProvided) {
				final Pair<HashMap<IPredicate, Validity>, HashMap<IPredicate, Validity>> impliesExpliesRelations =
						constructImpliesExpliesRelations(resAutomaton.getStates(), string, mapStateToString,
								impliesExpliesStringRelations);
				predicate = predicateUnifier.constructNewPredicate(term, impliesExpliesRelations.getFirst(),
						impliesExpliesRelations.getSecond());
			} else {
				predicate = predicateUnifier.getOrConstructPredicate(term);
			}

			addState(rawAutomatonFromFile, resAutomaton, mapStringToState, mapStateToString, predicate, string);
		}
		final int totalStates = removedStates + reusedStates;

		if (!USE_AUTOMATA_WITH_UNMATCHED_PREDICATES && removedStates > 0) {
			mReuseStats.addDroppedAutomata(1);
			return;
		}
		mReuseStats.addReusedStates(reusedStates);
		mReuseStats.addUselessPredicates(removedStates);
		mReuseStats.addTotalStates(totalStates);
		// Add transitions
		addTransitionsFromRawAutomaton(resAutomaton, rawAutomatonFromFile, mapStringToLetter, mapStringToState,
				mapStateToString);

		final ReuseAutomaton reuseAutomaton = new ReuseAutomaton(resAutomaton, abstractionAlphabet, predicateUnifier);
		// Add capability for on-demand extension to automata from file.
		mFloydHoareAutomataFromFile.add(reuseAutomaton);
		mReuseStats.addAutomataFromFile(1);
	}

	private void addState(final INestedWordAutomaton<String, String> rawAutomatonFromFile,
			final NestedWordAutomaton<LETTER, IPredicate> resAutomaton,
			final HashMap<String, IPredicate> mapStringToState, final HashMap<IPredicate, String> mapStateToString,
			final IPredicate predicate, final String string) {
		mapStringToState.put(string, predicate);
		mapStateToString.put(predicate, string);
		final boolean isInitial = rawAutomatonFromFile.isInitial(string);
		final boolean isFinal = rawAutomatonFromFile.isFinal(string);
		resAutomaton.addState(isInitial, isFinal, predicate);
	}

	private Pair<HashMap<IPredicate, Validity>, HashMap<IPredicate, Validity>> constructImpliesExpliesRelations(
			final Set<IPredicate> states, final String newStateString,
			final HashMap<IPredicate, String> mapStateToString,
			final Pair<HashRelation<String, String>, HashRelation<String, String>> result) {
		final HashRelation<String, String> impliedStrings = result.getFirst();
		final HashRelation<String, String> expliedStrings = result.getSecond();
		final HashMap<IPredicate, Validity> impliedPredicates = new HashMap<>();
		final HashMap<IPredicate, Validity> expliedPredicates = new HashMap<>();
		for (final IPredicate existingState : states) {
			final String existingStateString = mapStateToString.get(existingState);
			if (impliedStrings.containsPair(newStateString, existingStateString)) {
				impliedPredicates.put(existingState, Validity.VALID);
			} else {
				impliedPredicates.put(existingState, Validity.INVALID);
			}
			if (expliedStrings.containsPair(newStateString, existingStateString)) {
				expliedPredicates.put(existingState, Validity.VALID);
			} else {
				expliedPredicates.put(existingState, Validity.INVALID);
			}
		}
		return new Pair<>(impliedPredicates, expliedPredicates);
	}

	private Pair<HashRelation<String, String>, HashRelation<String, String>>
			constructImpliesExpliesStrings(final IEpsilonNestedWordAutomaton<String, String> rawEpsilon) {
		final HashRelation<String, String> implies = new HashRelation<>();
		final HashRelation<String, String> explies = new HashRelation<>();
		for (final String stringState : rawEpsilon.getStates()) {
			for (final String stringSucc : rawEpsilon.epsilonSuccessors(stringState)) {
				implies.addPair(stringState, stringSucc);
				explies.addPair(stringSucc, stringState);
			}
		}
		final Pair<HashRelation<String, String>, HashRelation<String, String>> result = new Pair<>(implies, explies);
		return result;
	}

	@Override
	public CegarLoopStatisticsGenerator getCegarLoopBenchmark() {
		// hacky: I know that this is only called during iterate, so we aggregate our benchmark in the cegar loop
		// benchmark right before that.
		assert !mStatsAlreadyAggregated;
		mStatsAlreadyAggregated = true;

		mFloydHoareAutomataFromFile.forEach(a -> {
			mReuseStats.reportHtcStats(a.getEdgeCheckerBenchmark());
			mReuseStats.reportPredicateUnifierStats(a.getPredicateUnifier().getPredicateUnifierBenchmark());
		});

		mCegarLoopBenchmark.addReuseStats(mReuseStats);
		return super.getCegarLoopBenchmark();
	}

	private static final <LETTER> void addLettersToStringMap(final Map<String, Set<LETTER>> map,
			final Set<LETTER> letters) {
		for (final LETTER letter : letters) {
			final String strLetter = letter.toString();
			final Set<LETTER> equivLetters = map.get(strLetter);
			if (equivLetters == null) {
				final Set<LETTER> newEquivLetters = new HashSet<>();
				newEquivLetters.add(letter);
				map.put(strLetter, newEquivLetters);
			} else {
				equivLetters.add(letter);
			}
		}
	}

	/**
	 * Counts the number of letters of the original alphabet (of type String) that were matched to objects of type
	 * LETTER in the new alphabet (reused letters), and those that were not matched to any object (removed letters).
	 * These two numbers are printed to the provided log. This function should only be used for debugging purposes.
	 */
	private final void countReusedAndRemovedLetters(final VpAlphabet<String> orgAlphabet,
			final Map<String, Set<LETTER>> map) {
		int removedLetters = 0;
		int reusedLetters = 0;
		final Set<String> letters = new HashSet<>();
		letters.addAll(orgAlphabet.getInternalAlphabet());
		letters.addAll(orgAlphabet.getReturnAlphabet());
		letters.addAll(orgAlphabet.getCallAlphabet());
		for (final String strLetter : letters) {
			if (map.containsKey(strLetter)) {
				reusedLetters++;
			} else {
				removedLetters++;
			}
		}
		final int totalLetters = removedLetters + reusedLetters;
		mReuseStats.addReusedLetters(reusedLetters);
		mReuseStats.addTotalLetters(totalLetters);
	}

	private final void addTransitionsFromRawAutomaton(final NestedWordAutomaton<LETTER, IPredicate> resAutomaton,
			final INestedWordAutomaton<String, String> rawAutomatonFromFile,
			final Map<String, Set<LETTER>> mapStringToLetter, final Map<String, IPredicate> mapStringToState,
			final Map<IPredicate, String> mapStateToString) {

		int removedTransitions = 0;
		int reusedTransitions = 0;
		final Set<IPredicate> availableStates = resAutomaton.getStates();

		for (final IPredicate predicateState : availableStates) {
			final String stringState = mapStateToString.get(predicateState);

			for (final OutgoingCallTransition<String, String> succ : rawAutomatonFromFile.callSuccessors(stringState)) {

				final Pair<Set<LETTER>, IPredicate> outTrans =
						filterTransitions(succ, mapStringToLetter, mapStringToState, availableStates);
				if (outTrans == null) {
					removedTransitions++;
					continue;
				}

				for (final LETTER letter : outTrans.getFirst()) {
					resAutomaton.addCallTransition(predicateState, letter, outTrans.getSecond());
					reusedTransitions++;
				}
			}

			for (final OutgoingInternalTransition<String, String> succ : rawAutomatonFromFile
					.internalSuccessors(stringState)) {

				final Pair<Set<LETTER>, IPredicate> outTrans =
						filterTransitions(succ, mapStringToLetter, mapStringToState, availableStates);
				if (outTrans == null) {
					removedTransitions++;
					continue;
				}

				for (final LETTER letter : outTrans.getFirst()) {
					resAutomaton.addInternalTransition(predicateState, letter, outTrans.getSecond());
					reusedTransitions++;
				}
			}

			for (final OutgoingReturnTransition<String, String> succ : rawAutomatonFromFile
					.returnSuccessors(stringState)) {

				final Pair<Set<LETTER>, IPredicate> outTrans =
						filterTransitions(succ, mapStringToLetter, mapStringToState, availableStates);
				if (outTrans == null) {
					removedTransitions++;
					continue;
				}

				final IPredicate heirPredState = mapStringToState.get(succ.getHierPred());
				if (!availableStates.contains(heirPredState)) {
					removedTransitions++;
					continue;
				}

				for (final LETTER letter : outTrans.getFirst()) {
					resAutomaton.addReturnTransition(predicateState, heirPredState, letter, outTrans.getSecond());
					reusedTransitions++;
				}
			}

		}
		final int totalTransitions = removedTransitions + reusedTransitions;
		mReuseStats.addReusedTransitions(reusedTransitions);
		mReuseStats.addTotalTransitions(totalTransitions);
	}

	private Pair<Set<LETTER>, IPredicate> filterTransitions(final IOutgoingTransitionlet<String, String> transition,
			final Map<String, Set<LETTER>> mapStringToLetter, final Map<String, IPredicate> mapStringToState,
			final Set<IPredicate> availableStates) {
		final Set<LETTER> letters = mapStringToLetter.get(transition.getLetter());
		if (letters == null) {
			// could not match the letter
			return null;
		}

		final String transitionSuccString = transition.getSucc();
		final IPredicate succState = mapStringToState.get(transitionSuccString);
		if (!availableStates.contains(succState)) {
			// could not match the successor state
			return null;
		}
		return new Pair<>(letters, succState);
	}

	private Term parseTerm(final PredicateParsingWrapperScript ppws, final String rawString) {
		final Term term;
		try {
			final String termString = removeSerialNumber(rawString);
			term = TermParseUtils.parseTerm(ppws, termString);
		} catch (final Exception ex) {
			mLogger.warn("Exception during parsing of " + rawString + ": " + ex.getMessage());
			return null;
		}
		return term;
	}

	private String removeSerialNumber(final String rawString) {
		final String[] res = rawString.split("#", 2);
		if (res.length == 1) {
			mLogger.warn("String " + rawString + " doesn't have a # symbol in it. Kepping entire string.");
			return res[0];
		} else if (res.length == 2) {
			// res[0] is the serial number, res[1] is the string
			return res[1];
		} else {
			mLogger.warn("Unexpected result from String's split function. String parsing failed.");
			throw new UnsupportedOperationException("String parsing failed");
		}
	}

	/**
	 * Container class that keeps predicate unifier, hoare triple checker and NWA together.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public final class ReuseAutomaton {
		private final boolean mUseEnhancement;

		private final IPredicateUnifier mPredicateUnifier;
		private final NestedWordAutomaton<LETTER, IPredicate> mAutomaton;
		private final VpAlphabet<LETTER> mAbstractionAlphabet;

		private AbstractInterpolantAutomaton<LETTER> mEnhancedAutomaton;
		private IHoareTripleChecker mHtc;

		private ReuseAutomaton(final NestedWordAutomaton<LETTER, IPredicate> automaton,
				final VpAlphabet<LETTER> abstractionAlphabet, final IPredicateUnifier predicateUnifier) {

			mPredicateUnifier = predicateUnifier;
			mAutomaton = automaton;
			mAbstractionAlphabet = abstractionAlphabet;
			mUseEnhancement = mPref.getFloydHoareAutomataReuseEnhancement() != FloydHoareAutomataReuseEnhancement.NONE;
		}

		public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getAutomaton() {
			if (mUseEnhancement) {
				return getEnhancedInterpolantAutomaton();
			}
			return mAutomaton;
		}

		public IHoareTripleChecker getHtc() {
			if (!mUseEnhancement) {
				throw new UnsupportedOperationException("You should not need a Hoare Triple Checker in this mode");
			}
			if (mHtc == null) {
				mHtc = constructHtc();
			}
			return mHtc;
		}

		private IHoareTripleChecker constructHtc() {
			final FloydHoareAutomataReuseEnhancement mode = mPref.getFloydHoareAutomataReuseEnhancement();
			switch (mode) {
			case AS_USUAL:
				// TODO: check with Matthias if this HTC is the one we want: it uses the ProtectiveHoareTripleChecker,
				// thus never checking intricate predicates. The other ones do not use the ProtectiveHoareTripleChecker.
				return TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
						mPref.getHoareTripleChecks(), mCsToolkit, getPredicateUnifier());
			case ONLY_NEW_LETTERS:
				return constructEfficientIgnoringHtc(false);
			case ONLY_NEW_LETTERS_SOLVER:
				return constructEfficientIgnoringHtc(true);
			case NONE:
			default:
				throw new UnsupportedOperationException("Unknown / illegal mode: " + mode);

			}
		}

		private IHoareTripleChecker constructEfficientIgnoringHtc(final boolean allowSdForProtectedActions)
				throws AssertionError {
			final IHoareTripleChecker smtHtc =
					TraceAbstractionUtils.constructSmtHoareTripleChecker(mPref.getHoareTripleChecks(), mCsToolkit);
			final EfficientIgnoringHoareTripleChecker eiHtc = new EfficientIgnoringHoareTripleChecker(smtHtc,
					mCsToolkit, getPredicateUnifier(), constructOldAlphabet(), allowSdForProtectedActions);
			return new CachingHoareTripleCheckerMap(mServices, eiHtc, getPredicateUnifier());
		}

		private Set<LETTER> constructOldAlphabet() {
			return DataStructureUtils.union(
					DataStructureUtils.intersection(mAbstractionAlphabet.getInternalAlphabet(),
							mAutomaton.getVpAlphabet().getInternalAlphabet()),
					DataStructureUtils.intersection(mAbstractionAlphabet.getCallAlphabet(),
							mAutomaton.getVpAlphabet().getCallAlphabet()),
					DataStructureUtils.intersection(mAbstractionAlphabet.getReturnAlphabet(),
							mAutomaton.getVpAlphabet().getReturnAlphabet()));
		}

		public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
			if (mHtc == null) {
				return new HoareTripleCheckerStatisticsGenerator();
			}
			return mHtc.getEdgeCheckerBenchmark();
		}

		public IPredicateUnifier getPredicateUnifier() {
			return mPredicateUnifier;
		}

		private INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getEnhancedInterpolantAutomaton() {
			if (mEnhancedAutomaton == null) {
				mEnhancedAutomaton = constructInterpolantAutomatonForOnDemandEnhancement(mAutomaton,
						getPredicateUnifier(), getHtc(), InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION);
			}
			return mEnhancedAutomaton;
		}
	}

	public enum ReuseStatisticsDefinitions implements IStatisticsElement {

		REUSED_STATES(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		TOTAL_STATES(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		REUSED_LETTERS(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		TOTAL_LETTERS(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		REUSED_TRANSITIONS(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		TOTAL_TRANSITIONS(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		BEFORE_DIFF_TRANS(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		AFTER_DIFF_TRANS(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		BEFORE_ACCEPT_TRANS(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		AFTER_ACCEPT_TRANS(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		USELESS_PREDICATES(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		NONREUSE_ITERATIONS(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		AUTOMATA_FROM_FILE(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		AUTOMATA_FROM_PREV_ERROR_LOC(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		REUSE_PREDICATE_UNIFIER(IStatisticsDataProvider.class, StatisticsType.STATISTICS_DATA_AGGREGATION,
				StatisticsType.KEY_BEFORE_DATA),

		REUSE_HTC(IStatisticsDataProvider.class, StatisticsType.STATISTICS_DATA_AGGREGATION,
				StatisticsType.KEY_BEFORE_DATA),

		REUSE_TIME(Integer.class, StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

		DROPPED_AUTOMATA(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),;

		private final Class<?> mClazz;
		private final Function<Object, Function<Object, Object>> mAggr;
		private final Function<String, Function<Object, String>> mPrettyprinter;

		ReuseStatisticsDefinitions(final Class<?> clazz, final Function<Object, Function<Object, Object>> aggr,
				final Function<String, Function<Object, String>> prettyprinter) {
			mClazz = clazz;
			mAggr = aggr;
			mPrettyprinter = prettyprinter;
		}

		@Override
		public Object aggregate(final Object o1, final Object o2) {
			return mAggr.apply(o1).apply(o2);
		}

		@Override
		public String prettyprint(final Object o) {
			return mPrettyprinter.apply(CoreUtil.getUpperToCamelCase(name())).apply(o);
		}

		@Override
		public Class<?> getDataType() {
			return mClazz;
		}
	}

	public static final class ReuseStatisticsType extends StatisticsType<ReuseStatisticsDefinitions> {

		private static final ReuseStatisticsType INSTANCE = new ReuseStatisticsType();

		public ReuseStatisticsType() {
			super(ReuseStatisticsDefinitions.class);
		}

		public static ReuseStatisticsType getInstance() {
			return INSTANCE;
		}
	}

	public static final class ReuseStatisticsGenerator implements IStatisticsDataProvider {

		private final StatisticsData mPredicateUnifierStats;
		private final Benchmark mTime;
		private final StatisticsData mHtcStats;

		private boolean mRunning = false;
		private int mAutomataFromFile;
		private int mAutomataFromPreviousErrorLocation;
		private int mReusedStates;
		private int mTotalStates;
		private int mReusedLetters;
		private int mTotalLetters;
		private int mReusedTransitions;
		private int mTotalTransitions;
		private int mNonReuseIterations;
		private int mBeforeDiffTransitions;
		private int mAfterDiffTransitions;
		private int mBeforeAcceptanceTransitions;
		private int mAfterAcceptanceTransitions;
		private int mUselessPredicates;
		private int mDroppedAutomata;

		public ReuseStatisticsGenerator() {
			mPredicateUnifierStats = new StatisticsData();
			mHtcStats = new StatisticsData();
			mTime = new Benchmark();
			mTime.register(String.valueOf(ReuseStatisticsDefinitions.REUSE_TIME));
			mAutomataFromFile = 0;
			mAutomataFromPreviousErrorLocation = 0;
			mReusedStates = 0;
			mTotalStates = 0;
			mReusedLetters = 0;
			mTotalLetters = 0;
			mReusedTransitions = 0;
			mTotalTransitions = 0;
			mNonReuseIterations = 0;
			mBeforeDiffTransitions = 0;
			mAfterDiffTransitions = 0;
			mBeforeAcceptanceTransitions = 0;
			mAfterAcceptanceTransitions = 0;
			mUselessPredicates = 0;
			mDroppedAutomata = 0;
		}

		public void reportPredicateUnifierStats(final IStatisticsDataProvider stats) {
			mPredicateUnifierStats.aggregateBenchmarkData(stats);
		}

		public void reportHtcStats(final IStatisticsDataProvider stats) {
			mHtcStats.aggregateBenchmarkData(stats);
		}

		public void addAutomataFromFile(final int value) {
			mAutomataFromFile = mAutomataFromFile + value;
		}

		public void addAutomataFromPreviousErrorLocation(final int value) {
			mAutomataFromPreviousErrorLocation = mAutomataFromPreviousErrorLocation + value;
		}

		public void addTotalStates(final int value) {
			mTotalStates = mTotalStates + value;
		}

		public void addReusedStates(final int value) {
			mReusedStates = mReusedStates + value;
		}

		public void addTotalLetters(final int value) {
			mTotalLetters = mTotalLetters + value;
		}

		public void addReusedLetters(final int value) {
			mReusedLetters = mReusedLetters + value;
		}

		public void addTotalTransitions(final int value) {
			mTotalTransitions = mTotalTransitions + value;
		}

		public void addReusedTransitions(final int value) {
			mReusedTransitions = mReusedTransitions + value;
		}

		public void addBeforeDiffTransitions(final int value) {
			mBeforeDiffTransitions = mBeforeDiffTransitions + value;
		}

		public void addAfterDiffTransitions(final int value) {
			mAfterDiffTransitions = mAfterDiffTransitions + value;
		}

		public void addBeforeAcceptanceTransitions(final int value) {
			mBeforeAcceptanceTransitions = mBeforeAcceptanceTransitions + value;
		}

		public void addAfterAcceptanceTransitions(final int value) {
			mAfterAcceptanceTransitions = mAfterAcceptanceTransitions + value;
		}

		public void addUselessPredicates(final int value) {
			mUselessPredicates = mUselessPredicates + value;
		}

		public void addDroppedAutomata(final int value) {
			mDroppedAutomata = mDroppedAutomata + value;
		}

		public void announceNextNonreuseIteration() {
			mNonReuseIterations++;
		}

		public long getTime() {
			return (long) mTime.getElapsedTime(String.valueOf(ReuseStatisticsDefinitions.REUSE_TIME),
					TimeUnit.NANOSECONDS);
		}

		public void continueTime() {
			assert !mRunning : "Timing already running";
			mRunning = true;
			mTime.unpause(String.valueOf(ReuseStatisticsDefinitions.REUSE_TIME));
		}

		public void stopTime() {
			assert mRunning : "Timing not running";
			mRunning = false;
			mTime.pause(String.valueOf(ReuseStatisticsDefinitions.REUSE_TIME));
		}

		@Override
		public Collection<String> getKeys() {
			return ReuseStatisticsType.getInstance().getKeys();
		}

		@Override
		public Object getValue(final String key) {
			final ReuseStatisticsDefinitions keyEnum = Enum.valueOf(ReuseStatisticsDefinitions.class, key);
			switch (keyEnum) {
			case REUSE_PREDICATE_UNIFIER:
				return mPredicateUnifierStats;
			case REUSE_TIME:
				return getTime();
			case NONREUSE_ITERATIONS:
				return mNonReuseIterations;
			case REUSE_HTC:
				return mHtcStats;
			case AUTOMATA_FROM_FILE:
				return mAutomataFromFile;
			case AUTOMATA_FROM_PREV_ERROR_LOC:
				return mAutomataFromPreviousErrorLocation;
			case REUSED_STATES:
				return mReusedStates;
			case TOTAL_STATES:
				return mTotalStates;
			case REUSED_LETTERS:
				return mReusedLetters;
			case REUSED_TRANSITIONS:
				return mReusedTransitions;
			case TOTAL_LETTERS:
				return mTotalLetters;
			case TOTAL_TRANSITIONS:
				return mTotalTransitions;
			case AFTER_DIFF_TRANS:
				return mAfterDiffTransitions;
			case BEFORE_DIFF_TRANS:
				return mBeforeDiffTransitions;
			case AFTER_ACCEPT_TRANS:
				return mAfterAcceptanceTransitions;
			case BEFORE_ACCEPT_TRANS:
				return mBeforeAcceptanceTransitions;
			case USELESS_PREDICATES:
				return mUselessPredicates;
			case DROPPED_AUTOMATA:
				return mDroppedAutomata;
			default:
				throw new UnsupportedOperationException("Unknown key: " + keyEnum);
			}
		}

		@Override
		public IStatisticsType getBenchmarkType() {
			return ReuseStatisticsType.getInstance();
		}
	}

}
