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
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.ReusingDeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
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

	protected final List<AbstractInterpolantAutomaton<LETTER>> mFloydHoareAutomataFromOtherErrorLocations;
	protected final List<NestedWordAutomaton<String, String>> mRawFloydHoareAutomataFromFile;
	protected List<ReuseAutomaton> mFloydHoareAutomataFromFile;

	protected final ReuseStatisticsGenerator mReuseStats;
	private boolean mStatsAlreadyAggregated = false;

	public ReuseCegarLoop(final String name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final List<AbstractInterpolantAutomaton<LETTER>> floydHoareAutomataFromOtherLocations,
			final List<NestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile) {
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

		// fill mRawFloydHoareAutomataFromFile
		mReuseStats.continueTime();

		for (final NestedWordAutomaton<String, String> rawAutomatonFromFile : mRawFloydHoareAutomataFromFile) {

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
			final ReuseAutomaton reuseAutomaton = new ReuseAutomaton(resAutomaton, abstractionAlphabet);

			// Add states
			final Set<String> statesOfRawAutomaton = rawAutomatonFromFile.getStates();
			final HashMap<String, IPredicate> mapStringToState = new HashMap<>();
			final HashMap<IPredicate, String> mapStateToString = new HashMap<>();
			int reusedStates = 0;
			int removedStates = 0;
			for (final String stringState : statesOfRawAutomaton) {
				final AtomicBoolean parsingResult = new AtomicBoolean(false);
				final IPredicate predicateState = getPredicateFromString(mPredicateFactory, stringState, mCsToolkit,
						mServices, parsingResult, mLogger, reuseAutomaton.getPredicateUnifier());
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
			final int totalStates = removedStates + reusedStates;
			assert totalStates == resAutomaton.size();
			mReuseStats.addReusedStates(reusedStates);
			mReuseStats.addTotalStates(totalStates);
			// Add transitions
			addTransitionsFromRawAutomaton(resAutomaton, rawAutomatonFromFile, mapStringToLetter, mapStringToState,
					mapStateToString);

			// Add capability for on-demand extension to automata from file.
			mFloydHoareAutomataFromFile.add(reuseAutomaton);
			mReuseStats.addAutomataFromFile(1);
		}

		mReuseStats.addAutomataFromPreviousErrorLocation(mFloydHoareAutomataFromOtherErrorLocations.size());
		mReuseStats.stopTime();
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

	private static final IPredicate getPredicateFromString(final PredicateFactory predicateFactory, final String str,
			final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services,
			final AtomicBoolean parsingSuccesful, final ILogger logger, final PredicateUnifier pu) {
		final PredicateParsingWrapperScript ppws = new PredicateParsingWrapperScript(csToolkit);
		IPredicate res = null;
		try {
			res = parsePredicate(ppws, pu, str, logger);
			parsingSuccesful.set(true);
		} catch (final UnsupportedOperationException ex) {
			res = predicateFactory.newDebugPredicate(str);
			parsingSuccesful.set(false);
		}
		return res;
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
			final NestedWordAutomaton<String, String> rawAutomatonFromFile,
			final Map<String, Set<LETTER>> mapStringToLetter, final Map<String, IPredicate> mapStringToState,
			final Map<IPredicate, String> mapStateToString) {
		final int[] reusedAndRemoved = { 0, 0 };
		// Index 0 is for Reused, index 1 is for removed
		for (final IPredicate predicateState : resAutomaton.getStates()) {
			final String stringState = mapStateToString.get(predicateState);
			addTransitionsFromState(rawAutomatonFromFile.callSuccessors(stringState), mapStringToLetter,
					mapStringToState, resAutomaton, predicateState, reusedAndRemoved);
			addTransitionsFromState(rawAutomatonFromFile.internalSuccessors(stringState), mapStringToLetter,
					mapStringToState, resAutomaton, predicateState, reusedAndRemoved);
			addTransitionsFromState(rawAutomatonFromFile.returnSuccessors(stringState), mapStringToLetter,
					mapStringToState, resAutomaton, predicateState, reusedAndRemoved);
		}
		final int totalTransitions = reusedAndRemoved[0] + reusedAndRemoved[1];
		mReuseStats.addReusedTransitions(reusedAndRemoved[0]);
		mReuseStats.addTotalTransitions(totalTransitions);
	}

	private final <E extends IOutgoingTransitionlet<String, String>> void addTransitionsFromState(
			final Iterable<E> transitionsIterator, final Map<String, Set<LETTER>> mapStringToLetter,
			final Map<String, IPredicate> mapStringToFreshState,
			final NestedWordAutomaton<LETTER, IPredicate> resAutomaton, final IPredicate predicateState,
			final int[] reusedAndRemovedTransitions) {
		for (final E transition : transitionsIterator) {
			final String transitionLetter = transition.getLetter();
			final String transitionSuccString = transition.getSucc();
			String transitionHeirPredString = "";
			if (transition instanceof OutgoingReturnTransition<?, ?>) {
				transitionHeirPredString = ((OutgoingReturnTransition<String, String>) transition).getHierPred();
			}
			if (mapStringToLetter.containsKey(transitionLetter)) {
				final IPredicate succState = mapStringToFreshState.get(transitionSuccString);
				IPredicate heirPredState = null;
				if (transition instanceof OutgoingReturnTransition<?, ?>) {
					heirPredState = mapStringToFreshState.get(transitionHeirPredString);
				}
				for (final LETTER letter : mapStringToLetter.get(transitionLetter)) {
					if (transition instanceof OutgoingReturnTransition<?, ?>) {
						resAutomaton.addReturnTransition(predicateState, heirPredState, letter, succState);
					} else if (transition instanceof OutgoingCallTransition<?, ?>) {
						resAutomaton.addCallTransition(predicateState, letter, succState);
					} else if (transition instanceof OutgoingInternalTransition<?, ?>) {
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
		final String termString = removeSerialNumber(rawString, logger);
		final Term term;
		try {
			term = TermParseUtils.parseTerm(ppws, termString);
		} catch (final SMTLIBException ex) {
			if (ex.getMessage().startsWith("Undeclared function symbol (")) {
				throw new UnsupportedOperationException(
						"Automaton probably uses unknown variables. We should think how we can continue in this case.");
			}
			throw ex;
		}
		return pu.getOrConstructPredicate(term);
	}

	private static String removeSerialNumber(final String rawString, final ILogger logger) {
		final String[] res = rawString.split("#", 2);
		if (res.length == 1) {
			logger.warn("String " + rawString + " doesn't have a # symbol in it. Kepping entire string.");
			return res[0];
		} else if (res.length == 2) {
			// res[0] is the serial number, res[1] is the string
			return res[1];
		} else {
			logger.warn("Unexpected result from String's split function. String parsing failed.");
			return null;
		}
	}

	private static void addToReturnCache(final IPredicate preLin, final IPredicate preHier, final IAction act,
			final IPredicate succ, final Validity result,
			final Map<IPredicate, NestedMap3<IAction, IPredicate, IPredicate, Validity>> returnCache) {
		NestedMap3<IAction, IPredicate, IPredicate, Validity> map = returnCache.get(preHier);
		if (map == null) {
			map = new NestedMap3<>();
			returnCache.put(preHier, map);
		}
		map.put(act, preLin, succ, result);
	}

	/**
	 * Container class that keeps predicate unifier, hoare triple checker and NWA together.
	 * 
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public final class ReuseAutomaton {
		private static final boolean ENHANCE = true;
		private static final boolean USE_EAGER_CACHING_HTC = false;

		private final PredicateUnifier mPredicateUnifier;
		private final NestedWordAutomaton<LETTER, IPredicate> mAutomaton;
		private final VpAlphabet<LETTER> mAbstractionAlphabet;

		private AbstractInterpolantAutomaton<LETTER> mEnhancedAutomaton;
		private IHoareTripleChecker mHtc;

		private ReuseAutomaton(final NestedWordAutomaton<LETTER, IPredicate> automaton,
				final VpAlphabet<LETTER> abstractionAlphabet) {
			mPredicateUnifier = new PredicateUnifier(mServices, mCsToolkit.getManagedScript(), mPredicateFactory,
					mCsToolkit.getSymbolTable(), SimplificationTechnique.SIMPLIFY_DDA,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
			mAutomaton = automaton;
			mAbstractionAlphabet = abstractionAlphabet;
		}

		public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getAutomaton() {
			if (ENHANCE) {
				return getEnhancedInterpolantAutomaton();
			}
			return mAutomaton;
		}

		public IHoareTripleChecker getHtc() {
			if (mHtc == null) {
				if (USE_EAGER_CACHING_HTC) {
					mHtc = constructHtcWithEagerCache(constructOldAlphabet());
				} else {
					mHtc = TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
							mPref.getHoareTripleChecks(), mCsToolkit, mPredicateUnifier);
				}
			}
			return mHtc;
		}

		private IHoareTripleChecker constructHtcWithEagerCache(final VpAlphabet<LETTER> oldAlphabet)
				throws AssertionError {
			final NestedMap3<IAction, IPredicate, IPredicate, Validity> initialInternalCache = new NestedMap3<>();
			final NestedMap3<IAction, IPredicate, IPredicate, Validity> initialCallCache = new NestedMap3<>();
			final Map<IPredicate, NestedMap3<IAction, IPredicate, IPredicate, Validity>> initialReturnCache =
					new HashMap<>();

			int cachedHoareTriples = 0;
			final Set<IPredicate> states = mAutomaton.getStates();
			for (final IPredicate state : states) {
				final Set<LETTER> unknownInternalSuccessors = DataStructureUtils
						.difference(oldAlphabet.getInternalAlphabet(), mAutomaton.lettersInternal(state));
				for (final LETTER succ : unknownInternalSuccessors) {
					for (final IPredicate succState : states) {
						initialInternalCache.put(succ, state, succState, Validity.UNKNOWN);
						cachedHoareTriples++;
					}
				}

				final Set<LETTER> unknownCallSuccessors =
						DataStructureUtils.difference(oldAlphabet.getCallAlphabet(), mAutomaton.lettersCall(state));
				for (final LETTER succ : unknownCallSuccessors) {
					for (final IPredicate succState : states) {
						initialCallCache.put(succ, state, succState, Validity.UNKNOWN);
						cachedHoareTriples++;
					}
				}
				final Set<LETTER> unknownReturnSuccessors =
						DataStructureUtils.difference(oldAlphabet.getReturnAlphabet(), mAutomaton.lettersReturn(state));
				for (final IPredicate hierState : states) {
					for (final LETTER succ : unknownReturnSuccessors) {
						for (final IPredicate succState : states) {
							addToReturnCache(state, hierState, succ, succState, Validity.UNKNOWN, initialReturnCache);
							cachedHoareTriples++;
						}
					}
				}

			}
			mLogger.warn("Cached " + cachedHoareTriples + " hoare triples");
			return TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
					mPref.getHoareTripleChecks(), mCsToolkit, mPredicateUnifier, initialInternalCache, initialCallCache,
					initialReturnCache);
		}

		private VpAlphabet<LETTER> constructOldAlphabet() {
			return new VpAlphabet<>(
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

		public PredicateUnifier getPredicateUnifier() {
			return mPredicateUnifier;
		}

		public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getEnhancedInterpolantAutomaton() {
			if (mEnhancedAutomaton == null) {
				if (USE_EAGER_CACHING_HTC) {
					mEnhancedAutomaton = constructInterpolantAutomatonForOnDemandEnhancement(mAutomaton,
							getPredicateUnifier(), getHtc(), InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION);
				} else {
					final VpAlphabet<LETTER> oldAlphabet = constructOldAlphabet();
					mEnhancedAutomaton = new ReusingDeterministicInterpolantAutomaton<>(mServices, mCsToolkit, getHtc(),
							mAutomaton, getPredicateUnifier(), false, false, oldAlphabet);
				}
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

		NONREUSE_ITERATIONS(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		AUTOMATA_FROM_FILE(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		AUTOMATA_FROM_PREV_ERROR_LOC(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

		REUSE_PREDICATE_UNIFIER(IStatisticsDataProvider.class, StatisticsType.STATISTICS_DATA_AGGREGATION,
				StatisticsType.KEY_BEFORE_DATA),

		REUSE_HTC(IStatisticsDataProvider.class, StatisticsType.STATISTICS_DATA_AGGREGATION,
				StatisticsType.KEY_BEFORE_DATA),

		REUSE_TIME(Integer.class, StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_TIME),;

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
