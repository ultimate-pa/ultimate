package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public class PreNestedWord {
	private final int[] mSymbols;
	private final List<Integer> mPendingCalls;
	private final List<Integer> mPendingReturns;
	private final List<Loop> mLoops;
	private final Map<Integer, Integer> mInternal;
	private final ILogger mLogger;

	public PreNestedWord(final ILogger logger, final List<Integer> symbols, final List<Integer> pendingCalls,
			final List<Integer> pendingReturns, final Map<Integer, Integer> internal, final List<Loop> loops) {
		mLogger = logger;
		mPendingCalls = pendingCalls;
		mPendingReturns = pendingReturns;
		mLoops = loops;
		mInternal = internal;
		// Java still sucks because you have to do this.
		mSymbols = new int[symbols.size()];
		IntStream.range(0, mSymbols.length).forEach(i -> mSymbols[i] = symbols.get(i));
		/*
		 * mNestingRelation = new int[mSymbols.length]; IntStream.range(0, mSymbols.length).forEach(i -> { mSymbols[i] =
		 * symbols.get(i); if (pendingCalls.contains(i)) { mNestingRelation[i] = NestedWord.PLUS_INFINITY; } else if
		 * (pendingReturns.contains(i)) { mNestingRelation[i] = NestedWord.MINUS_INFINITY; } else if
		 * (internal.containsKey(i)) { mNestingRelation[i] = internal.get(i); mNestingRelation[internal.get(i)] = i; }
		 * else if (!internal.containsValue(i)) { mNestingRelation[i] = NestedWord.INTERNAL_POSITION; } });
		 */
	}

	/*
	 * public static NestedWord<Integer> getIntNestedWord(){
	 *
	 * }
	 */
	private List<Integer> expand(final List<Loop> loops) {
		final List<Integer> result = new ArrayList<>();
		expand(loops, result, 0, mSymbols.length);
		return result;
	}

	private void expand(final List<Loop> loops, final List<Integer> result, int start, final int end) {
		for (final Loop loop : loops) {
			for (int i = start; i < loop.mStart; i++)
				result.add(mSymbols[i]);
			final List<Integer> intermediate = new ArrayList<>();
			expand(loop.mNested, intermediate, loop.mStart, loop.mEnd);
			for (int j = 0; j < loop.mReps; j++)
				result.addAll(intermediate);
			start = loop.mEnd;
		}
		for (int i = start; i < end; i++)
			result.add(mSymbols[i]);
	}

	private IPredicate newTruePredicate(final PredicateFactory predicateFactory, final ManagedScript script) {
		return predicateFactory.newPredicate(script.getScript().term("true"));
	}

	public <LETTER> INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getAutomaton(final IUltimateServiceProvider services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> automaton,
			final IEmptyStackStateFactory<IPredicate> taContentFactory, final PredicateFactory predicateFactory,
			final ManagedScript script) {

		final Set<LETTER> internalAlphabet = automaton.getVpAlphabet().getInternalAlphabet();
		final Set<LETTER> callAlphabet = automaton.getVpAlphabet().getCallAlphabet();
		final Set<LETTER> returnAlphabet = automaton.getVpAlphabet().getReturnAlphabet();
		final Map<Integer, LETTER> internalAlphabetMap =
				internalAlphabet.stream().collect(Collectors.toMap(Object::hashCode, x -> x));
		final Map<Integer, LETTER> callAlphabetMap =
				callAlphabet.stream().collect(Collectors.toMap(Object::hashCode, x -> x));
		final Map<Integer, LETTER> returnAlphabetMap =
				returnAlphabet.stream().collect(Collectors.toMap(Object::hashCode, x -> x));
		// final Map<Integer, LETTER> allAlphabetMap = new HashMap<>();
		// allAlphabetMap.putAll(internalAlphabetMap);
		// allAlphabetMap.putAll(callAlphabetMap);
		// allAlphabetMap.putAll(returnAlphabetMap);
		final NestedWordAutomaton<LETTER, IPredicate> nwa =
				new NestedWordAutomaton<>(new AutomataLibraryServices(services), automaton.getVpAlphabet(), taContentFactory);

		IPredicate previousState = newTruePredicate(predicateFactory, script);
		IPredicate previousHierarchyState = null;
		nwa.addState(true, false, previousState);

		final List<Integer> symbols = expand(mLoops);
		for (int i = 0; i < symbols.size(); i++) {
			final boolean isFinal = i >= symbols.size() - 1;
			final Integer symbolRef = symbols.get(i);
			final LETTER symbol;
			final IPredicate target = newTruePredicate(predicateFactory, script);
			nwa.addState(false, isFinal, target);

			if (callAlphabetMap.containsKey(symbolRef)) {
				symbol = callAlphabetMap.get(symbolRef);
				nwa.addCallTransition(previousState, symbol, target);
				previousHierarchyState = previousState;
			} else if (returnAlphabetMap.containsKey(symbolRef)) {
				symbol = returnAlphabetMap.get(symbolRef);
				nwa.addReturnTransition(previousState, previousHierarchyState, symbol, target);
			} else if (internalAlphabetMap.containsKey(symbolRef)) {
				symbol = internalAlphabetMap.get(symbolRef);
				nwa.addInternalTransition(previousState, symbol, target);
			}

			previousState = target;
		}

		/*
		 * NestedWord<LETTER> word = getNestedWord(automaton); mLogger.info("Client has chosen the word: " +
		 * word.toString()); for (int i = 0; i < mSymbols.length; i++) { final boolean isFinal = i >= mSymbols.length -
		 * 1; final LETTER symbol = word.getSymbol(i);
		 *
		 * IPredicate target = newTruePredicate(predicateFactory, script);
		 *
		 * nwa.addState(false, isFinal, target); if (word.isCallPosition(i)) { nwa.addCallTransition(previousState,
		 * symbol, target); previousHierarchyState = previousState; } else if (word.isReturnPosition(i)) {
		 * nwa.addReturnTransition(previousState, previousHierarchyState, symbol, target); } else if
		 * (word.isInternalPosition(i)) { nwa.addInternalTransition(previousState, symbol, target); }
		 *
		 * previousState = target; }
		 */

		return nwa;
	}

	public <LETTER> LETTER[] getWord(final INwaOutgoingLetterAndTransitionProvider<LETTER, ?> automaton) {
		final Set<LETTER> internalAlphabet = automaton.getVpAlphabet().getInternalAlphabet();
		final Set<LETTER> callAlphabet = automaton.getVpAlphabet().getCallAlphabet();
		final Set<LETTER> returnAlphabet = automaton.getVpAlphabet().getReturnAlphabet();
		final Map<Integer, LETTER> internalAlphabetMap =
				internalAlphabet.stream().collect(Collectors.toMap(Object::hashCode, x -> x));
		final Map<Integer, LETTER> callAlphabetMap =
				callAlphabet.stream().collect(Collectors.toMap(Object::hashCode, x -> x));
		final Map<Integer, LETTER> returnAlphabetMap =
				returnAlphabet.stream().collect(Collectors.toMap(Object::hashCode, x -> x));
		final Map<Integer, LETTER> allAlphabetMap = new HashMap<>();
		allAlphabetMap.putAll(internalAlphabetMap);
		allAlphabetMap.putAll(callAlphabetMap);
		allAlphabetMap.putAll(returnAlphabetMap);

		@SuppressWarnings("unchecked")
		final LETTER[] word = (LETTER[]) new Object[mSymbols.length];
		for (int i = 0; i < mSymbols.length; i++) {
			word[i] = allAlphabetMap.get(mSymbols[i]);
		}
		return word;
	}

	/*
	 * public <LETTER> NestedWord<LETTER> getNestedWord(final INestedWordAutomatonSimple<LETTER, ?> automaton) { return
	 * new NestedWord<>(getWord(automaton), mNestingRelation); }
	 */

	public static class Loop {
		public final int mStart;
		public final int mEnd;
		public final int mReps;
		public final ArrayList<Loop> mNested = new ArrayList<>();

		public Loop(final int start, final int end, final int reps) {
			mStart = start;
			mEnd = end;
			mReps = reps;
			if (end <= start)
				throw new IllegalStateException("Invalid loop: " + this);
		}

		private String thisAndOther(final String prefix, final Loop other) {
			return prefix + this + " and " + other;
		}

		public boolean isNestedChildOf(final Loop other) {
			assert !equalBounds(other) : thisAndOther("Equal loops: ", other);
			if (mStart >= other.mEnd)
				return false;
			if (mStart >= other.mStart) {
				assert mEnd <= other.mEnd : thisAndOther("Crossing Loops: ", other);
				return true;
			}
			assert mEnd <= other.mStart : thisAndOther(
					mEnd >= other.mEnd ? "checked parent loop late" : "Crossing Loops: ", other);
			return false;
		}

		public static Loop addLoop(final List<Loop> loops, final Loop child) {
			for (final Loop nested : loops) {
				if (child.isNestedChildOf(nested)) {
					return addLoop(nested.mNested, child);
				}
			}
			loops.add(child);
			return null;
		}

		public int ExpandedWordLength() {
			return mReps * (mEnd - mStart);
		}

		public boolean equalBounds(final Loop other) {
			return mStart == other.mStart && mEnd == other.mEnd;
		}

		@Override
		public String toString() {
			return "Loop [" + mStart + "-" + mEnd + "]x" + mReps + (mNested.isEmpty() ? "" : " nested:" + mNested);
		}
	}
}
