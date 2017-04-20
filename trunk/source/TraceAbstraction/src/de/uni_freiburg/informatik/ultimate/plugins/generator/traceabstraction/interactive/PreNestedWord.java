package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public class PreNestedWord {
	final int[] mSymbols;
	final int[] mNestingRelation;
	final List<Integer> mPendingCalls;
	final List<Integer> mPendingReturns;
	final Map<Integer, Integer> mInternal;
	final ILogger mLogger;

	public static class Loop {
		public Loop(int start, int end, int reps) {
			mStart = start;
			mEnd = end;
			mReps = reps;
			if (end <= start)
				throw new IllegalStateException("Invalid loop: " + this);
		}

		private String thisAndOther(String prefix, Loop other) {
			return prefix + this + " and " + other;
		}

		public boolean isNestedChildOf(Loop other) {
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

		public static Loop addLoop(List<Loop> loops, Loop child) {
			for (Loop nested : loops) {
				if (child.isNestedChildOf(nested)) {
					return addLoop(nested.mNested, child);
				}
			}
			loops.add(child);
			return null;
		}

		public boolean equalBounds(Loop other) {
			return mStart == other.mStart && mEnd == other.mEnd;
		}

		@Override
		public String toString() {
			return "Loop [" + mStart + "-" + mEnd + "]x" + mReps + (mNested.isEmpty() ? "" : " nested:" + mNested);
		}

		public final int mStart;
		public final int mEnd;
		public final int mReps;
		public final ArrayList<Loop> mNested = new ArrayList<>();
	}

	public PreNestedWord(ILogger logger, List<Integer> symbols, List<Integer> pendingCalls,
			List<Integer> pendingReturns, Map<Integer, Integer> internal, List<Loop> loops) {
		mLogger = logger;
		mPendingCalls = pendingCalls;
		mPendingReturns = pendingReturns;
		mInternal = internal;
		// Java still sucks because you have to do this.
		mSymbols = new int[symbols.size()];
		mNestingRelation = new int[mSymbols.length];
		IntStream.range(0, mSymbols.length).forEach(i -> {
			mSymbols[i] = symbols.get(i);
			if (pendingCalls.contains(i)) {
				mNestingRelation[i] = NestedWord.PLUS_INFINITY;
			} else if (pendingReturns.contains(i)) {
				mNestingRelation[i] = NestedWord.MINUS_INFINITY;
			} else if (internal.containsKey(i)) {
				mNestingRelation[i] = internal.get(i);
				mNestingRelation[internal.get(i)] = i;
			} else if (!internal.containsValue(i)) {
				mNestingRelation[i] = NestedWord.INTERNAL_POSITION;
			}
		});
	}

	/*
	 * public static NestedWord<Integer> getIntNestedWord(){
	 * 
	 * }
	 */

	private IPredicate newTruePredicate(PredicateFactory predicateFactory, ManagedScript script) {
		return predicateFactory.newPredicate(script.getScript().term("true"));
	}

	public <LETTER> INestedWordAutomatonSimple<LETTER, IPredicate> getAutomaton(final IUltimateServiceProvider services,
			final INestedWordAutomatonSimple<LETTER, IPredicate> automaton,
			final IStateFactory<IPredicate> taContentFactory, PredicateFactory predicateFactory, ManagedScript script) {
		// allAlphabetMap.get(key)
		// SmtUtils.

		final NestedWordAutomaton<LETTER, IPredicate> nwa =
				new NestedWordAutomaton<>(new AutomataLibraryServices(services), automaton.getAlphabet(),
						automaton.getCallAlphabet(), automaton.getReturnAlphabet(), taContentFactory);

		// IPredicate previousState = predicateUnifier.getTruePredicate();
		IPredicate previousState = newTruePredicate(predicateFactory, script);
		IPredicate previousHierarchyState = null;
		nwa.addState(true, false, previousState);

		NestedWord<LETTER> word = getNestedWord(automaton);
		mLogger.info("Client has chosen the word: " + word.toString());
		for (int i = 0; i < mSymbols.length; i++) {
			final boolean isFinal = i >= mSymbols.length - 1;
			final LETTER symbol = word.getSymbol(i);

			IPredicate target = newTruePredicate(predicateFactory, script);

			nwa.addState(false, isFinal, target);
			if (word.isCallPosition(i)) {
				nwa.addCallTransition(previousState, symbol, target);
				previousHierarchyState = previousState;
			} else if (word.isReturnPosition(i)) {
				nwa.addReturnTransition(previousState, previousHierarchyState, symbol, target);
			} else if (word.isInternalPosition(i)) {
				nwa.addInternalTransition(previousState, symbol, target);
			}

			previousState = target;
		}

		return nwa;
	}

	public <LETTER> LETTER[] getWord(final INestedWordAutomatonSimple<LETTER, ?> automaton) {
		final Set<LETTER> internalAlphabet = automaton.getAlphabet();
		final Set<LETTER> callAlphabet = automaton.getCallAlphabet();
		final Set<LETTER> returnAlphabet = automaton.getReturnAlphabet();
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

	public <LETTER> NestedWord<LETTER> getNestedWord(final INestedWordAutomatonSimple<LETTER, ?> automaton) {
		return new NestedWord<>(getWord(automaton), mNestingRelation);
	}
}
