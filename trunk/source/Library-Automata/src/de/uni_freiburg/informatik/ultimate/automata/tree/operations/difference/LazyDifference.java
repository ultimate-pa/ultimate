package de.uni_freiburg.informatik.ultimate.automata.tree.operations.difference;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.DummySemanticReducerFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISemanticReducerFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.StringRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.Determinize;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.util.CombinatoricsUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class LazyDifference<LETTER extends IRankedLetter, STATE>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>>
		implements IOperation<LETTER, STATE, IStateFactory<STATE>> {

	/**
	 * The first operand for the difference operation.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mFirstOperand;
	/**
	 * The resulting tree automaton after computing the difference.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mResult;
	/**
	 * The second operand for the difference operation.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mSecondOperand;

	/***
	 * Sink state
	 */
	private final STATE mSink;

	/***
	 * Cache for pair intersections
	 */
	private NestedMap2<STATE, STATE, STATE> mCache;

	/***
	 * Reducer for semantically redundant states
	 */
	private final ISemanticReducerFactory<STATE, LETTER> mReducer;

	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> LazyDifference(
			final AutomataLibraryServices services, final SF factory,
			final ITreeAutomatonBU<LETTER, STATE> firstOperand, final ITreeAutomatonBU<LETTER, STATE> secondOperand,
			final ISemanticReducerFactory<STATE, LETTER> reducer) throws AutomataOperationCanceledException {

		super(services);

		this.mFirstOperand = new Determinize<>(services, factory, firstOperand).getResult();
		this.mSecondOperand = new Determinize<>(services, factory, secondOperand).getResult();

		mReducer = reducer;
		mSink = factory.createSinkStateContent();
		this.mCache = new NestedMap2<>();
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug(startMessage());
		}

		this.mResult = computeDifference(factory);

		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug(exitMessage());
		}
	}

	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> LazyDifference(
			final AutomataLibraryServices services, final SF factory,
			final ITreeAutomatonBU<LETTER, STATE> firstOperand, final ITreeAutomatonBU<LETTER, STATE> secondOperand)
					throws AutomataOperationCanceledException {
		this(services, factory, firstOperand, secondOperand,
				(factory instanceof ISemanticReducerFactory) ? (ISemanticReducerFactory<STATE, LETTER>) factory
				: new DummySemanticReducerFactory<>());
	}

	private <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>>
		boolean getAllDestinations(
			final SF fac, final List<Collection<Pair<STATE, STATE>>> combinationValues,
			final Map<STATE, Set<STATE>> successors, final TreeAutomatonRule<LETTER, STATE> rule,
			final Set<TreeAutomatonRule<LETTER, STATE>> newRules) {

		boolean newReached = false;
		assert combinationValues.size() == rule.getArity() && rule.getArity() == rule.getLetter().getRank();
		for (final List<Pair<STATE, STATE>> srcState : CombinatoricsUtils.getCombinations(combinationValues)) {

			final List<STATE> first = new ArrayList<>();
			final List<STATE> second = new ArrayList<>();
			final List<STATE> newSource = new ArrayList<>();
			for (final Pair<STATE, STATE> p : srcState) {
				first.add(p.getFirst());
				second.add(p.getSecond());
				newSource.add(intersectPair(fac, p.getFirst(), p.getSecond()));
			}
			for (final STATE firstSucc : mFirstOperand.getSuccessors(first, rule.getLetter())) {
				if (successors.get(firstSucc) == null) {
					successors.put(firstSucc, new HashSet<>());
				}
				final Set<STATE> successorsSet = CombinatoricsUtils
						.iterateAll(mSecondOperand.getSuccessors(second, rule.getLetter()));
				if (successorsSet.isEmpty()) {
					newRules.add(new TreeAutomatonRule<LETTER, STATE>(rule.getLetter(), newSource,
							intersectPair(fac, firstSucc, mSink)));

					newReached |= !successors.get(firstSucc).contains(mSink);
					successors.get(firstSucc).add(mSink);

				} else {

					for (final STATE secondSucc : successorsSet) {
						newRules.add(new TreeAutomatonRule<LETTER, STATE>(rule.getLetter(), newSource,
								intersectPair(fac, firstSucc, secondSucc)));
						newReached |= !successors.get(firstSucc).contains(secondSucc);
						successors.get(firstSucc).add(secondSucc);
					}
				}
			}
		}
		return newReached;
	}

	private <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>>
		ITreeAutomatonBU<LETTER, STATE> computeDifference(
			final SF fac) {

		// Map of all states from t1 to the states from t2 that are derived as a
		// pair
		final Map<STATE, Set<STATE>> successors = new HashMap<>();

		final Set<TreeAutomatonRule<LETTER, STATE>> newRules = new HashSet<>();

		boolean newReached;
		do {
			newReached = false;
			for (final List<STATE> src : mFirstOperand.getSourceCombinations()) {
				for (final TreeAutomatonRule<LETTER, STATE> rule : mFirstOperand.getSuccessors(src)) {
					// f(a, y) -> x : f(b, z) -> w
					if (!successors.keySet().containsAll(rule.getSource())) {
						assert !rule.getSource().isEmpty();
						continue;
					}
					// a, y are all visited so we can derive x
					final List<Collection<Pair<STATE, STATE>>> combinations = new LinkedList<>();
					for (final STATE first : rule.getSource()) {
						final Set<Pair<STATE, STATE>> s = new HashSet<>();
						for (final STATE second : successors.get(first)) {
							// all derived pairs (a, b)
							s.add(new Pair<STATE, STATE>(first, second));
						}
						s.add(new Pair<STATE, STATE>(first, mSink));
						combinations.add(s);
					}
					newReached |= getAllDestinations(fac, combinations, successors, rule, newRules);
				}
			}
		} while (newReached);

		final NestedMap2<List<STATE>, LETTER, Set<STATE>> strongRules = new NestedMap2<>();
		for (final TreeAutomatonRule<LETTER, STATE> rule : newRules) {
			if (strongRules.get(rule.getSource(), rule.getLetter()) == null) {
				strongRules.put(rule.getSource(), rule.getLetter(), new HashSet<>());
			}
			strongRules.get(rule.getSource(), rule.getLetter()).add(rule.getDest());
		}
		newRules.clear();
		for (final Triple<List<STATE>, LETTER, Set<STATE>> triple : strongRules.entrySet()) {
			for (final STATE destination : mReducer.filter(triple.getThird())) {
				newRules.add(new TreeAutomatonRule<LETTER, STATE>(triple.getSecond(), triple.getFirst(), destination));
			}
		}
		final TreeAutomatonBU<LETTER, STATE> result = new TreeAutomatonBU<>();
		result.extendAlphabet(mFirstOperand.getAlphabet());
		result.extendAlphabet(mSecondOperand.getAlphabet());

		for (final TreeAutomatonRule<LETTER, STATE> rule : newRules) {
			result.addRule(rule);
		}

		for (final STATE s1 : mFirstOperand.getStates()) {
			// TODO(mostafa): Add state pair to result only if the pair already
			// exists (reachable)
			for (final STATE s2 : mSecondOperand.getStates()) {
				result.addState(intersectPair(fac, s1, s2));
				if (mFirstOperand.isFinalState(s1) && !mSecondOperand.isFinalState(s2)) {
					result.addFinalState(intersectPair(fac, s1, s2));
				}
			}
			assert !mSecondOperand.isFinalState(mSink);
			result.addState(intersectPair(fac, s1, mSink));
			if (mFirstOperand.isFinalState(s1)) {
				result.addFinalState(intersectPair(fac, s1, mSink));
			}
		}

		return result;
	}

	private <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>>
		STATE intersectPair(
			final SF factory, final STATE s1, final STATE s2) {

		STATE res = mCache.get(s1, s2);
		if (res == null) {
			res = factory.intersection(s1, s2);
			mCache.put(s1, s2, res);
		}
		return res;
	}

	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

	public static void main(final String[] args) throws AutomataOperationCanceledException {

		final Set<Integer> s1 = new HashSet<Integer>();
		s1.add(2);
		s1.add(3);
		s1.add(5);
		final Set<Integer> s2 = new HashSet<Integer>();
		s2.add(1);
		s2.add(10);
		s2.add(100);
		final List<Collection<Integer>> rr = Arrays.asList(new Set[] { s1, s2 });
		System.out.println(s1);
		System.out.println(s2);
		System.out.println(CombinatoricsUtils.getCombinations(rr));

		final StringFactory factory = new StringFactory();
		final TreeAutomatonBU<StringRankedLetter, String> ones = new TreeAutomatonBU<>();
		final String NUM = "Num", LIST = "List";
		ones.addRule(new TreeAutomatonRule<StringRankedLetter, String>(new StringRankedLetter("cons", 2),
				Arrays.asList(new String[] { NUM, LIST }), LIST));
		ones.addRule(new TreeAutomatonRule<StringRankedLetter, String>(new StringRankedLetter("nil", 0),
				Arrays.asList(new String[] {}), LIST));
		ones.addRule(new TreeAutomatonRule<StringRankedLetter, String>(new StringRankedLetter("0", 0),
				Arrays.asList(new String[] {}), NUM));
		ones.addRule(new TreeAutomatonRule<StringRankedLetter, String>(new StringRankedLetter("succ", 1),
				Arrays.asList(new String[] { NUM }), NUM));
		ones.addFinalState(LIST);

		final TreeAutomatonBU<StringRankedLetter, String> bin = new TreeAutomatonBU<>();
		bin.addRule(new TreeAutomatonRule<StringRankedLetter, String>(new StringRankedLetter("cons", 2),
				Arrays.asList(new String[] { NUM, LIST }), LIST));
		bin.addRule(new TreeAutomatonRule<StringRankedLetter, String>(new StringRankedLetter("nil", 0),
				Arrays.asList(new String[] {}), LIST));
		bin.addRule(new TreeAutomatonRule<StringRankedLetter, String>(new StringRankedLetter("0", 0),
				Arrays.asList(new String[] {}), NUM));
		bin.addRule(new TreeAutomatonRule<StringRankedLetter, String>(new StringRankedLetter("1", 0),
				Arrays.asList(new String[] {}), NUM));
		bin.addFinalState(LIST);

		System.out.println(ones);
		System.out.println(bin);

		final AutomataLibraryServices services = new AutomataLibraryServices(new ToolchainStorage());

		final Difference<StringRankedLetter, String> d1 = new Difference<>(services, factory, ones, bin);
		final LazyDifference<StringRankedLetter, String> d2 = new LazyDifference<>(services, factory, ones, bin);

		final boolean equiv = new IsEquivalent<StringRankedLetter, String>(services, factory, d1.getResult(), d2.getResult())
				.getResult();
		System.out.println(equiv);

		System.out.println(new LazyDifference<>(services, factory, ones, bin).getResult());
	}
}
