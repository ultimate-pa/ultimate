/*
 * Copyright (C) 2020 Leonard Fichtner
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Random;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;

/**
 * This class provides several heuristics for choosing MUSes or groups of MUSes for Interpolant generation.
 *
 * @author LeonardFichtner (leonard.fichtner@web.de)
 *
 */
public class Heuristics {

	private enum ResultOfComparison {
		MUS1 {
		},
		MUS2 {
		},
		EQUAL {
		}
	}

	/**
	 * Chooses a random MusContainer from the given ArrayList and returns it. Returns null if the given list is emtpy.
	 */
	public static MusContainer chooseRandomMus(final ArrayList<MusContainer> muses, final Random rnd) {
		if (muses.isEmpty()) {
			return null;
		}
		return muses.get(rnd.nextInt(muses.size()));
	}

	/**
	 * Chooses the the smallest Mus (in terms of cardinality) from the given ArrayList and returns its MusContainer. In
	 * case there are multiple such muses, this algorithm randomly chooses one of them. Returns null if the given list
	 * is empty. If termination is requested, this heuristic returns one of the best muses found until this point.
	 */
	public static MusContainer chooseSmallestMus(final ArrayList<MusContainer> muses, final Random rnd,
			final TerminationRequest request) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(
				findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsSmaller, request), rnd);
	}

	/**
	 * Chooses the biggest Mus (in terms of cardinality) from the given ArrayList and returns its MusContainer. In case
	 * there are multiple such muses, this algorithm randomly chooses one of them. Returns null if the given list is
	 * empty. If termination is requested, this heuristic returns one of the best muses found until this point.
	 */
	public static MusContainer chooseBiggestMus(final ArrayList<MusContainer> muses, final Random rnd,
			final TerminationRequest request) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(
				findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsBigger, request), rnd);
	}

	/**
	 * Chooses the Mus with the lowest Lexicographical order (in terms of indices of the contained constraints) from the
	 * given ArrayList and returns its MusContainer. Returns null if List is empty. If termination is requested, this
	 * heuristic returns one of the best muses found until this point.
	 */
	public static MusContainer chooseMusWithLowestLexicographicalOrder(final ArrayList<MusContainer> muses,
			final Random rnd, final TerminationRequest request) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(findBestMusesAccordingToGivenCriterion(muses,
				Heuristics::compareWhichMusHasLowerLexicographicalOrder, request), rnd);
	}

	/**
	 * Chooses the Mus with the highest Lexicographical order (in terms of indices of the contained constraints) from
	 * the given ArrayList and returns its MusContainer. Returns null if the given list is empty. If termination is
	 * requested, this heuristic returns one of the best muses found until this point.
	 */
	public static MusContainer chooseMusWithHighestLexicographicalOrder(final ArrayList<MusContainer> muses,
			final Random rnd, final TerminationRequest request) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(findBestMusesAccordingToGivenCriterion(muses,
				Heuristics::compareWhichMusHasHigherLexicographicalOrder, request), rnd);
	}

	/**
	 * Chooses the shallowest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm randomly chooses one of them. Shallow here means, that the first constraint of the mus has
	 * a low index. Returns null if the given list is empty. If termination is requested, this heuristic returns one of
	 * the best muses found until this point.
	 */
	public static MusContainer chooseShallowestMus(final ArrayList<MusContainer> muses, final Random rnd,
			final TerminationRequest request) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(
				findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsShallowerMus, request), rnd);
	}

	/**
	 * Chooses the deepest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm randomly chooses one of them. Deep here means, that the first constraint of the mus has a
	 * high index. Returns null if the given list is empty. If termination is requested, this heuristic returns one of
	 * the best muses found until this point.
	 */
	public static MusContainer chooseDeepestMus(final ArrayList<MusContainer> muses, final Random rnd,
			final TerminationRequest request) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(
				findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsDeeperMus, request), rnd);
	}

	/**
	 * Chooses the narrowest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm randomly chooses one of them. Narrow here means, that the difference between the highest
	 * index of a constraint in the mus and the lowest index of a constraint in the mus is small. Returns null if the
	 * given list is empty. If termination is requested, this heuristic returns one of the best muses found until this
	 * point.
	 */
	public static MusContainer chooseNarrowestMus(final ArrayList<MusContainer> muses, final Random rnd,
			final TerminationRequest request) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(
				findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsNarrowerMus, request), rnd);
	}

	/**
	 * Chooses the widest Mus of the given ArrayList and returns its MusContainer. In case there are multiple such
	 * muses, this algorithm randomly chooses one of them. Wide here means, that the difference between the highest
	 * index of a constraint in the mus and the lowest index of a constraint in the mus is big. Returns null if the
	 * given list is empty. If termination is requested, this heuristic returns one of the best muses found until this
	 * point.
	 */
	public static MusContainer chooseWidestMus(final ArrayList<MusContainer> muses, final Random rnd,
			final TerminationRequest request) {
		if (muses.isEmpty()) {
			return null;
		}
		return chooseRandomMus(
				findBestMusesAccordingToGivenCriterion(muses, Heuristics::compareWhichMusIsWiderMus, request), rnd);
	}

	/**
	 * First selects the wide Muses of the given ArrayList. Tolerance specifies which muses count as "wide" - to be
	 * precise a mus counts as wide when widthOf(mus) >= (1-tolerance)*maximumWidthOfMuses(muses). Afterwards, the
	 * smallest Mus amongst the widest muses is returned. In case there are multiple such muses, this algorithm randomly
	 * chooses one of them. Returns null if the given list is empty. If termination is requested, this heuristic returns
	 * one of the best muses found until this point.
	 */
	public static MusContainer chooseSmallestAmongWideMuses(final ArrayList<MusContainer> muses, final double tolerance,
			final Random rnd, final TerminationRequest request) {
		if (muses.isEmpty()) {
			return null;
		}
		final ArrayList<MusContainer> widestMuses = new ArrayList<>();
		final MusContainer widestMus = chooseWidestMus(muses, rnd, request);
		final int maximalOccurringWidth = width(widestMus);
		int currentWidth;
		if (request.isTerminationRequested()) {
			return widestMus;
		}
		int i = 0;
		MusContainer container;
		while (i < muses.size() && !request.isTerminationRequested()) {
			container = muses.get(i);
			currentWidth = width(container);
			if (currentWidth >= (1 - tolerance) * maximalOccurringWidth) {
				widestMuses.add(container);
			}
			i++;
		}
		return chooseSmallestMus(widestMuses, rnd, request);
	}

	/**
	 * First selects the small Muses of the given ArrayList. Tolerance specifies which muses count as "small" - to be
	 * precise a mus counts as small when sizeOf(mus) <= (1+tolerance)*minimumSizeOfMuses(muses). Afterwards, the widest
	 * Mus amongst the small muses is returned. In case there are multiple such muses, this algorithm randomly chooses
	 * one of them. Returns null if the given list is empty. If termination is requested, this heuristic returns one of
	 * the best muses found until this point.
	 */
	public static MusContainer chooseWidestAmongSmallMuses(final ArrayList<MusContainer> muses, final double tolerance,
			final Random rnd, final TerminationRequest request) {
		if (muses.isEmpty()) {
			return null;
		}
		final ArrayList<MusContainer> smallestMuses = new ArrayList<>();
		final MusContainer smallestMus = chooseSmallestMus(muses, rnd, request);
		final int minimalOccurringSize = size(smallestMus);
		int currentSize;
		if (request.isTerminationRequested()) {
			return smallestMus;
		}
		int i = 0;
		MusContainer container;
		while (i < muses.size() && !request.isTerminationRequested()) {
			container = muses.get(i);
			currentSize = size(container);
			if (currentSize <= (1 + tolerance) * minimalOccurringSize) {
				smallestMuses.add(container);
			}
			i++;
		}
		return chooseWidestMus(smallestMuses, rnd, request);
	}

	/**
	 * This is here for documentary purpose and also maybe for use as FunctionalInterface later on.
	 */
	public static ArrayList<MusContainer> chooseAllMuses(final ArrayList<MusContainer> muses) {
		return muses;
	}

	/**
	 * This returns the most extreme muses in terms of the other heuristics in this class that return a single mus.
	 * Random and the TerminationRequest are just passed to the individual heuristics.
	 */
	public static ArrayList<MusContainer> chooseMostDifferentMusesWithRespectToOtherHeuristics(
			final ArrayList<MusContainer> muses, final Random rnd, final TerminationRequest request) {
		if (muses.isEmpty()) {
			return new ArrayList<>();
		}
		final ArrayList<MusContainer> mostExtremeMuses = new ArrayList<>();
		// ignore Random
		mostExtremeMuses.add(chooseSmallestMus(muses, rnd, request));
		mostExtremeMuses.add(chooseBiggestMus(muses, rnd, request));
		mostExtremeMuses.add(chooseMusWithLowestLexicographicalOrder(muses, rnd, request));
		mostExtremeMuses.add(chooseMusWithHighestLexicographicalOrder(muses, rnd, request));
		mostExtremeMuses.add(chooseShallowestMus(muses, rnd, request));
		mostExtremeMuses.add(chooseDeepestMus(muses, rnd, request));
		mostExtremeMuses.add(chooseNarrowestMus(muses, rnd, request));
		mostExtremeMuses.add(chooseWidestMus(muses, rnd, request));
		mostExtremeMuses.add(chooseSmallestAmongWideMuses(muses, 0.9, rnd, request));
		mostExtremeMuses.add(chooseWidestAmongSmallMuses(muses, 0.9, rnd, request));
		return mostExtremeMuses;
	}

	/**
	 * For a given set of muses and a random number generator, returns an ArrayList of {@link MusContainer} which muses
	 * are as different as possible. More specifically, at the beginning a random mus is chosen. Afterwards, a loop is
	 * executed until the given size is reached. The loop finds the mus which maximizes the minimum number of different
	 * statements {@link #numberOfDifferentStatements(MusContainer, MusContainer)} between itself and the muses that
	 * have already been chosen to be in the list that will be returned. Note that the returned list will not contain
	 * duplicates, hence it could be smaller than the given size. If termination is requested, this heuristic returns
	 * one of the best muses found until this point.
	 */
	public static ArrayList<MusContainer> chooseDifferentMusesWithRespectToStatements(
			final ArrayList<MusContainer> muses, final int size, final Random rnd, final TerminationRequest request) {
		if (muses.isEmpty() || size == 0) {
			return new ArrayList<>();
		}
		final ArrayList<MusContainer> differentMuses = new ArrayList<>();
		final ArrayList<MusContainer> maxMinDifferenceMuses = new ArrayList<>();
		differentMuses.add(muses.get(rnd.nextInt(muses.size())));
		int maxMinDifference;
		int currentMinDifference;
		int i = 1;
		while (i < size && !request.isTerminationRequested()) {
			maxMinDifference = Integer.MIN_VALUE;
			for (final MusContainer contender : muses) {
				currentMinDifference = findMinimumNumberOfDifferentStatements(contender, differentMuses);
				if (currentMinDifference > maxMinDifference) {
					maxMinDifference = currentMinDifference;
					maxMinDifferenceMuses.clear();
					maxMinDifferenceMuses.add(contender);
				} else if (currentMinDifference == maxMinDifference) {
					maxMinDifferenceMuses.add(contender);
				}
			}
			if (maxMinDifference == 0) {
				// This means maxMinDifferenceMus is a duplicate
				break;
			}
			differentMuses.add(chooseRandomMus(maxMinDifferenceMuses, rnd));
			i++;
		}
		return differentMuses;
	}

	/**
	 * Find the minimum number of different statements (the minimum Hamming distance) between the given mus1 and some
	 * mus of the given list of muses.
	 */
	private static int findMinimumNumberOfDifferentStatements(final MusContainer mus1,
			final ArrayList<MusContainer> muses) {
		int currentDifference;
		int minimumDifference = Integer.MAX_VALUE;
		for (final MusContainer mus2 : muses) {
			currentDifference = numberOfDifferentStatements(mus1, mus2);
			if (currentDifference < minimumDifference) {
				minimumDifference = currentDifference;
			}
		}
		return minimumDifference;
	}

	/**
	 * Returns the number of different statements of the two muses (hence, the Hamming distance).
	 */
	public static int numberOfDifferentStatements(final MusContainer mus1, final MusContainer mus2) {
		final BitSet realMus1 = mus1.getMus();
		final BitSet realMus2 = mus2.getMus();
		int difference = 0;
		for (int i = 0; i < realMus1.length(); i++) {
			if ((realMus1.get(i) && !realMus2.get(i)) || (realMus2.get(i) && !realMus1.get(i))) {
				difference++;
			}
		}
		if (realMus2.length() > realMus1.length()) {
			for (int i = realMus2.nextSetBit(realMus1.length()); i >= 0; i = realMus2.nextSetBit(i + 1)) {
				difference++;
			}
		}
		return difference;
	}

	private static ResultOfComparison compareWhichMusIsSmaller(final MusContainer mus1, final MusContainer mus2) {
		final int length1 = size(mus1);
		final int length2 = size(mus2);
		if (length1 < length2) {
			return ResultOfComparison.MUS1;
		} else if (length1 > length2) {
			return ResultOfComparison.MUS2;
		} else {
			return ResultOfComparison.EQUAL;
		}
	}

	private static ResultOfComparison compareWhichMusIsBigger(final MusContainer mus1, final MusContainer mus2) {
		return compareWhichMusIsSmaller(mus2, mus1);
	}

	private static ResultOfComparison compareWhichMusHasLowerLexicographicalOrder(final MusContainer mus1,
			final MusContainer mus2) {
		final BitSet realMus1 = mus1.getMus();
		final BitSet realMus2 = mus2.getMus();
		for (int i = 0; i < realMus1.length(); i++) {
			if (realMus1.get(i)) {
				if (!realMus2.get(i)) {
					return ResultOfComparison.MUS1;
				}
			} else {
				if (realMus2.get(i)) {
					return ResultOfComparison.MUS2;
				}
			}
		}
		if (realMus2.length() > realMus1.length()) {
			return ResultOfComparison.MUS1;
		}
		throw new SMTLIBException("Both muses must be the same. This should not be.");
	}

	private static ResultOfComparison compareWhichMusHasHigherLexicographicalOrder(final MusContainer mus1,
			final MusContainer mus2) {
		if (compareWhichMusHasLowerLexicographicalOrder(mus1, mus2) == ResultOfComparison.MUS1) {
			return ResultOfComparison.MUS2;
		}
		return ResultOfComparison.MUS1;
	}

	private static ResultOfComparison compareWhichMusIsShallowerMus(final MusContainer mus1, final MusContainer mus2) {
		final int depth1 = depth(mus1);
		final int depth2 = depth(mus2);
		if (depth1 < depth2) {
			return ResultOfComparison.MUS1;
		} else if (depth1 > depth2) {
			return ResultOfComparison.MUS2;
		} else {
			return ResultOfComparison.EQUAL;
		}
	}

	private static ResultOfComparison compareWhichMusIsDeeperMus(final MusContainer mus1, final MusContainer mus2) {
		return compareWhichMusIsShallowerMus(mus2, mus1);
	}

	private static ResultOfComparison compareWhichMusIsNarrowerMus(final MusContainer mus1, final MusContainer mus2) {
		final int width1 = width(mus1);
		final int width2 = width(mus2);
		if (width1 < width2) {
			return ResultOfComparison.MUS1;
		} else if (width1 > width2) {
			return ResultOfComparison.MUS2;
		} else {
			return ResultOfComparison.EQUAL;
		}
	}

	private static ResultOfComparison compareWhichMusIsWiderMus(final MusContainer mus1, final MusContainer mus2) {
		return compareWhichMusIsNarrowerMus(mus2, mus1);
	}

	private static ArrayList<MusContainer> findBestMusesAccordingToGivenCriterion(final ArrayList<MusContainer> muses,
			final BiFunction<MusContainer, MusContainer, ResultOfComparison> criterion,
			final TerminationRequest request) {
		final ArrayList<MusContainer> bestMuses = new ArrayList<>();
		MusContainer oneOfTheBestMuses = muses.get(0);
		bestMuses.add(oneOfTheBestMuses);
		MusContainer contender;
		ResultOfComparison result;
		int i = 1;
		while (i < muses.size() && !request.isTerminationRequested()) {
			contender = muses.get(i);
			result = criterion.apply(oneOfTheBestMuses, contender);
			if (result == ResultOfComparison.MUS2) {
				bestMuses.clear();
				bestMuses.add(contender);
				oneOfTheBestMuses = contender;
			} else if (result == ResultOfComparison.EQUAL) {
				bestMuses.add(contender);
			}
			i++;
		}
		return bestMuses;
	}

	public static int size(final MusContainer mus) {
		return mus.getMus().cardinality();
	}

	public static int depth(final MusContainer mus) {
		return mus.getMus().nextSetBit(0);
	}

	public static int width(final MusContainer mus) {
		return mus.getMus().length() - mus.getMus().nextSetBit(0);
	}
}
