/*
 * Copyright (C) 2010-2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.Word;

/**
 * Implementation of a nested word.
 * <p>
 * A nested word is a model for data that has not only a linear order (like a word) but also a hierarchical order (like
 * an execution of a procedural program or an XML document).
 * <p>
 * Nested words have been introduced by Rajeev Alur et al.
 * <ul>
 * <li>[1] http://www.cis.upenn.edu/~alur/nw.html</li>
 * <li>[2] Rajeev Alur, P. Madhusudan: Adding Nesting Structure to Words. Developments in Language Theory 2006:1-13</li>
 * <li>[3] Rajeev Alur, P. Madhusudan: Adding nesting structure to words. J. ACM (JACM) 56(3) (2009)</li>
 * </ul>
 * In this implementation we stick to the definition of [3] and deviate from [2] by allowing nested words to have
 * pending calls and pending returns.
 * <p>
 * In this implementation Objects are used as symbols of the alphabet. The type of these objects is specified by the
 * parameter {@link LETTER}.
 * <p>
 * We model the word of a nested word using an array of {@link LETTER}s. The (binary) nesting relation is modeled by an
 * integer array (of the same length) in the following way. If <tt>i</tt> is an internal position, the array at position
 * <tt>i</tt> is {@link #INTERNAL_POSITION}. If <tt>i</tt> is a call position, the array at position <tt>i</tt> is
 * either the position of the corresponding return position, or {@link #PLUS_INFINITY} if it is a pending call. If
 * <tt>i</tt> is a return position, the array at position <tt>i</tt> is either the position of the corresponding call
 * position, or {@link #MINUS_INFINITY} if it is a pending return.
 * <p>
 * Example: The nested word <tt>(a b c d, [(0,2),(-infinity,3)])</tt> is modeled as <tt>word = ['a', 'b', 'c', 'd'],
 * nesting relation = [2, {@link #INTERNAL_POSITION}, 0, {@link #MINUS_INFINITY}]</tt>
 * <p>
 * This model of a nesting relation wastes some memory if the nested word has only few calls and returns, but is very
 * simple.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Type of the objects which can be symbols of the alphabet.
 */
// FIXME after all testscript are ready: Remove unnecessay constructors an let
// callers use the right methods.
public class NestedWord<LETTER> extends Word<LETTER> {
	/**
	 * Constant to represent internal positions in our array model of a nesting relation.
	 */
	public static final int INTERNAL_POSITION = -2;
	
	/**
	 * Constant to represent pending calls in our array model of a nesting relation.
	 */
	public static final int PLUS_INFINITY = Integer.MAX_VALUE;
	
	/**
	 * Constant to represent pending returns in our array model of a nesting relation.
	 */
	public static final int MINUS_INFINITY = Integer.MIN_VALUE;

	private static final String QUOTE_SPACE = "\" ";
	private static final char QUOTE = '\"';
	private static final String ACCESS_TO_POSITION = "Access to position ";
	
	private final int[] mNestingRelation;
	
	private Set<Integer> mCallPositions;
	
	private SortedMap<Integer, LETTER> mPendingReturns;
	
	/**
	 * Constructor for a nested word from two arrays.
	 * <p>
	 * The two arrays must have the same length.
	 * <p>
	 * The empty word is constructed by passing two empty arrays.
	 * <p>
	 * Whether the given arguments satisfy the definition of a nested word is checked by {@code assert} statements.
	 * 
	 * @param word
	 *            The (linear) word of a nested word.
	 * @param nestingRelation
	 *            The nesting relation of nested word.
	 */
	public NestedWord(final LETTER[] word, final int[] nestingRelation) {
		assert assertValidNestedWord(word, nestingRelation);
		mWord = word;
		mNestingRelation = nestingRelation;
	}
	
	/**
	 * Constructor for the empty nested word.
	 */
	@SuppressWarnings("unchecked")
	public NestedWord() {
		mWord = (LETTER[]) new Object[0];
		mNestingRelation = new int[0];
	}
	
	/**
	 * Constructor for the nested word of length 1 (one).
	 * 
	 * @param letter
	 *            letter
	 * @param internalOrCallOrReturn
	 *            represents the nesting relation (either {@link #INTERNAL_POSITION}, {@link #PLUS_INFINITY}, or
	 *            {@link MINUS_INFINITY})
	 */
	@SuppressWarnings("unchecked")
	public NestedWord(final LETTER letter, final int internalOrCallOrReturn) {
		if (!isSpecialNestingRelationIndex(internalOrCallOrReturn)) {
			throw new IllegalArgumentException(
					"The only position has to be either internal, pending call, or pending return.");
		}
		mWord = (LETTER[]) new Object[] { letter };
		mNestingRelation = new int[] { internalOrCallOrReturn };
	}
	
	/**
	 * Private constructor for the nested word of only internal positions from an ordinary word.
	 * <p>
	 * Called from {@link #nestedWord(Word)}.
	 * <p>
	 * TODO: Preserve nesting relation if word is nested word
	 * 
	 * @param word
	 *            word
	 */
	@SuppressWarnings("unchecked")
	private NestedWord(final Word<LETTER> word) {
		final int length = word.length();
		mWord = (LETTER[]) new Object[length];
		mNestingRelation = new int[length];
		for (int i = 0; i < length; i++) {
			mWord[i] = word.getSymbol(i);
			mNestingRelation[i] = INTERNAL_POSITION;
		}
	}
	
	/**
	 * Converts any {@link Word} to a nested word.
	 * 
	 * @param word
	 *            ordinary word
	 * @param <LETTER>
	 *            letter type
	 * @return the input if it was a nested word, a fresh nested word otherwise
	 */
	public static <LETTER> NestedWord<LETTER> nestedWord(final Word<LETTER> word) {
		if (word instanceof NestedWord) {
			return (NestedWord<LETTER>) word;
		} else {
			return new NestedWord<>(word);
		}
	}
	
	/**
	 * Computes all call positions.<br>
	 * The result is cached, so the result needs not be stored locally by a user.
	 * 
	 * @return all call positions
	 */
	public Set<Integer> getCallPositions() {
		if (mCallPositions == null) {
			mCallPositions = computeCallPositions();
		}
		return mCallPositions;
	}
	
	/**
	 * @return All call positions.
	 */
	private Set<Integer> computeCallPositions() {
		final Set<Integer> result = new LinkedHashSet<>();
		for (int i = 0; i < mNestingRelation.length; i++) {
			if (isCallPosition(i)) {
				result.add(i);
			}
		}
		return result;
	}
	
	/**
	 * TODO Christian 2016-08-25: All callers directly invoke the {@link java.util.SortedMap#keySet()} method.
	 * We could change the return value to a {@link java.util.SortedSet}.
	 * 
	 * @return all pending return positions in a sorted order
	 */
	public SortedMap<Integer, LETTER> getPendingReturns() {
		if (mPendingReturns == null) {
			mPendingReturns = computePendingReturnPositions();
		}
		return mPendingReturns;
	}
	
	private SortedMap<Integer, LETTER> computePendingReturnPositions() {
		final SortedMap<Integer, LETTER> result = new TreeMap<>();
		for (int i = 0; i < mNestingRelation.length; i++) {
			if (isPendingReturn(i)) {
				result.put(i, mWord[i]);
			}
		}
		return result;
	}
	
	/**
	 * Checks whether all entries in the nesting relation are in valid range.
	 * <p>
	 * This is a necessary check that an {@code int} array is a possible candidate for a nesting relation.
	 * <p>
	 * This method is only used in assertions.
	 * 
	 * @param nestingRelation
	 *            our array model of a nesting relation
	 * @return true iff every entry of <tt>nestingRelation</tt> is in the range of the array or an INTERNAL_POSITION,
	 *         PLUS_INFINITY, or MINUS_INFINITY.
	 */
	private static boolean nestingRelationValuesInRange(final int[] nestingRelation) {
		for (final int content : nestingRelation) {
			if ((content < 0 || content >= nestingRelation.length) && (!isSpecialNestingRelationIndex(content))) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * Checks whether all matching call-return entries in the nesting relation are symmetric.
	 * <p>
	 * This is a necessary check that an {@code int} array is a possible candidate for a nesting relation.
	 * <p>
	 * This method is only used in assertions.
	 * 
	 * @param nestingRelation
	 *            our array model of a nesting relation
	 * @return true iff <tt>nestingRelation[i] = j</tt> implies <tt>nestingRelation[j] = i</tt> for all <tt>i</tt> such
	 *         that <tt>0 <= nestingRelation[i] < nestingRelation.length</tt>
	 */
	private static boolean nestingRelationSymmetricNestingEdges(final int[] nestingRelation) {
		for (int i = 0; i < nestingRelation.length; i++) {
			if (0 <= nestingRelation[i] && nestingRelation[i] < nestingRelation.length
					&& nestingRelation[nestingRelation[i]] != i) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * Performs two checks:
	 * <ul>
	 * <li>The nesting is proper, i.e., that no two matched call-return pairs cross.</li>
	 * <li>A position in the nesting relation is not reflexive, i.e., there is no call-return pair at the same position
	 * </li>
	 * </ul>
	 * <p>
	 * This is a necessary check that an {@code int} array is a possible candidate for a nesting relation.
	 * <p>
	 * This method is only used in assertions.<br>
	 * (Caution!) Its runtime is quadratic in the length of the word.
	 * 
	 * @return false iff the modeled nesting relation contains (i,j) and (i',j') such that <tt>i < i' <= j < j'</tt>
	 */
	private static boolean nestingEdgesDoNotCross(final int[] nestingRelation) {
		for (int i = 0; i < nestingRelation.length; i++) {
			final int nestingEntry = nestingRelation[i];
			if (nestingEntry < 0 || nestingEntry >= nestingRelation.length) {
				continue;
			}
			if (nestingEntry == i) {
				return false;
			}
			for (int k = i + 1; k < nestingEntry; k++) {
				if ((nestingRelation[k] >= nestingEntry) || (nestingRelation[k] == MINUS_INFINITY)) {
					return false;
				}
			}
		}
		return true;
	}
	
	/**
	 * @return The length of the nested word is the length of the word.
	 *         {@inheritDoc}
	 */
	@SuppressWarnings("squid:S1185")
	@Override
	public int length() {
		return super.length();
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return true iff the position is a call position
	 */
	public boolean isCallPosition(final int position) {
		assert assertBounds(position);
		return mNestingRelation[position] >= position;
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return true iff the position is an internal position
	 */
	public boolean isInternalPosition(final int position) {
		assert assertBounds(position);
		return mNestingRelation[position] == INTERNAL_POSITION;
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return true iff the position is a return position
	 */
	public boolean isReturnPosition(final int position) {
		assert assertBounds(position);
		return mNestingRelation[position] <= position && mNestingRelation[position] != INTERNAL_POSITION;
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return the symbol at the given position
	 */
	public LETTER getSymbolAt(final int position) {
		assert position >= 0 && position < mWord.length;
		return mWord[position];
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return the corresponding return position if the given position is call position
	 */
	public int getReturnPosition(final int position) {
		if (isCallPosition(position)) {
			return mNestingRelation[position];
		} else {
			throw new IllegalArgumentException("Argument must be a call position.");
		}
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return the corresponding call position if the given position is return position
	 */
	public int getCallPosition(final int position) {
		if (isReturnPosition(position)) {
			return mNestingRelation[position];
		} else {
			throw new IllegalArgumentException("Argument must be a return position.");
		}
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return true iff the position is a pending call position
	 */
	public boolean isPendingCall(final int position) {
		return mNestingRelation[position] == PLUS_INFINITY;
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return true iff the position is a pending return position
	 */
	public boolean isPendingReturn(final int position) {
		return mNestingRelation[position] == MINUS_INFINITY;
	}
	
	/**
	 * @return true iff the word contains pending returns.
	 */
	public boolean containsPendingReturns() {
		for (int i = 0; i < mWord.length; i++) {
			if (isPendingReturn(i)) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Creates a new nested word as a subword in the given range.
	 * 
	 * @param firstIndex
	 *            the index where the subword starts
	 * @param lastIndex
	 *            the index where the subword ends
	 * @return a new nested word which is a subword of {@code this}
	 */
	public NestedWord<LETTER> getSubWord(final int firstIndex, final int lastIndex) {
		if (firstIndex < 0) {
			throw new IllegalArgumentException("The first index must be greater or equal to 0.");
		}
		if (lastIndex < firstIndex) {
			throw new IllegalArgumentException("The last index must not be smaller than the first.");
		}
		if (lastIndex >= length()) {
			throw new IllegalArgumentException("The last index must be strictly smaller than the word length.");
		}
		
		// create nesting relation (more involved due to index changes)
		final int[] newNestingRelation = new int[lastIndex - firstIndex + 1];
		for (int i = firstIndex, newWordPos = 0; i <= lastIndex; ++i, ++newWordPos) {
			final int oldNestingEntry = mNestingRelation[i];
			if (isSpecialNestingRelationIndex(oldNestingEntry)) {
				newNestingRelation[newWordPos] = oldNestingEntry;
			} else if (oldNestingEntry < firstIndex) {
				// becomes pending return
				assert oldNestingEntry >= 0;
				newNestingRelation[newWordPos] = MINUS_INFINITY;
			} else if (oldNestingEntry > lastIndex) {
				// becomes pending call
				assert oldNestingEntry < length();
				newNestingRelation[newWordPos] = PLUS_INFINITY;
			} else {
				assert oldNestingEntry >= firstIndex && oldNestingEntry <= lastIndex;
				newNestingRelation[newWordPos] = oldNestingEntry - firstIndex;
			}
		}
		
		// copy word
		final LETTER[] subwordAsArray = Arrays.copyOfRange(mWord, firstIndex, lastIndex + 1);
		
		return new NestedWord<>(subwordAsArray, newNestingRelation);
	}
	
	/**
	 * Concatenation of nested words as described in [2].
	 * <p>
	 * Pending calls of the first word are 'matched' with pending
	 * returns of the second word. E.g., concatenation of <tt>(a b, {(0,infinity)})</tt> and
	 * <tt>(c, { (0,-infinity)}</tt> results is the nested word <tt>(a b c, {(0,2)})</tt>. The method does not change
	 * the original words.
	 * <p>
	 * Implementation details:<br>
	 * There are two pointers, one starting at the end of the first word and descending, and the other starting at the
	 * beginning of the second word and increasing. Whenever a pending call is found in the first word, the next pending
	 * return in the second word is found and they are matched.
	 * 
	 * @param nestedWord2
	 *            nested word that is 'appended' to this word
	 * @return new nested word which is the concatenation
	 */
	@SuppressWarnings("unchecked")
	public NestedWord<LETTER> concatenate(final NestedWord<LETTER> nestedWord2) {
		final LETTER[] word2 = nestedWord2.mWord;
		final int[] nestingRelation2 = nestedWord2.mNestingRelation;
		
		// create nesting relation
		final int[] concatNestingRelation = new int[mWord.length + word2.length];
		int index1 = mWord.length - 1;
		int index2 = 0;
		while (index1 >= 0) {
			if (mNestingRelation[index1] == PLUS_INFINITY) {
				// pending call
				if (index2 != word2.length) {
					index2 = findNextPendingReturn(nestingRelation2, concatNestingRelation, index2);
				}
				
				if (index2 == word2.length) {
					// found no pending return, stays a pending call
					concatNestingRelation[index1] = mNestingRelation[index1];
				} else {
					// found a pending return, nest
					concatNestingRelation[index1] = mWord.length + index2;
					concatNestingRelation[mWord.length + index2] = index1;
					index2++;
				}
			} else {
				// no pending call, just copy
				concatNestingRelation[index1] = mNestingRelation[index1];
			}
			index1--;
		}
		// finished first word, copy possibly remaining parts from second word
		for (; index2 < nestingRelation2.length; ++index2) {
			if (isSpecialNestingRelationIndex(nestingRelation2[index2])) {
				concatNestingRelation[mWord.length + index2] = nestingRelation2[index2];
			} else {
				concatNestingRelation[mWord.length + index2] = mWord.length + nestingRelation2[index2];
			}
		}
		
		// copy word parts
		final LETTER[] concatWord = (LETTER[]) new Object[mWord.length + word2.length];
		System.arraycopy(mWord, 0, concatWord, 0, mWord.length);
		System.arraycopy(word2, 0, concatWord, mWord.length, word2.length);
		
		return new NestedWord<>(concatWord, concatNestingRelation);
	}
	
	/**
	 * Helper method for concatenation.
	 * <p>
	 * Finds the next pending call in the second word and already copies the other parts to the new nesting relation.
	 * 
	 * @param nestingRelation2
	 *            nesting relation of the second word
	 * @param concatNestingRelation
	 *            new nesting relation
	 * @param index2in
	 *            current index in the second word
	 * @return index in the second word where search should continue
	 */
	private int findNextPendingReturn(final int[] nestingRelation2, final int[] concatNestingRelation,
			final int index2in) {
		int index2out = index2in;
		while (index2out < nestingRelation2.length && nestingRelation2[index2out] != MINUS_INFINITY) {
			if (nestingRelation2[index2out] == INTERNAL_POSITION) {
				concatNestingRelation[mWord.length + index2out] = INTERNAL_POSITION;
			} else if (nestingRelation2[index2out] == PLUS_INFINITY) {
				concatNestingRelation[mWord.length + index2out] = PLUS_INFINITY;
			} else {
				concatNestingRelation[mWord.length + index2out] = mWord.length + nestingRelation2[index2out];
			}
			index2out++;
		}
		return index2out;
	}
	
	/*
	 * Some example Code for testing Concatenation
	 *
	 * Character[] testWord = { 'm' , 'n', 'o', 'p' }; int[] testRelation = { NestedWord.MINUS_INFINITY,
	 * NestedWord.MINUS_INFINITY, NestedWord.PLUS_INFINITY, NestedWord.PLUS_INFINITY }; NestedWord<Character> nw = new
	 * NestedWord<Character>(testWord, testRelation); Character[] testWord2 = { 'a', 'b', 'c', 'd', 'e', 'f', 'g'};
	 * int[] testRelation2 = { -2 , 3 , -2, 1, -2, NestedWord.MINUS_INFINITY, NestedWord.PLUS_INFINITY };
	 * NestedWord<Character> nw2 = new NestedWord<Character>(testWord2, testRelation2); mLogger.info("Nested Word:  "+
	 * nw.concatenate(nw2).toString());
	 */
	
	/**
	 * Print this nested word in style of a tagged alphabet [2].
	 * <p>
	 * Every symbol (which is itself printed by its {@link LETTER#toString()} method in quotes) at a call position is
	 * succeeded by {@code <} and every symbol at a return position is preceded by {@code >}.
	 * <p>
	 * Remark: There is a bijection from nested words to words in this tagged alphabet style.
	 */
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		for (int i = 0; i < mWord.length; i++) {
			// @formatter:off
			if (isInternalPosition(i)) {
				builder.append(QUOTE)
						.append(getSymbolAt(i))
						.append(QUOTE_SPACE);
			} else if (isCallPosition(i)) {
				builder.append(QUOTE)
						.append(getSymbolAt(i))
						.append("\"< ");
			} else {
				assert isReturnPosition(i);
				builder.append(">\"")
						.append(getSymbolAt(i))
						.append(QUOTE_SPACE);
			}
			// @formatter:on
		}
		return builder.toString();
	}
	
	private boolean assertValidNestedWord(final LETTER[] word, final int[] nestingRelation) {
		assert word.length == nestingRelation.length : "The nesting relation must contain one entry for each letter "
				+ "in the word.";
		assert nestingRelationValuesInRange(
				nestingRelation) : "The nesting relation may only contain -2, plus infinity, minus infinity, or "
						+ "natural numbers.";
		assert nestingRelationSymmetricNestingEdges(
				nestingRelation) : "If nestingRelation[i]=k, then nestingRelation[k]=i or nestingRelation[i] is either"
						+ "-2, plus infinity, or minus infinity.";
		assert nestingEdgesDoNotCross(nestingRelation) : "Nesting edges must not cross.";
		return true;
	}
	
	/**
	 * Asserts that the given index is within the word bounds.
	 * 
	 * @param index
	 *            index
	 * @return true (assertions are checked inside the method)
	 */
	private boolean assertBounds(final int index) {
		assert 0 <= index : ACCESS_TO_POSITION + index + " not possible. The first position of a nested word is 0.";
		assert index < mWord.length : ACCESS_TO_POSITION + index
				+ " not possible. The last position of this word is " + (mWord.length - 1) + '.';
		return true;
	}
	
	private static boolean isSpecialNestingRelationIndex(final int nestingRelationEntry) {
		return nestingRelationEntry == INTERNAL_POSITION || nestingRelationEntry == PLUS_INFINITY
				|| nestingRelationEntry == MINUS_INFINITY;
	}
}
