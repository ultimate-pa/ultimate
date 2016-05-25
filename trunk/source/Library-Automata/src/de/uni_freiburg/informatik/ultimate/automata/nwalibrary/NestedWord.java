/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.Word;

/**
 * Implementation of nested words.
 * 
 * A nested word is a model for data that has not only a linear order (like a
 * word) but also a hierarchical order (like an execution of a procedural
 * program or like an XML document.
 *  
 * Nested words have been introduced by Rajeev Alur et al.
 * [1] http://www.cis.upenn.edu/~alur/nw.html
 * [2] Rajeev Alur, P. Madhusudan: Adding Nesting Structure to Words. Developments in Language Theory 2006:1-13
 * [3] Rajeev Alur, P. Madhusudan: Adding nesting structure to words. J. ACM (JACM) 56(3) (2009)
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * In this implementation we stick to the definition of [3] and deviate from [2]
 * by allowing nested words to have pending calls and pending returns.
 * 
 * In this implementation Objects are used as symbols of the alphabet. The type
 * of these objects is specified by the LETTER parameter.
 * 
 * We model the word of a nested word using an array of LETTERs.
 * The (binary) nesting Relation is modeled by an int array mNestingRelation
 * (that has the same length) the following way.
 * If i is an internal position mNestingRelation[i] is INTERNAL_POSITION.
 * If i is a call position mNestingRelation[i] is the position of the
 * corresponding return position and PLUS_INFINITY is it is a pending call.
 * If i is a return position mNestingRelation[i] is the position of the
 * corresponding call position and MINUS_INFINITY is it is a pending return.
 * 
 * Example:
 * The nested word
 *                    (a b c d, {(0,2),(-infinity,3)} )
 * is modeled as
 *            mWord = {'a',       'b'        ,'c'      'd' }
 * mNestingRelation = { 2 , INTERNAL_POSITION, 0 , MINUS_INFINITY }
 * 
 * This model of a nesting relation wastes some memory if the nested word has 
 * only few calls and returns, but is very simple.
 * 
 * @param <LETTER>
 * 		Type of the Objects which can be symbols of the alphabet.
 */

//FIXME after all testscript are ready: Remove unnecessay constructors an let
//callers use the right methods. 
public class NestedWord<LETTER> extends Word<LETTER> {
	/**
	 * Constant to represent internal positions in our array model of a 
	 * nesting relation.
	 */
	public static final int INTERNAL_POSITION = -2;

	/**
	 * Constant to represent pending calls in our array model of a nesting
	 * relation.
	 */
	public static final int PLUS_INFINITY = Integer.MAX_VALUE;
	
	/**
	 * Constant to represent pending returns in our array model of a nesting
	 * relation.
	 */
	public static final int MINUS_INFINITY = Integer.MIN_VALUE;
	

	private final int[] mNestingRelation;

	private Set<Integer> mCallPositions;
	
	private TreeMap<Integer, LETTER> mPendingReturns;
	
	
	/**
	 * Constructor for NestedWord. The empty word is constructed by using two
	 * empty arrays as arguments.
	 * If the given arguments satisfy, the definition of a nested word is checked
	 * by assert statements.
	 * To use exception for the case, the definitions are violated would have
	 * been a nicer way of doing this. But I wanted to offer a fast way of
	 * constructing a nested word for users that are sure that their delivered
	 * arguments are valid. 
	 * @param word
	 * 		The (linear) word of a nested word.
	 * @param nestingRelation
	 * 		The nestingRelation of nested word.
	 */
	public NestedWord(LETTER[] word, int[] nestingRelation) {
		assert (word.length == nestingRelation.length) : 
				"nestingRelation must contain one entry for each LETTER in the word";
		assert (nestingRelationValuesInRange(nestingRelation)) : 
				"nestingRelation may contain one only -2, plus infinity, minus infinity or natural numbers";
		assert (nestingRelationSymmetricNestingEdges(nestingRelation)) : 
				"if nestingRelation[i]=k then nestingRelation[k]=i or nestingRelation[i] is either" +
				"plus infinity, minus infinity or internal position";
		assert (nestingEdgesDoNotCross(nestingRelation)) : 
				"nesting edges must not cross";
		mWord = word;
	    this.mNestingRelation = nestingRelation;	
	}
	
	public NestedWord() {
		final ArrayList<LETTER> al = new ArrayList<LETTER>(0);
		mWord = (LETTER[]) al.toArray();
		final int[] nr = { };
		this.mNestingRelation = nr;
	}
	
	/**
	 * Word of length one
	 * @param letter
	 */
	public NestedWord(LETTER letter, int internalORcallORreturn) {
		if (internalORcallORreturn != INTERNAL_POSITION && 
				internalORcallORreturn != PLUS_INFINITY && 
				internalORcallORreturn != MINUS_INFINITY) {
			throw new IllegalArgumentException(
					"only position has to be either internal, pending call, or pending return");
		}
		final ArrayList<LETTER> al = new ArrayList<LETTER>(1);
		al.add(letter);
		mWord = (LETTER[]) al.toArray();
		final int[] nr = { internalORcallORreturn };
		this.mNestingRelation = nr;
	}
	
	/**
	 * TODO: Preserve nesting relation if word is nested word
	 * @param word
	 */
	private NestedWord(Word<LETTER> word) {
		mWord = (LETTER[]) new ArrayList<LETTER>(word.asList()).toArray();
		final int length = word.length();
		this.mNestingRelation = new int[length];
		for (int i=0; i<length; i++) {
			mWord[i] = word.getSymbol(i);
			mNestingRelation[i] = INTERNAL_POSITION;
		}
	}
	
	public static <LETTER> NestedWord<LETTER> nestedWord(Word<LETTER> word) {
		if (word instanceof NestedWord) {
			return (NestedWord<LETTER>) word;
		}
		else {
			return new NestedWord<LETTER>(word);
		}
	}
	
	
	private LETTER[] getWord() {
		return mWord;
	}
	
	private int[] getNestingRelation() {
		return this.mNestingRelation;
	}
	
	public Set<Integer> getCallPositions() {
		if (mCallPositions == null) {
			mCallPositions = computeCallPositions();
		}
		return mCallPositions;
	}
	
	private Set<Integer> computeCallPositions() {
		final Set<Integer> result = new HashSet<Integer>();
		for (int i=0; i<mNestingRelation.length; i++) {
			if (isCallPosition(i)) {
				result.add(i);
			}
		}
		return result;
	}
	
	public TreeMap<Integer, LETTER> getPendingReturns() {
		if (mPendingReturns == null) {
			mPendingReturns = computePendingReturnPositions();
		}
		return mPendingReturns;
	}
	
	private TreeMap<Integer, LETTER> computePendingReturnPositions() {
		final TreeMap<Integer, LETTER> result = new TreeMap<Integer, LETTER>();
		for (int i=0; i<mNestingRelation.length; i++) {
			if (isReturnPosition(i) && isPendingReturn(i)) {
				result.put(i, mWord[i]);
			}
		}
		return result;
	}
	
	
	/**
	 * Checks if an int array is a possible candidate for a nesting relation.
	 * This method is only used in assertions. 
	 * @param nestingRelation
	 * 		Our array model of a nesting relation
	 * @return 
	 * 		True iff every entry of nestingRelation is in index in the range of
	 * 		the array or an INTERNAL_POSITION, PLUS_INFINITY or	MINUS_INFINITY.   
	 */
	private boolean nestingRelationValuesInRange(int[] nestingRelation) {
		for (int i=0; i< nestingRelation.length; i++) {
			if (nestingRelation[i] == INTERNAL_POSITION) { }
			else if (0<=nestingRelation[i] && nestingRelation[i] < nestingRelation.length) {}
			else if (nestingRelation[i] == PLUS_INFINITY) {}
			else if (nestingRelation[i] == MINUS_INFINITY) {}
			else {
				return false;
			}
		}
		return true;
	}

	
	/**
	 * Checks if an int array is a possible candidate for a nesting relation.
	 * This method is only used in assertions. 
	 * @param nestingRelation
	 * 		Our array model of a nesting relation
	 * @return 
	 * 		True iff nestingRelation[i]=j implies nestingRelation[j]=i for all i
	 * 		such that 0<=nestingRelation[i]< nestingRelation.length
	 */
	private boolean nestingRelationSymmetricNestingEdges(int[] nestingRelation) {
		for (int i=0; i< nestingRelation.length; i++) {
			if ( 0 <= nestingRelation[i]
			     && nestingRelation[i]<nestingRelation.length
			     && nestingRelation[nestingRelation[i]]!=i ) {
			return false;
			}
		}
	return true;
	}
	
	
	/**
	 * Checks if an int array is a possible candidate for a nesting relation.
	 * This method is only used in assertions.
	 * (Caution!) Its runtime is quadratic in the length of the word.
	 * @param nestingRelation
	 * @return
	 * 		False iff the modeled nesting relation contains (i,j) and (i',j')
	 * 		such that i<i'<=j<j'.
	 */

	private boolean nestingEdgesDoNotCross(int[] nestingRelation) {
		for (int i=0; i< nestingRelation.length; i++) {
			if ( 0<=nestingRelation[i] && nestingRelation[i]<nestingRelation.length) {
				for (int k=i+1; k<nestingRelation[i]; k++) {
					if (nestingRelation[k]>=nestingRelation[i]) {
						return false;
					}
					if (nestingRelation[k]==MINUS_INFINITY) {
						return false;
					}
				}
				if (nestingRelation[i]==i) {
					return false;
				}
			}
		}
		return true;
	}
	
	/**
	 * 
	 * @return The length of the NestedWord is the length of the word. The length is 0 
	 * for the empty word, 1 for the word that consists of one symbol, etc.
	 */
	@Override
	public int length() {
		return super.length();
	}
	
	
	public boolean isCallPosition(int i) {
		assert (0<=i) : "Access to position " + i + " not possible. The first position of a nested word is 0";
		assert (i<=mWord.length) : "Access to position " + i + " not possible. The last positions of this word is " + (mWord.length-1);
		if (mNestingRelation[i] >=i) {
			return true;
		} else {
			return false;
		}
	}
	
	
	public boolean isInternalPosition(int i) {
		assert (0<=i) : "Access to position " + i + " not possible. The first position of a nested word is 0";
		assert (i<=mWord.length) : "Access to position " + i + " not possible. The last positions of this word is " + (mWord.length-1);
		if (mNestingRelation[i] == INTERNAL_POSITION) {
			return true;
		} else {
			return false;
		}
	}
	
	
	public boolean isReturnPosition(int i) {
		assert (0<=i) : "Access to position " + i + " not possible. The first position of a nested word is 0";
		assert (i<=mWord.length) : "Access to position " + i + " not possible. The last positions of this word is " + (mWord.length-1);
		if (mNestingRelation[i] <=i && mNestingRelation[i] != INTERNAL_POSITION) {
			return true;
		} else {
			return false;
		}
	}
	
	
	public LETTER getSymbolAt(int position) 
	{
		assert(position >= 0 && position < mWord.length);
		return mWord[position];
	}
	
	/**
	 * Return the corresponding return position if i is call position.
	 */
	public int getReturnPosition(int i) {
		if (isCallPosition(i)) {
			return mNestingRelation[i];
		}
		else {
			throw new IllegalArgumentException("Argument must be call position");
		}
	}
	
	
	/**
	 * Return the corresponding call position if i is return position.
	 */
	public int getCallPosition(int i) {
		if (isReturnPosition(i)) {
			return mNestingRelation[i];
		}
		else {
			throw new IllegalArgumentException("Argument must be return position");
		}
	}
	
	public boolean isPendingCall(int i) {
		if (mNestingRelation[i] == PLUS_INFINITY) {
			return true;
		} else {
			return false;
		}
	}
	
	public boolean isPendingReturn(int i) {
		if (mNestingRelation[i] == MINUS_INFINITY) {
			return true;
		} else {
			return false;
		}
	}
	
	public boolean containsPendingReturns() {
		boolean result = false;
		for (int i=0; i<this.length(); i++) {
			result = result || isPendingReturn(i);
		}
		return result;
	}
	
	
	/**
	 * Returns a new NestedWord which is a subword of this starting with
	 * firstIndex and ending with lastIndex.
	 */
	public NestedWord<LETTER> getSubWord(int firstIndex, int lastIndex) {
		if (lastIndex<firstIndex) {
			throw new IllegalArgumentException("lastIndex must not be smaller than first");
		}
		final ArrayList<LETTER> word = new ArrayList<LETTER>(lastIndex-firstIndex+1);
		final int[] nestingRelation = new int[lastIndex-firstIndex+1];
		int newWordPos = 0;
		for (int i=firstIndex;i<=lastIndex;i++) {
			word.add(getWord()[i]);
			final int nestingEntry = mNestingRelation[i];
			if (nestingEntry == INTERNAL_POSITION) {
				nestingRelation[newWordPos] = INTERNAL_POSITION;
			} else if  (nestingEntry == MINUS_INFINITY) {
				nestingRelation[newWordPos] = MINUS_INFINITY;
			} else if  (nestingEntry == PLUS_INFINITY) {
				nestingRelation[newWordPos] = PLUS_INFINITY;
			} else {
				if (isCallPosition(i)) {
					if (nestingEntry > lastIndex) {
						nestingRelation[newWordPos] = PLUS_INFINITY;
					} else {
						nestingRelation[newWordPos] = nestingEntry - firstIndex;
					}
				} else if (isReturnPosition(i)) {
					if (nestingEntry < firstIndex) {
						nestingRelation[newWordPos] = MINUS_INFINITY;
					} else {
						nestingRelation[newWordPos] = nestingEntry - firstIndex;
					}
				} else {
					throw new AssertionError();
				}
			}
			newWordPos++;
		}
		final LETTER[] wordAsArray = (LETTER[]) word.toArray();
		return new NestedWord<LETTER>(wordAsArray, nestingRelation);
	}
	


	/**
	 * Concatenation of nested words as described in [2]. Pending calls of the
	 * first word are 'matched' with pending returns of the second word.
	 * E.g. concatenation of 
	 *      (a b, {(0,infinity)})  and    (c, { (0,-infinity)}
	 * results is the nested word
	 *      (a b c, {(0,2)}).
	 * The method does not change this word.
	 * @param nestedWord2
	 * 		Nested word that is 'appended' to this word. 
	 * @return
	 * 		New nested word which is the concatenation.
	 */
	@SuppressWarnings("unchecked")
	public NestedWord<LETTER> concatenate(NestedWord<LETTER> nestedWord2) {
		final LETTER[] word2 = nestedWord2.getWord();
		final int[] nestingRelation2 = nestedWord2.getNestingRelation();
		final int[] concatNestingRelation = new int[mWord.length+word2.length];
		int i = mWord.length -1;
		int j = 0;
		while (i>=0) {
			if (mNestingRelation[i]!=PLUS_INFINITY) {
				concatNestingRelation[i]=mNestingRelation[i];
			}
			else {
				while (j<nestingRelation2.length && nestingRelation2[j]!=MINUS_INFINITY) {
					if (nestingRelation2[j]==INTERNAL_POSITION) {
						concatNestingRelation[mWord.length+j]=INTERNAL_POSITION;
					}
					else if (nestingRelation2[j]==PLUS_INFINITY) {
						concatNestingRelation[mWord.length+j]=PLUS_INFINITY;
					}
					else {
					concatNestingRelation[mWord.length+j]=mWord.length+nestingRelation2[j];
					}
					j++;
				}

				if (j!=word2.length) {
					concatNestingRelation[i]=mWord.length+j;
					concatNestingRelation[mWord.length+j]=i;
					j++;
				}
				else {
					concatNestingRelation[i]=mNestingRelation[i];
				}
			}
			i--;
		}
		while (j<nestingRelation2.length) {
			if (nestingRelation2[j]==INTERNAL_POSITION) {
				concatNestingRelation[mWord.length+j]=INTERNAL_POSITION;
			}
			else if (nestingRelation2[j]==PLUS_INFINITY) {
				concatNestingRelation[mWord.length+j]=PLUS_INFINITY;
			}
			else if (nestingRelation2[j]==MINUS_INFINITY) {
				concatNestingRelation[mWord.length+j]=MINUS_INFINITY;
			}
			else {
			concatNestingRelation[mWord.length+j]=mWord.length+nestingRelation2[j];
			}
			j++;
		}
		
		final LETTER[] concatWord = (LETTER[]) new Object[mWord.length+word2.length];
		System.arraycopy(mWord, 0, concatWord, 0, mWord.length);
		System.arraycopy(word2, 0, concatWord, mWord.length, word2.length);
		
		return new NestedWord<LETTER>(concatWord,concatNestingRelation);
	}
	
	/*
	*	Some example Code for testing Concateneation
	*
	*	Character[] testWord = { 'm' , 'n', 'o', 'p' }; 
	*	int[] testRelation = { NestedWord.MINUS_INFINITY, NestedWord.MINUS_INFINITY, NestedWord.PLUS_INFINITY, NestedWord.PLUS_INFINITY };
	*	NestedWord<Character> nw = new NestedWord<Character>(testWord, testRelation);
	*	Character[] testWord2 = { 'a', 'b', 'c', 'd', 'e', 'f', 'g'}; 
	*	int[] testRelation2 = { -2 , 3 , -2, 1, -2, NestedWord.MINUS_INFINITY, NestedWord.PLUS_INFINITY };
	*	NestedWord<Character> nw2 = new NestedWord<Character>(testWord2, testRelation2);
	*	mLogger.info("Nested Word:  "+ nw.concatenate(nw2).toString());
	*/

	
	/**
	 * Print this nested word in style of a tagged alphabet [2].
	 * Every symbol (which is itself printed by its toString() method) at a call
	 * position is succeeded by <, every return is preceded by >.
	 * Remark: There is a bijection from nested words to words in this tagged
	 * alphabet style.
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (int i = 0; i<mWord.length; i++) {
			if (isInternalPosition(i)) {
				sb.append("\"");
				sb.append(getSymbolAt(i));
				sb.append("\"");
				sb.append(" ");
			}
			else if (isCallPosition(i)) {
				sb.append("\"");
				sb.append(getSymbolAt(i));
				sb.append("\"");
				sb.append("<");
				sb.append(" ");
			}
			else if (isReturnPosition(i)) {
				sb.append(">");
				sb.append("\"");
				sb.append(getSymbolAt(i));
				sb.append("\"");
				sb.append(" ");
			}
		}
		return sb.toString();
	}
	
	
	/**
	 * Return the subWord starting with firstIndex and lastIndex.
	 */
	public NestedWord<LETTER> subWord(int firstIndex, int lastIndex) {
		if (firstIndex < 0) {
			throw new IllegalArgumentException(
					"first index must be >=0");
		}
		if (firstIndex > lastIndex) {
			throw new IllegalArgumentException(
					"last index must be >= first index");
		}
		if (lastIndex >= length()) {
			throw new IllegalArgumentException(
					"last index must smaller strictly smaller than length");
		}
		final LETTER[] subWord = Arrays.copyOfRange(mWord, firstIndex, lastIndex+1);
		final int[] subNestingRelation = new int[lastIndex-firstIndex+1];
		for (int i = firstIndex; i<=lastIndex; i++) {
			int translatedNestingCode;
			if (mNestingRelation[i] == -2 || 
					mNestingRelation[i] == Integer.MIN_VALUE || 
					mNestingRelation[i] == Integer.MAX_VALUE) {
				translatedNestingCode = mNestingRelation[i];
			} else if (mNestingRelation[i] < firstIndex) {
				//becomes pending return
				assert mNestingRelation[i] >=0;
				translatedNestingCode = Integer.MIN_VALUE;
			} else if (mNestingRelation[i] > lastIndex) {
				//becomes pending call
				assert mNestingRelation[i] < length();
				translatedNestingCode = Integer.MAX_VALUE;
			} else {
				assert mNestingRelation[i] >= firstIndex && mNestingRelation[i] <= lastIndex;
				translatedNestingCode = mNestingRelation[i] - firstIndex;
			}
			subNestingRelation[i-firstIndex] = translatedNestingCode; 
		}
		assert subWord.length == subNestingRelation.length;
		return new NestedWord<LETTER>(subWord, subNestingRelation);
	}
}
