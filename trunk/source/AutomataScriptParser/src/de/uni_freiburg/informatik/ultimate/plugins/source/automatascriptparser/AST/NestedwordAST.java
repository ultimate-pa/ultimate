/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptParser plug-in.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AutomataScriptParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class NestedwordAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = 498949013884049199L;
	private final ArrayList<String> mWord;
	private int msizeOfWordSymbols;
	private final ArrayList<Integer> mNestingRelation;
	// Stack for positions of call symbols
	Deque<Integer> mCallPositions;
	
	// TODO: Following declaration must be removed when NestedWord
	// can be imported!
	
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
	
	public NestedwordAST(ILocation loc) {
		super(loc);
		mCallPositions = new ArrayDeque<Integer>();
		mWord = new ArrayList<String>();
		mNestingRelation = new ArrayList<Integer>();
		msizeOfWordSymbols = 0;
		setType(de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord.class);
	}
	
	public void addSymbol(CallSymbolAST c) {
		mCallPositions.push(msizeOfWordSymbols);
		mWord.add(c.getSymbol());
		// For each call symbol we assume it is a pending call.
		// If it is not, it is changed in the addSymbol(ReturnSymbol) method.
		mNestingRelation.add(PLUS_INFINITY);
		++msizeOfWordSymbols;
	}
	public void addSymbol(InternalSymbolAST c) {
		mWord.add(c.getSymbol());
		mNestingRelation.add(INTERNAL_POSITION);
		++msizeOfWordSymbols;

	}

	public void addSymbol(ReturnSymbolAST c) {
		final int positionOfThisSymbol = msizeOfWordSymbols;
		mWord.add(c.getSymbol());
		if (mCallPositions.isEmpty()) {
			mNestingRelation.add(MINUS_INFINITY);
		} else {
			final int posOfMatchingCall = mCallPositions.pop();
			mNestingRelation.add(posOfMatchingCall);
			mNestingRelation.set(posOfMatchingCall, positionOfThisSymbol);
		}
		++msizeOfWordSymbols;

	}
	
	/**
	 * Checks if this Nestedword is correct in the sense, that 
	 * - its NestingRelation values are in range,
	 * - it does not contain any crossing edges and
	 * - the nesting relation is symmetric 
	 * @return true iff the conditions above are all true, otherwise false
	 */
	public boolean isNestedWordCorrect() {
		final int[] nestingRelation = new int[mNestingRelation.size()];
		for (int i = 0; i < mNestingRelation.size(); i++) {
			nestingRelation[i] = mNestingRelation.get(i);
		}
		return (nestingRelationValuesInRange(nestingRelation) && nestingEdgesDoNotCross(nestingRelation) && nestingRelationSymmetricNestingEdges(nestingRelation) );
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("Nestedword [");
		for (int i = 0; i < msizeOfWordSymbols; i++) {
			if ((mNestingRelation.get(i) != INTERNAL_POSITION) && (mNestingRelation.get(i) < i)) {
				builder.append(">" + mWord.get(i));
			} else if (mNestingRelation.get(i) > i) {
				builder.append(mWord.get(i) + "<");
			} else {
				builder.append(mWord.get(i));
			}
			builder.append(" ");
		}
		builder.append("]");
		return builder.toString();
	}

	
	/*
	 * FIXME: Following methods are copied from nwalibrary.NestedWord, maybe they should be made
	 * public in NestedWord, so I can use them.
	 */
	
	 /** Checks if an int array is a possible candidate for a nesting relation.
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
	
	public String[] getWordSymbols() {
		final String[] symbols = new String[mWord.size()];
		for (int i = 0; i < mWord.size(); i++) {
			symbols[i] = mWord.get(i);
		}
		return symbols;
	}
	
	public int[] getNestingRelation() {
		final int[] nestingRelation = new int[mNestingRelation.size()];
		for (int i = 0; i < mNestingRelation.size(); i++) {
			nestingRelation[i] = mNestingRelation.get(i);
		}
		return nestingRelation;
	}

	@Override
	public String getAsString() {
		return toString().substring(11);
	}
	
	
}
