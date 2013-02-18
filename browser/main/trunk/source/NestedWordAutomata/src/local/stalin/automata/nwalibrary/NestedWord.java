package local.stalin.automata.nwalibrary;

import java.util.ArrayList;

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
 * of these objects is specified by the Symbol parameter.
 * 
 * We model the word of a nested word using an array of Symbols.
 * The (binary) nesting Relation is modeled by an int array m_NestingRelation
 * (that has the same length) the following way.
 * If i is an internal position m_NestingRelation[i] is INTERNAL_POSITION.
 * If i is a call position m_NestingRelation[i] is the position of the
 * corresponding return position and PLUS_INFINITY is it is a pending call.
 * If i is a return position m_NestingRelation[i] is the position of the
 * corresponding call position and MINUS_INFINITY is it is a pending return.
 * 
 * Example:
 * The nested word
 *                    (a b c d, {(0,2),(3,-infinity)} )
 * is modeled as
 *            m_Word = {'a',       'b'        ,'c'      'd' }
 * m_NestingRelation = { 2 , INTERNAL_POSITION, 0 , MINUS_INFINITY }
 * 
 * This model of a nesting relation wastes some memory if the nested word has 
 * only few calls and returns, but is very simple.
 * 
 * @param <Symbol>
 * 		Type of the Objects which can be symbols of the alphabet.
 */


public class NestedWord<Symbol> {
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
	

	private Symbol[] m_Word;
	private int[] m_NestingRelation;
	
	
	/**
	 * Constructor for NestedWord. The empty word is constructed by using two
	 * empty arrays as arguments.
	 * If the given arguments satisfy the definition of a nested word is checked
	 * by assert statements.
	 * To use exception for the case the definitions are violated would have
	 * been a nicer way of doing this. But I wanted to offer a fast way of
	 * constructing a nested word for users that are sure that their delivered
	 * arguments are valid. 
	 * @param word
	 * 		The (linear) word of a nested word.
	 * @param nestingRelation
	 * 		The nestingRelation of nested word.
	 */
	public NestedWord(Symbol[] word, int[] nestingRelation) {
		assert (word.length == nestingRelation.length) : 
				"nestingRelation must contain one entry for each Symbol in the word";
		assert (nestingRelationValuesInRange(nestingRelation)) : 
				"nestingRelation may contain one only -2, plus infinity, minus infinity or natural numbers";
		assert (nestingRelationSymmetricNestingEdges(nestingRelation)) : 
				"if nestingRelation[i]=k then nestingRelation[k]=i or nestingRelation[i] is either" +
				"plus infinity, minus infinity or internal position";
		assert (nestingEdgesDoNotCross(nestingRelation)) : 
				"nesting edges must not cross";
		this.m_Word = word;
	    this.m_NestingRelation = nestingRelation;	
	}
	
	public NestedWord() {
		ArrayList<Symbol> al = new ArrayList<Symbol>(0);
		this.m_Word = (Symbol[]) al.toArray();
		int[] nr = { };
		this.m_NestingRelation = nr;
	}
	
	/**
	 * Word of length one
	 * @param symbol
	 */
	public NestedWord(Symbol symbol) {
		ArrayList<Symbol> al = new ArrayList<Symbol>(1);
		al.add(symbol);
		this.m_Word = (Symbol[]) al.toArray();
		int[] nr = { INTERNAL_POSITION };
		this.m_NestingRelation = nr;
	}
	
	public NestedWord(Symbol[] word) {
		this.m_Word = word;
		this.m_NestingRelation = new int[0];
	}
	
	
	private Symbol[] getWord() {
		return this.m_Word;
	}
	
	private int[] getNestingRelation() {
		return this.m_NestingRelation;
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
	public int length() {
		return m_Word.length;
	}
	
	
	public boolean isCallPosition(int i) {
		assert (0<=i) : "Access to position " + i + " not possible. The first position of a nested word is 0";
		assert (i<=this.m_Word.length) : "Access to position " + i + " not possible. The last positions of this word is " + (m_Word.length-1);
		if (m_NestingRelation[i] >=i) 
			return true;
		else 
			return false;
	}
	
	
	public boolean isInternalPosition(int i) {
		assert (0<=i) : "Access to position " + i + " not possible. The first position of a nested word is 0";
		assert (i<=this.m_Word.length) : "Access to position " + i + " not possible. The last positions of this word is " + (m_Word.length-1);
		if (m_NestingRelation[i] == INTERNAL_POSITION) 
			return true;
		else 
			return false;
	}
	
	
	public boolean isReturnPosition(int i) {
		assert (0<=i) : "Access to position " + i + " not possible. The first position of a nested word is 0";
		assert (i<=this.m_Word.length) : "Access to position " + i + " not possible. The last positions of this word is " + (m_Word.length-1);
		if (m_NestingRelation[i] <=i && m_NestingRelation[i] != INTERNAL_POSITION) 
			return true;
		else 
			return false;
	}
	
	
	public Symbol getSymbolAt(int position) 
	{
		assert(position >= 0 && position < m_Word.length);
		return m_Word[position];
	}
	
	
	public int getReturnPosition(int i) {
		if (isCallPosition(i)) {
			return m_NestingRelation[i];
		}
		else {
			throw new IllegalArgumentException("Argument must be call position");
		}
	}
	
	
	public int getCallPosition(int i) {
		if (isReturnPosition(i)) {
			return m_NestingRelation[i];
		}
		else {
			throw new IllegalArgumentException("Argument must be return position");
		}
	}
	
	public boolean isPendingCall(int i) {
		if (m_NestingRelation[i] == PLUS_INFINITY) {
			return true;
		}
		else 
			return false;
	}
	
	public boolean isPendingReturn(int i) {
		if (m_NestingRelation[i] == MINUS_INFINITY) {
			return true;
		}
		else 
			return false;
	}
	
	public boolean containsPendingReturns() {
		boolean result = false;
		for (int i=0; i<this.length(); i++) {
			result = result || isPendingReturn(i);
		}
		return result;
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
	public NestedWord<Symbol> concatenate(NestedWord<Symbol> nestedWord2) {
		Symbol[] word2 = nestedWord2.getWord();
		int[] nestingRelation2 = nestedWord2.getNestingRelation();
		int[] concatNestingRelation = new int[m_Word.length+word2.length];
		int i = m_Word.length -1;
		int j = 0;
		while (i>=0) {
			if (m_NestingRelation[i]!=PLUS_INFINITY) {
				concatNestingRelation[i]=m_NestingRelation[i];
			}
			else {
				while (j<nestingRelation2.length && nestingRelation2[j]!=MINUS_INFINITY) {
					if (nestingRelation2[j]==INTERNAL_POSITION) {
						concatNestingRelation[m_Word.length+j]=INTERNAL_POSITION;
					}
					else if (nestingRelation2[j]==PLUS_INFINITY) {
						concatNestingRelation[m_Word.length+j]=PLUS_INFINITY;
					}
					else {
					concatNestingRelation[m_Word.length+j]=m_Word.length+nestingRelation2[j];
					}
					j++;
				}

				if (j!=word2.length) {
					concatNestingRelation[i]=m_Word.length+j;
					concatNestingRelation[m_Word.length+j]=i;
					j++;
				}
				else {
					concatNestingRelation[i]=m_NestingRelation[i];
				}
			}
			i--;
		}
		while (j<nestingRelation2.length) {
			if (nestingRelation2[j]==INTERNAL_POSITION) {
				concatNestingRelation[m_Word.length+j]=INTERNAL_POSITION;
			}
			else if (nestingRelation2[j]==PLUS_INFINITY) {
				concatNestingRelation[m_Word.length+j]=PLUS_INFINITY;
			}
			else if (nestingRelation2[j]==MINUS_INFINITY) {
				concatNestingRelation[m_Word.length+j]=MINUS_INFINITY;
			}
			else {
			concatNestingRelation[m_Word.length+j]=m_Word.length+nestingRelation2[j];
			}
			j++;
		}
		
		Symbol[] concatWord = (Symbol[]) new Object[m_Word.length+word2.length];
		System.arraycopy(m_Word, 0, concatWord, 0, m_Word.length);
		System.arraycopy(word2, 0, concatWord, m_Word.length, word2.length);
		
		return new NestedWord<Symbol>(concatWord,concatNestingRelation);
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
	*	s_Logger.info("Nested Word:  "+ nw.concatenate(nw2).toString());
	*/

	
	/**
	 * Print this nested word in style of a tagged alphabet [2].
	 * Every symbol (which is itself printed by its toString() method) at a call
	 * position is succeeded by <, every return is preceded by >.
	 * Remark: There is a bijection from nested words to words in this tagged
	 * alphabet style.
	 */
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i<m_Word.length; i++) {
			if (isInternalPosition(i)) {
				sb.append(getSymbolAt(i)+" ");
			}
			else if (isCallPosition(i)) {
				sb.append(getSymbolAt(i)+"< ");
			}
			else if (isReturnPosition(i)) {
				sb.append(">" + getSymbolAt(i) + " ");
			}
		}
		return sb.toString();
	}
}
