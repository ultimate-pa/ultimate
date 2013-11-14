package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.*;

/**
 * This class is used to convert a resolution proof step.
 * 
 * @author Christian Schilling
 */
public class ResolutionConverter extends AConverter {
	// true iff fast proofs shall be printed
	private final boolean m_fastProofs;
	// appendable for the lemmata
	private final Appendable m_lemmaAppendable;
	// map from pattern to lemma number
	private final HashMap<ResolutionPattern, Integer> m_pattern2lemma;
	// number of lemmata already proven
	private int m_lemmaCount;
	
	// prefix resolution placeholder variables use
	private static final String RESOLUTION_L_PREFIX = "l";
	private static final String RESOLUTION_C_PREFIX = "c";
	private static final String RESOLUTION_R_PREFIX = "r";
	private static final String RESOLUTION_PIVOT_L = "pl";
	private static final String RESOLUTION_PIVOT_R = "pr";
	
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 * @param fastProofs true iff fast proofs shall be printed
	 * @param lemmaAppendable the theory file for the lemmata
	 */
	public ResolutionConverter(final Appendable appendable,
			final Theory theory, final TermConverter converter,
			final ComputationSimplifier simplifier, final boolean fastProofs,
			final Appendable lemmaAppendable) {
		super(appendable, theory, converter, simplifier);
		m_fastProofs = fastProofs;
		m_pattern2lemma = new HashMap<ResolutionPattern, Integer>();
		m_lemmaAppendable = lemmaAppendable;
		m_lemmaCount = 0;
	}
	
	/**
	 * This method creates the resolution result.
	 * 
	 * It first detects if the proof pattern already exists and in this case
	 * just prints a proof by the lemma. Else a new lemma is written.
	 * In both cases the result has to be computed anyway, since the other
	 * resolution proofs need the information.
	 * 
	 * @param first the first (possibly singleton) disjunction
	 * @param second the second (possibly singleton) disjunction
	 * @param pivot the pivot
	 * @return the resulting (possibly singleton or 0-ary) disjunction
	 */
	public Term convert(final Term first, final Term second,
			final Term pivot) {
		// create a pattern
		final PatternSwapWrapper wrapper = createWrapper(first, second, pivot);
		
		// check if the lemma was already proven
		Integer lemmaNumber =
				wrapper.isStoreCandidate()
				? m_pattern2lemma.get(wrapper.m_patternWrap)
				: null;
		
		// lemma is new, create it
		if (lemmaNumber == null) {
			lemmaNumber = ++m_lemmaCount;
			createLemma(wrapper, lemmaNumber);
			
			// store the lemma if it is small enough
			if (wrapper.isStoreCandidate()) {
				m_pattern2lemma.put(wrapper.m_patternWrap, lemmaNumber);
			}
		}
		
		final Term result = createResult(wrapper.m_patternWrap,
				wrapper.m_swap ? second : first,
				wrapper.m_swap ? first : second,
						wrapper.m_sharedTerms.length);
		
		// write the proof by lemma to the file
		writeProof(wrapper.m_swap, wrapper.m_doubleNegation, lemmaNumber,
				result);
		
		return result;
	}
	
	/**
	 * This method creates the pattern data structure. This is used for both
	 * checking if the lemma has already been proven and for creating a new
	 * lemma.
	 * 
	 * @param first the first disjunction
	 * @param second the second disjunction
	 * @param pivot the pivot
	 * @return a wrapper with the pattern and swapping information 
	 */
	private PatternSwapWrapper createWrapper(Term first, Term second,
			final Term pivot) {
		// find out the size
		int firstSize = 1, secondSize = 1;
		if (first instanceof ApplicationTerm) {
			if (((ApplicationTerm)first).getFunction() == m_theory.m_Or) {
				firstSize = ((ApplicationTerm)first).getParameters().length;
			}
		}
		else {
			assert ((first instanceof AnnotatedTerm) &&
					(((AnnotatedTerm)first).getAnnotations().length == 1)
					&&
					(((AnnotatedTerm)first).getAnnotations()[0].getKey() ==
							":quoted"));
		}
		if (second instanceof ApplicationTerm) {
			if (((ApplicationTerm)second).getFunction() == m_theory.m_Or) {
				secondSize = ((ApplicationTerm)second).getParameters().length;
			}
		}
		else {
			assert ((second instanceof AnnotatedTerm) &&
					(((AnnotatedTerm)second).getAnnotations().length == 1)
					&&
					(((AnnotatedTerm)second).getAnnotations()[0].getKey() ==
							":quoted"));
		}
		
		// make sure the first term is the bigger one
		final Term pivotFirst, pivotSecond;
		final boolean swap;
		boolean isNegated = isNegated(pivot);
		if (firstSize < secondSize) {
			swap = true;
			
			final Term tmpT = first;
			final int tmpI = firstSize;
			first = second;
			firstSize = secondSize;
			second = tmpT;
			secondSize = tmpI;
			
			pivotFirst = pivot;
			if (isNegated) {
				pivotSecond = ((ApplicationTerm)pivot).getParameters()[0];
			}
			else {
				pivotSecond = m_theory.term(m_theory.m_Not, pivot);
			}
			isNegated = (! isNegated);
		}
		else {
			swap = false;
			
			if (isNegated) {
				pivotFirst = ((ApplicationTerm)pivot).getParameters()[0];
			}
			else {
				pivotFirst = m_theory.term(m_theory.m_Not, pivot);
			}
			pivotSecond = pivot;
		}
		
		assert ((firstSize > 0) && (secondSize > 0));
		
		// check that the pivot is contained
		assert checkPivotContainment(first, second, pivotFirst, pivotSecond,
				firstSize, secondSize);
		
		// find pivot in P
		final int plIndex;
		if (firstSize == 1) {
			assert (first == pivotFirst) :
				"A singleton clause must be the (correctly negated) pivot.";
			plIndex = 0;
		}
		else {
			assert ((first instanceof ApplicationTerm) &&
					(((ApplicationTerm)first).getFunction() == m_theory.m_Or));
			plIndex = findPivot(((ApplicationTerm)first).getParameters(),
					pivotFirst);
		}
		
		// create pattern only for Q
		final PatternSharedWrapper wrapper = createQPattern(
				firstSize == 1
						? null
						: ((ApplicationTerm)first).getParameters(),
				second, secondSize, plIndex, pivotSecond);
		
		return new PatternSwapWrapper(
				new ResolutionPattern(firstSize, plIndex, wrapper.m_pattern),
				wrapper.m_sharedTerms, swap, (! isNegated));
	}
	
	/**
	 * This method checks if the pivot is negated.
	 * 
	 * @param pivot the pivot
	 * @return true iff the pivot is negated
	 */
	private boolean isNegated(final Term pivot) {
		if (pivot instanceof ApplicationTerm) {
			if (((ApplicationTerm)pivot).getFunction() == m_theory.m_Not) {
				assert (((ApplicationTerm)pivot).getParameters().length == 1);
				return true; 
			}
		}
		return false;
	}
	
	/**
	 * This method finds the index of the pivot.
	 * 
	 * @param disjuncts the disjuncts
	 * @param pivot the pivot
	 * @return the index of the pivot in the disjunction
	 */
	private int findPivot(final Term[] disjuncts,
			final Term pivot) {
		assert (disjuncts.length > 1);
		for (int i = disjuncts.length - 1; i >= 0; --i) {
			if (disjuncts[i] == pivot) {
				return i;
			}
		}
		throw new IllegalArgumentException("The pivot was not found.");
	}
	
	/**
	 * This method creates the pattern for the second disjunction.
	 * 
	 * @param first the disjuncts of the first disjunction
	 * @param second the second disjunction
	 * @param secondSize the size of the second disjunction
	 * @param plIndex the index of the pivot in the first disjunction
	 * @param pivot the pivot in the second disjunction
	 * @return the partial pattern wrapper with the pattern and shared terms
	 */
	private PatternSharedWrapper createQPattern(final Term[] first,
			final Term second, final int secondSize, final int plIndex,
			final Term pivot) {
		final int[] result = new int[secondSize];
		final int[] sharedTerms;
		
		// trivial case
		if (secondSize == 1) {
			assert (second == pivot) :
				"A singleton clause must be the (correctly negated) pivot.";
			result[0] = -1;
			sharedTerms = new int[0];
		}
		else {
			assert (second instanceof ApplicationTerm);
			final Term[] qDisjuncts =
					((ApplicationTerm)second).getParameters();
			assert (qDisjuncts.length == secondSize);
			assert ((first != null) && (first.length > 1));
			
			// create a mapping from terms in the first disjunction
			HashMap<Term, Integer> disjunct2index =
					new HashMap<Term, Integer>((int)(first.length / 0.75) + 1);
			for (int i = first.length - 1; i > plIndex; --i) {
				disjunct2index.put(first[i], i);
			}
			for (int i = plIndex - 1; i >= 0; --i) {
				disjunct2index.put(first[i], i);
			}
			
			assert checkForDuplicates(disjunct2index.size(), first.length,
					qDisjuncts);
			
			// create Q pattern
			int index = first.length - 1;
			ArrayList<Integer> shared =
					new ArrayList<Integer>(secondSize);
			int i = -1;
			while (++i < qDisjuncts.length) {
				final Term disjunct = qDisjuncts[i];
				if (disjunct == pivot) {
					break;
				}
				
				final Integer oldIndex = disjunct2index.get(disjunct);
				if (oldIndex == null) {
					result[i] = ++index;
				}
				else {
					result[i] = oldIndex;
					shared.add(oldIndex);
				}
			}
			result[i] = -1;
			while (++i < qDisjuncts.length) {
				final Integer oldIndex = disjunct2index.get(qDisjuncts[i]);
				if (oldIndex == null) {
					result[i] = ++index;
				}
				else {
					result[i] = oldIndex;
					shared.add(oldIndex);
				}
			}
			
			sharedTerms = new int[shared.size()];
			i = -1;
			for (Integer j : shared) {
				assert (i < sharedTerms.length - 1);
				sharedTerms[++i] = j;
			}
			assert (i == sharedTerms.length - 1);
		}
		return new PatternSharedWrapper(result, sharedTerms);
	}
	
	/**
	 * This method creates the lemma for the pattern. It constructs the
	 * necessary pattern disjunctions and the result and calls the writing
	 * method.
	 * 
	 * @param wrapper the pattern wrapper
	 * @param lemmaNummer the new lemma number
	 */
	private void createLemma(final PatternSwapWrapper wrapper,
			final int lemmaNummer) {
		final Term[] first = new Term[wrapper.m_patternWrap.m_pLength];
		final int[] qPattern =  wrapper.m_patternWrap.m_pattern;
		final Term[] second = new Term[qPattern.length];
		final Term[] resultDisj = new Term[first.length + second.length -
		                                   wrapper.m_sharedTerms.length - 2];
		
		// sort shared terms array in ascending order
		final int[] sharedTerms = wrapper.m_sharedTerms;
		Arrays.sort(sharedTerms);
		
		/* create disjunction objects */
		final Term[] params = new Term[0];
		final Sort[] paramSorts = new Sort[0];
		final Term pivotFirst =
				getTerm(RESOLUTION_PIVOT_L, params, paramSorts);
		final Term pivotSecond =
				getTerm(RESOLUTION_PIVOT_R, params, paramSorts);
		
		// first disjunction
		final int pivotIndex = wrapper.m_patternWrap.m_plIndex;
		first[pivotIndex] = pivotFirst;
		if (sharedTerms.length == 0) {
			for (int i = 0; i < pivotIndex; ++i) {
				final Term term =
						getTerm(RESOLUTION_L_PREFIX + i, params, paramSorts);
				first[i] = term;
				resultDisj[i] = term;
			}
			for (int i = pivotIndex + 1; i < first.length; ++i) {
				final Term term =
						getTerm(RESOLUTION_L_PREFIX + i, params, paramSorts);
				first[i] = term;
				resultDisj[i - 1] = term;
			}
		}
		else {
			int sharedIndex = 0;
			int nextShared = sharedTerms[0];
			
			int resultL = -1;
			int resultC = first.length - wrapper.m_sharedTerms.length - 2;
			for (int i = 0; i < pivotIndex; ++i) {
				// term shared in both disjunctions
				if (i == nextShared) {
					final Term term = getTerm(RESOLUTION_C_PREFIX + i, params,
							paramSorts);
					first[i] = term;
					resultDisj[++resultC] = term;
					if (sharedIndex < sharedTerms.length - 1) {
						nextShared = sharedTerms[++sharedIndex];
					}
				}
				// term only in the first disjunction
				else {
					final Term term = getTerm(RESOLUTION_L_PREFIX + i, params,
							paramSorts);
					first[i] = term;
					resultDisj[++resultL] = term;
				}
			}
			for (int i = pivotIndex + 1; i < first.length; ++i) {
				// term shared in both disjunctions
				if (i == nextShared) {
					final Term term = getTerm(RESOLUTION_C_PREFIX + i, params,
							paramSorts);
					first[i] = term;
					resultDisj[++resultC] = term;
					if (sharedIndex < sharedTerms.length - 1) {
						nextShared = sharedTerms[++sharedIndex];
					}
				}
				// term only in the first disjunction
				else {
					final Term term = getTerm(RESOLUTION_L_PREFIX + i, params,
							paramSorts);
					first[i] = term;
					resultDisj[++resultL] = term;
				}
			}
		}
		// second disjunction
		int i = 0;
		int resultR = first.length - 2;
		for (; i < qPattern.length; ++i) {
			final int patternIndex = qPattern[i];
			
			if (patternIndex < first.length) {
				// pivot
				if (patternIndex == -1) {
					second[i] = pivotSecond;
					++i;
					break;
				}
				// term shared in both disjunctions
				else {
					second[i] = getTerm(RESOLUTION_C_PREFIX + patternIndex,
							params, paramSorts);
				}
			}
			// term only in the second disjunction
			else {
				final Term term = getTerm(RESOLUTION_R_PREFIX + patternIndex,
						params, paramSorts);
				second[i] = term;
				resultDisj[++resultR] = term;
			}
		}
		for (; i < qPattern.length; ++i) {
			final int patternIndex = qPattern[i];
			
			// term shared in both disjunctions
			if (patternIndex < first.length) {
				assert (patternIndex > -1);
				second[i] = getTerm(RESOLUTION_C_PREFIX + patternIndex,
						params, paramSorts);
			}
			// term only in the second disjunction
			else {
				final Term term = getTerm(RESOLUTION_R_PREFIX + patternIndex,
						params, paramSorts);
				second[i] = term;
				resultDisj[++resultR] = term;
			}
		}
		
		// write the lemma proof
		writeLemmaProof(first, second, resultDisj, pivotFirst,
				pivotSecond, lemmaNummer);
	}
	
	/**
	 * This method creates a new term given the function name and the
	 * parameters.
	 * 
	 * @param name function name
	 * @param parameters parameters
	 * @param parameterSorts parameter sorts
	 * @return ApplicationTerm with the function and the parameters
	 */
	private ApplicationTerm getTerm(final String name, final Term[] parameters,
			final Sort[] parameterSorts) {
		ApplicationTerm result = m_theory.term(name, parameters);
		
		if (result == null) {
			return m_theory.term(
					m_theory.declareFunction(
							name, parameterSorts, m_theory.getBooleanSort()),
					parameters);
		}
		
		return result;
	}
	
	/**
	 * This method is only used for asserting that the pivot is contained in
	 * both disjunctions.
	 * 
	 * @param first the bigger disjunction
	 * @param second the smaller disjunction
	 * @param pivotFirst the first pivot
	 * @param pivotSecond the second pivot 
	 * @param firstSize the size of the first term
	 * @param secondSize the size of the second term
	 * @return true
	 * @throws AssertionError iff pivot is not found
	 */
	private boolean checkPivotContainment(final Term first, final Term second,
			final Term pivotFirst, final Term pivotSecond,
			final int firstSize, final int secondSize) throws AssertionError {
		if (firstSize == 1) {
			assert (first == pivotFirst) :
				"A singleton clause must be the (correctly negated) pivot.";
		}
		else {
			assert ((first instanceof ApplicationTerm) &&
					(((ApplicationTerm)first).getFunction() == m_theory.m_Or));
			assert (findPivot(((ApplicationTerm)first).getParameters(),
					pivotFirst) >= 0);
		}
		
		if (secondSize == 1) {
			assert (second == pivotSecond) :
				"A singleton clause must be the (correctly negated) pivot.";
		}
		else {
			assert ((second instanceof ApplicationTerm) &&
					(((ApplicationTerm)second).getFunction() ==
							m_theory.m_Or));
			assert (findPivot(((ApplicationTerm)second).getParameters(),
					pivotSecond) >= 0);
		}
		
		
		return true;
	}
	
	/**
	 * This method is only used for asserting that the disjunction does not
	 * contain any duplicates.
	 * 
	 * @param mapSize size of the map for the first disjunction (without pivot)
	 * @param firstLength length of the first disjunction
	 * @param qDisjuncts the second disjunction
	 * @return true iff there are no duplicates
	 */
	private boolean checkForDuplicates(final int mapSize,
			final int firstLength, final Term[] qDisjuncts) {
		if (mapSize != firstLength - 1) {
			return false;
		}
		HashSet<Term> set = new HashSet<Term>(
				(int)(qDisjuncts.length / 0.75) + 1);
		for (Term disjunct : qDisjuncts) {
			set.add(disjunct);
		}
		return (set.size() == qDisjuncts.length);
	}
	
	/**
	 * This method writes the lemma to the lemma appendable.
	 * 
	 * @param first the first disjuncts
	 * @param second the second disjuncts
	 * @param result the result disjuncts
	 * @param pivotFirst pattern pivot in the first term
	 * @param pivotSecond pattern pivot in the second term
	 * @param lemmaNumber the lemma number
	 */
	private void writeLemmaProof(final Term[] first, final Term[] second,
			final Term[] result, final Term pivotFirst,
			final Term pivotSecond, final int lemmaNumber) {
		final FunctionSymbol or = m_theory.m_Or;
		final Term firstDisjunction = (first.length == 1)
				? first[0]
				: m_theory.term(or, first);
		final Term secondDisjunction = (second.length == 1)
				? second[0]
				: m_theory.term(or, second);
		final Term resultDisjunction = (result.length == 0)
				? m_theory.FALSE
				: (result.length == 1)
						? result[0]
						: m_theory.term(or, result);
				
		// head line
		writeLemmaString("\nlemma ");
		writeLemmaString(RESOLUTION_LEMMA_PREFIX);
		writeLemmaString(Integer.toString(lemmaNumber));
		writeLemmaString(": \"[|");
		m_converter.convertToAppendable(firstDisjunction, m_lemmaAppendable);
		writeLemmaString("; ");
		m_converter.convertToAppendable(secondDisjunction, m_lemmaAppendable);
		writeLemmaString("; (~ ");
		m_converter.convertToAppendable(pivotFirst, m_lemmaAppendable);
		writeLemmaString(") = ");
		m_converter.convertToAppendable(pivotSecond, m_lemmaAppendable);
		writeLemmaString("|] ==> ");
		m_converter.convertToAppendable(resultDisjunction, m_lemmaAppendable);
		writeLemmaString("\"\n");
		
		/* proof */
		
		// both disjunctions consist of only the pivot
		if (first.length == 1) {
			writeLemmaString("by (rule res_false)\n");
			return;
		}
		
		// strings for fast and slow proofs
		final String next = ")\nby (";
		final String finish = ") +\n";
		writeLemmaString("apply (erule (2) res_");
		
		final int sharedCount =
				first.length + second.length - result.length - 2;
		
		// shared terms exist
		if (sharedCount > 0) {
			// only shared terms (C terms)
			if (first.length == sharedCount + 1) {
				writeLemmaString("c");
				writeLemmaString(next);
				writeLemmaString(
						"simp only: HOL.disj_commute HOL.disj_left_commute");
				writeLemmaString(finish);
			}
			// second disjunction only contains shared terms (L and C terms)
			else if (second.length == sharedCount + 1) {
				writeLemmaString("lc [where l = \"");
				final Term[] lTerms = getLTerms(result, first.length,
						sharedCount);
				m_converter.convertToAppendable(
						(lTerms.length == 1)
								? lTerms[0]
								: m_theory.term(or, lTerms),
						m_lemmaAppendable);
				writeLemmaString("\" and c = \"");
				final Term[] cTerms = getCTerms(result, first.length,
						sharedCount);
				m_converter.convertToAppendable(
						(cTerms.length == 1)
								? cTerms[0]
								: m_theory.term(or, cTerms),
						m_lemmaAppendable);
				writeLemmaString("\"]");
				writeLemmaString(next);
				writeLemmaString("simp only: HOL.disj_commute " +
						"HOL.disj_left_commute HOL.disj_assoc");
				writeLemmaString(finish);
			}
			// L, C, and R terms
			else {
				writeLemmaString("lcr [where l = \"");
				final Term[] lTerms = getLTerms(result, first.length,
						sharedCount);
				m_converter.convertToAppendable(
						lTerms.length == 1
								? lTerms[0]
								: m_theory.term(or, lTerms),
						m_lemmaAppendable);
				writeLemmaString("\" and c = \"");
				final Term[] cTerms = getCTerms(result, first.length,
						sharedCount);
				m_converter.convertToAppendable(
						cTerms.length == 1
								? cTerms[0]
								: m_theory.term(or, cTerms),
						m_lemmaAppendable);
				writeLemmaString("\" and r = \"");
				final Term[] rTerms = getRTerms(result, second.length,
						sharedCount);
				m_converter.convertToAppendable(
						rTerms.length == 1
								? rTerms[0]
								: m_theory.term(or, rTerms),
						m_lemmaAppendable);
				writeLemmaString("\"]");
				writeLemmaString(next);
				writeLemmaString("simp only: HOL.disj_commute " +
						"HOL.disj_left_commute HOL.disj_assoc");
				writeLemmaString(finish);
			}
		}
		// no shared terms exist
		else {
			// only the disjuncts from the first disjunction (L terms)
			if (second.length == 1) {
				writeLemmaString("l");
				writeLemmaString(next);
				writeLemmaString(
						"simp only: HOL.disj_commute HOL.disj_left_commute");
				writeLemmaString(finish);
			}
			// L and R terms
			else {
				writeLemmaString("lr [where l = \"");
				final Term[] lTerms = getLTerms(result, first.length,
						sharedCount);
				m_converter.convertToAppendable(
						lTerms.length == 1
								? lTerms[0]
								: m_theory.term(or, lTerms),
						m_lemmaAppendable);
				writeLemmaString("\" and r = \"");
				final Term[] rTerms = getRTerms(result, second.length,
						sharedCount);
				m_converter.convertToAppendable(
						rTerms.length == 1
								? rTerms[0]
								: m_theory.term(or, rTerms),
						m_lemmaAppendable);
				writeLemmaString("\"]");
				writeLemmaString(next);
				writeLemmaString("simp only: HOL.disj_commute " +
						"HOL.disj_left_commute HOL.disj_assoc");
				writeLemmaString(finish);
			}
		}
	}
	
	/**
	 * This method extracts the L terms from the result.
	 * 
	 * @param result the result disjunction
	 * @param length length of the first disjunction
	 * @param sharedCount length of the shared terms
	 * @return array with the L terms
	 */
	private Term[] getLTerms(final Term[] result, final int length,
			final int sharedCount) {
		final Term[] lTerms = new Term[length - sharedCount - 1];
		assert (lTerms.length <= result.length);
		for (int i = 0; i < lTerms.length; ++i) {
			lTerms[i] = result[i];
		}
		return lTerms;
	}
	
	/**
	 * This method extracts the C terms from the result.
	 * 
	 * @param result the result disjunction
	 * @param length length of the first disjunction
	 * @param sharedCount length of the shared terms
	 * @return array with the C terms
	 */
	private Term[] getCTerms(final Term[] result, final int length,
			final int sharedCount) {
		final int offset = length - sharedCount - 1;
		final Term[] cTerms = new Term[sharedCount];
		for (int i = 0; i < cTerms.length; ++i) {
			cTerms[i] = result[i + offset];
		}
		return cTerms;
	}
	
	/**
	 * This method extracts the R terms from the result.
	 * 
	 * @param result the result disjunction
	 * @param length length of the second disjunction
	 * @param sharedCount length of the shared terms
	 * @return array with the R terms
	 */
	private Term[] getRTerms(final Term[] result, final int length,
			final int sharedCount) {
		final int offset = result.length - length + sharedCount + 1;
		final Term[] rTerms = new Term[length - sharedCount - 1];
		for (int i = 0; i < rTerms.length; ++i) {
			rTerms[i] = result[i + offset];
		}
		return rTerms;
	}
	
	/**
	 * This method creates the result disjunction.
	 * 
	 * @param pattern the pattern
	 * @param first the first term
	 * @param second the second term
	 * @return the result term
	 */
	private Term createResult(final ResolutionPattern pattern,
			final Term first, final Term second, final int sharedLength) {
		final int firstSize = pattern.m_pLength;
		// both disjunctions consist of only the pivot
		if (firstSize == 1) {
			return m_theory.FALSE;
		}
		
		final FunctionSymbol or = m_theory.m_Or;
		final int secondSize = pattern.m_pattern.length;
		assert ((first instanceof ApplicationTerm) &&
				(((ApplicationTerm)first).getFunction() == or) &&
				(((ApplicationTerm)first).getParameters().length > 1));
		final Term[] firstDisjuncts = ((ApplicationTerm)first).getParameters();
		
		// only the disjuncts from the first disjunction (without the pivot)
		if (secondSize == 1) {
			if (firstSize == 2) {
				return firstDisjuncts[1 - pattern.m_plIndex];
			}
			
			final Term[] disjuncts = new Term[firstSize - 1];
			assert ((firstSize > 2) && (disjuncts.length > 1));
			for (int i = 0; i < pattern.m_plIndex; ++i) {
				disjuncts[i] = firstDisjuncts[i];
			}
			for (int i = pattern.m_plIndex + 1; i < firstSize; ++i) {
				disjuncts[i - 1] = firstDisjuncts[i];
			}
			return m_theory.term(or, disjuncts);
		}
		
		assert ((second instanceof ApplicationTerm) &&
				(((ApplicationTerm)second).getFunction() == or) &&
				(((ApplicationTerm)second).getParameters().length > 1));
		final Term[] secondDisjuncts =
				((ApplicationTerm)second).getParameters();
				
		final Term[] disjuncts =
				new Term[firstSize + secondSize -
				         sharedLength - 2];
		assert (disjuncts.length > 0);
		
		// add R terms and find C terms
		int rIndex = firstSize - 2;
		final int[] qPattern = pattern.m_pattern;
		ArrayList<Integer> sharedList =
				new ArrayList<Integer>(secondDisjuncts.length);
		int i = 0;
		for (; i < secondSize; ++i) {
			final int patternIndex = qPattern[i];
			if (patternIndex < firstSize) {
				// pivot
				if (patternIndex == -1) {
					++i;
					break;
				}
				// shared term
				else {
					sharedList.add(patternIndex);
				}
			}
			// R term
			else {
				disjuncts[++rIndex] = secondDisjuncts[i];
				assert (rIndex < disjuncts.length);
			}
		}
		for (; i < secondSize; ++i) {
			final int patternIndex = qPattern[i];
			if (patternIndex < firstSize) {
				assert (patternIndex > -1);
				// shared term
				sharedList.add(patternIndex);
			}
			// R term
			else {
				disjuncts[++rIndex] = secondDisjuncts[i];
				assert (rIndex < disjuncts.length);
			}
		}
		
		// no shared terms, faster implementation
		if (sharedList.size() == 0) {
			for (int j = 0; j < pattern.m_plIndex; ++j) {
				disjuncts[j] = firstDisjuncts[j];
			}
			for (int j = pattern.m_plIndex + 1; j < firstSize; ++j) {
				disjuncts[j - 1] = firstDisjuncts[j];
			}
			return m_theory.term(or, disjuncts);
		}
		
		// sort shared terms indices
		Integer[] shared = new Integer[sharedList.size()];
		assert (shared.length == sharedLength);
		sharedList.toArray(shared);
		Arrays.sort(shared);
		
		// add L and C terms
		int sharedIndex = 0;
		int currentShared = shared[0];
		int lIndex = -1;
		int cIndex = firstSize - shared.length - 2;
		i = 0;
		for (; i < firstSize; ++i) {
			if (i == pattern.m_plIndex) {
				continue;
			}
			if (i == currentShared) {
				disjuncts[++cIndex] = firstDisjuncts[i];
				assert (cIndex < firstSize);
				if (++sharedIndex < shared.length) {
					currentShared = shared[sharedIndex];
				}
				else {
					++i;
					break;
				}
			}
			else {
				disjuncts[++lIndex] = firstDisjuncts[i];
				assert (lIndex < firstSize - shared.length);
			}
		}
		for (; i < pattern.m_plIndex; ++i) {
			disjuncts[++lIndex] = firstDisjuncts[i];
			assert (lIndex < firstSize - shared.length);
		}
		if (i == pattern.m_plIndex) {
			++i;
		}
		for (; i < firstSize; ++i) {
			disjuncts[++lIndex] = firstDisjuncts[i];
			assert (lIndex < firstSize - shared.length);
		}
		
		return (disjuncts.length == 1)
				? disjuncts[0]
				: m_theory.term(or, disjuncts);
	}
	
	/**
	 * This method writes the proof of the lemma in the main file.
	 * 
	 * @param swap true iff arguments were swapped
	 * @param doubleNegation true iff pivot is doubly negated
	 * @param lemmaNumber number of the lemma
	 * @param result the result term
	 */
	private void writeProof(final boolean swap, final boolean doubleNegation,
			final Integer lemmaNumber, final Term result) {
		m_converter.convert(result);
		writeString("\"\napply ");
		// swap
		if (swap) {
			writeString("rotate_tac\n");
			
			if (m_fastProofs) {
				writeString("by (erule (1) ");
			}
			else {
				writeString("apply (erule (1) ");
			}
		}
		// no swap
		else {
			writeString("(rule ");
		}
		
		// lemma
		writeString(RESOLUTION_LEMMA_PREFIX);
		writeString(Integer.toString(lemmaNumber));
		
		// finishing
		if (swap && m_fastProofs) {
			writeString(", rule ");
		}
		else {
			writeString(")\nby (rule ");
		}
		if (doubleNegation) {
			writeString("HOL.not_not)\n");
		}
		else {
			writeString("HOL.refl)\n");
		}
	}
	
	/**
	 * This class contains the minimal information necessary to discriminate
	 * two different proof patterns. It contains the length and the position of
	 * the pivot in the first disjunction and the whole pattern of the second
	 * disjunction.
	 * This makes the construction of the result term slightly more difficult,
	 * but saves memory, which should be more important, since all patterns are
	 * stored in a global hash map.
	 */
	private class ResolutionPattern {
		// length of the P
		private final int m_pLength;
		// index of the pivot in P
		private final int m_plIndex;
		// wrapper with pattern of Q and number of shared terms
		private final int[] m_pattern;
		
		/**
		 * @param pLength length of P
		 * @param plIndex index of the pivot in P
		 * @param pattern pattern of Q
		 */
		public ResolutionPattern(final int pLength, final int plIndex,
				final int[] pattern) {
			m_pLength = pLength;
			m_plIndex = plIndex;
			m_pattern = pattern;
		}

		@Override
		public int hashCode() {
			int hashCode = m_pLength + m_plIndex + m_pattern.length;
			for (int i = Math.min(m_pattern.length - 1, 5); i >= 0; --i) {
				hashCode += m_pattern[i];
			}
			return hashCode;
		}
		
		@Override
		public boolean equals(final Object o) {
			assert (o instanceof ResolutionPattern);
			final ResolutionPattern other = (ResolutionPattern)o;
			if ((m_pLength == other.m_pLength) &&
					(m_plIndex == other.m_plIndex) &&
					(m_pattern.length ==
							other.m_pattern.length)) {
				for (int i = m_pattern.length - 1; i >= 0; --i) {
					if (m_pattern[i] !=
							other.m_pattern[i]) {
						return false;
					}
				}
				return true;
			}
			return false;
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("(");
			builder.append("P: ");
			builder.append(m_pLength);
			builder.append(", ");
			builder.append(m_plIndex);
			builder.append("; Q: [");
			String append = "";
			for (int i = 0; i < m_pattern.length; ++i) {
				builder.append(append);
				append = ", ";
				builder.append(m_pattern[i]);
			}
			builder.append("])");
			return builder.toString();
		}
	}
	
	/**
	 * This class is used to wrap the return types of a method.
	 * The pattern is wrapped here even more (cp. {@link ResolutionPattern}).
	 */
	private class PatternSwapWrapper {
		// pattern
		private final ResolutionPattern m_patternWrap;
		// array for shared terms
		private final int[] m_sharedTerms;
		// true iff terms were swapped
		private final boolean m_swap;
		// true iff pivot is doubly negated
		private final boolean m_doubleNegation;
		
		/**
		 * @param pattern pattern
		 * @param sharedTerms array of the shared terms indices
		 * @param doubleNegation true iff pivot is doubly negated
		 * @param swap true iff terms were swapped
		 */
		public PatternSwapWrapper(final ResolutionPattern pattern,
				final int[] sharedTerms, final boolean swap,
				final boolean doubleNegation) {
			m_patternWrap = pattern;
			m_sharedTerms = sharedTerms;
			m_swap = swap;
			m_doubleNegation = doubleNegation;
		}
		
		/**
		 * This method indicates whether the pattern is relevant for storing.
		 * The reason this is considered is that for big proofs, the hash map
		 * could become too big and the chance for reusing a pattern with many
		 * variables is small due to combinatorial explosions in the number
		 * of permutations.
		 * 
		 * Currently the implementation only stores patterns whose bigger
		 * disjunction has size less than 6.
		 * 
		 * @return true iff the pattern does not exceed a fixed size
		 */
		public boolean isStoreCandidate() {
			return (m_patternWrap.m_pLength < 6);
		}
		
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("{");
			builder.append(m_patternWrap.toString());
			builder.append(", [");
			String append = "";
			for (int i = 0; i < m_sharedTerms.length; ++i) {
				builder.append(append);
				append = ", ";
				builder.append(m_sharedTerms[i]);
			}
			builder.append("], ");
			builder.append(m_swap);
			builder.append(", ");
			builder.append(m_doubleNegation);
			builder.append("}");
			return builder.toString();
		}
	}
	
	/**
	 * This class is used to wrap the return types of a method.
	 * The pattern is packed together with the shared terms.
	 */
	private class PatternSharedWrapper {
		// pattern
		private final int[] m_pattern;
		// array for shared terms
		private final int[] m_sharedTerms;
		
		/**
		 * @param qPattern pattern
		 * @param sharedTerms array for shared terms
		 */
		public PatternSharedWrapper(final int[] qPattern,
				final int[] sharedTerms) {
			m_pattern = qPattern;
			m_sharedTerms = sharedTerms;
		}
	}
	
	/**
	 * This method writes a string to the lemma appendable.
	 * 
	 * @param string string that is written
	 * @throws RuntimeException thrown if an IOException is caught
	 */
	private void writeLemmaString(String string) {
		try {
			m_lemmaAppendable.append(string);
        } catch (IOException e) {
            throw new RuntimeException("Appender throws IOException", e);
        }
	}
}