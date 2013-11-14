package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import de.uni_freiburg.informatik.ultimate.logic.*;

/**
 * This class is used to convert a trichotomy lemma.
 * That is, a number 'x' must be one of the following:
 * '(= x 0), (< x 0), or (> x 0)'
 * 
 * @author Christian Schilling
 */
public class LemmaTrichotomyConverter extends AConverter {
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 */
	public LemmaTrichotomyConverter(final Appendable appendable,
			final Theory theory, final TermConverter converter,
			final ComputationSimplifier simplifier) {
		super(appendable, theory, converter, simplifier);
	}
	
	/**
	 * This method converts a trichotomy lemma.
	 * The lemma is always a ternary disjunction, where one disjunct has the
	 * form '(= x 0)' (equality, 'e'), one disjunct has the form
	 * '(not (<= x 0))' (greater, 'g'), and one disjunct is the less ('l')
	 * disjunct. The order can vary.
	 * 
	 * The 'l' disjunct depends on the sort of 'x'. For integer 'x', the form
	 * is '(<= y 0)', where 'y' is equivalent to 'x + 1'. For real 'x' the form
	 * is '(< x 0)'.
	 * 
	 * The conversion first brings the disjunction to the normal form
	 * '(e | l | g)' (only internally). Since afterwards there can only occur
	 * resolution nodes, we can set our own order here.
	 * For real 'x' the lemma is then proven with a single rule.
	 * For integer 'x' the rule has an open obligation 'y = x + 1', which is
	 * finally proven by the simplifier.
	 * 
	 * @param lemma the ternary disjunction
	 * @return the disjunction (possibly reordered)
	 */
	public ApplicationTerm convert(ApplicationTerm lemma) {
		assert (lemma.getFunction() == m_theory.m_Or);
		final Term[] oldDisjunction = lemma.getParameters();
		assert ((oldDisjunction.length == 3) &&
				(unquote(oldDisjunction[0]) != null) &&
				(unquote(oldDisjunction[1]) != null) &&
				(unquote(oldDisjunction[2]) != null));
		final FunctionSymbol first = unquote(oldDisjunction[0]).getFunction();
		final FunctionSymbol second = unquote(oldDisjunction[1]).getFunction();
		final Sort sort;
		
		/* bring the disjuncts to the order 'e | l | g' */
		
		if (first == m_theory.m_Not) {
			assert (second.getParameterSorts().length == 2);
			sort = second.getParameterSorts()[0];
			final Term[] newDisjunction = new Term[3];
			newDisjunction[2] = oldDisjunction[0];
			
			// 'gel'
			if (second.getName() == "=") {
				assert ((unquote(oldDisjunction[2]).getFunction().getName() ==
								"<=") ||
						(unquote(oldDisjunction[2]).getFunction().getName() ==
								"<"));
				newDisjunction[0] = oldDisjunction[1];
				newDisjunction[1] = oldDisjunction[2];
			}
			// 'gle'
			else {
				assert (((second.getName() == "<=") ||
						(second.getName() == "<")) &&
						(unquote(oldDisjunction[2]).getFunction().getName() ==
								"="));
				newDisjunction[0] = oldDisjunction[2];
				newDisjunction[1] = oldDisjunction[1];
			}
			
			lemma = m_theory.term(m_theory.m_Or, newDisjunction);
		}
		else {
			assert (first.getParameterSorts().length == 2);
			sort = first.getParameterSorts()[0];
			
			if (first.getName() == "=") {
				// 'egl'
				if (second == m_theory.m_Not) {
					assert ((unquote(oldDisjunction[2]).getFunction().
									getName() == "<=") ||
							(unquote(oldDisjunction[2]).getFunction().
									getName() == "<"));
					final Term[] newDisjunction = new Term[3];
					newDisjunction[0] = oldDisjunction[0];
					newDisjunction[1] = oldDisjunction[2];
					newDisjunction[2] = oldDisjunction[1];
					lemma = m_theory.term(m_theory.m_Or, newDisjunction);
				}
				// 'elg'
				else {
					assert (((second.getName() == "<=") ||
							(second.getName() == "<")) &&
							(unquote(oldDisjunction[2]).getFunction() ==
									m_theory.m_Not));
					// nothing to do here
				}
			}
			else {
				assert ((first.getName() == "<=") ||
						(first.getName() == "<"));
				final Term[] newDisjunction = new Term[3];
				newDisjunction[1] = oldDisjunction[0];
				
				// 'lge'
				if (second == m_theory.m_Not) {
					assert (unquote(oldDisjunction[2]).getFunction().
									getName() == "=");
					newDisjunction[0] = oldDisjunction[2];
					newDisjunction[2] = oldDisjunction[1];
				}
				// 'leg'
				else {
					assert ((second.getName() == "=") &&
							(unquote(oldDisjunction[2]).getFunction() ==
									m_theory.m_Not));
					newDisjunction[0] = oldDisjunction[1];
					newDisjunction[2] = oldDisjunction[2];
				}
				
				lemma = m_theory.term(m_theory.m_Or, newDisjunction);
			}
		}
		
		// write rule
		m_converter.convert(lemma);
		
		// integer case
		if (sort == m_theory.getNumericSort()) {
			writeString("\" by (rule trichotomy_int, ");
			writeString(m_simplifier.getRule());
			writeString(")\n");
		}
		// real case
		else {
			assert (sort == m_theory.getRealSort());
			writeString("\" by (rule trichotomy_real)\n");
		}

		// result may have been modified, so return it
		return lemma;
	}
	
	/**
	 * This method returns the ApplicationTerm from a disjunct.
	 * If the disjunct is negated, it will be returned unchanged and
	 * is unpacked from the :quoted literals otherwise.
	 * 
	 * @param term the quoted term (must be an AnnotatedTerm)
	 * @return the inner term
	 */
	private ApplicationTerm unquote(Term term) {
		if (term instanceof ApplicationTerm) {
			assert (((ApplicationTerm)term).getFunction() == m_theory.m_Not);
			return (ApplicationTerm)term;
		}
		assert ((term instanceof AnnotatedTerm) &&
				(((AnnotatedTerm)term).getAnnotations().length == 1) &&
				(((AnnotatedTerm)term).getAnnotations()[0].getKey() ==
						":quoted") &&
				(((AnnotatedTerm)term).getSubterm() instanceof
						ApplicationTerm));
		return (ApplicationTerm)((AnnotatedTerm)term).getSubterm();
	}
}