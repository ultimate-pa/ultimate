package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.*;

/**
 * This class is used to convert a split proof node (@split).
 * A split brings canonical term forms (DAG) to CNF. There are two kinds of
 * rules: The real splitting (of a conjunct from a conjunction) and
 * transformations for Boolean equalities and if-then-else.
 * 
 * @author Christian Schilling
 */
public class SplitConverter extends AConverter {
	// map for the rules
	private final HashMap<String, IRule> m_annot2Rule;
	
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 */
	public SplitConverter(final Appendable appendable, final Theory theory,
			final TermConverter converter,
			final ComputationSimplifier simplifier) {
		super(appendable, theory, converter, simplifier);
		
		// fill rule map
		m_annot2Rule = new HashMap<String, IRule>((int)(9 / 0.75) + 1);
		fillMap();
	}
	
	// [start] rules //
	
	/**
	 * This method fills the rule map with the rules.
	 * For each rule a conversion object is added to a hash map, which handles
	 * the conversion individually.
	 * 
	 * Here the rules could be changed or new ones added if necessary.
	 */
	private void fillMap() {
		// splitting a negated disjunct from a negated disjunction
		m_annot2Rule.put(":notOr",
				new NotOrRule());
		/*
		 * Boolean equality to disjunction with positive first and negative
		 * second term
		 */
		m_annot2Rule.put(":=+1",
				new SimpleRule("(rule split_eqP1)\n"));
		/*
		 * Boolean equality to disjunction with negative first and positive
		 * second term
		 */
		m_annot2Rule.put(":=+2",
				new SimpleRule("(rule split_eqP2)\n"));
		/*
		 * negated Boolean equality to disjunction with positive first and
		 * second term
		 */
		m_annot2Rule.put(":=-1",
				new SimpleRule("(rule split_eqM1)\n"));
		/*
		 * negated Boolean equality to disjunction with negative first and
		 * second term
		 */
		m_annot2Rule.put(":=-2",
				new SimpleRule("(rule split_eqM2)\n"));
		/*
		 * if-then-else to disjunction with negative condition and positive
		 * first case
		 */
		m_annot2Rule.put(":ite+1",
				new SimpleRule("(rule split_iteP1)\n"));
		// if-then-else to disjunction with positive condition and second case
		m_annot2Rule.put(":ite+2",
				new SimpleRule("(rule split_iteP2)\n"));
		/*
		 * negative if-then-else to disjunction with negative condition and
		 * first case
		 */
		m_annot2Rule.put(":ite-1",
				new SimpleRule("(rule split_iteM1)\n"));
		/*
		 * negative if-then-else to disjunction with positive condition and
		 * negative second case
		 */
		m_annot2Rule.put(":ite-2",
				new SimpleRule("(rule split_iteM2)\n"));
	}
	
	/**
	 * This interface is used for the rule translation.
	 */
	private interface IRule {
		/**
		 * @param negDisjunction the (negated) disjunction
		 * @param result the (negated) disjunct that is split away
		 */
		void convert(final ApplicationTerm negDisjunction,
				final ApplicationTerm result);
	}
	
	/**
	 * This class translates trivial rules that need no further investigation.
	 */
	private class SimpleRule implements IRule {
		// Isabelle rule
		private final String m_rule;
		
		/**
		 * @param rule the rule
		 */
		public SimpleRule(final String rule) {
			m_rule = rule;
		}
		
		/**
		 * The rule is simply written without any additional steps.
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public void convert(final ApplicationTerm negDisjunction,
				final ApplicationTerm result) {
			writeString(m_rule);
		}
	}
	
	/**
	 * This class translates the :notOr rule.
	 * 
	 * This is a split of a negated disjunct from a negated disjunction.
	 * Note that this is equivalent to splitting a conjunct from a
	 * conjunction. Disjunction is right-associative in Isabelle, so we
	 * only consider binary disjunctions.
	 * 
	 * The proof goes by elimination tactics, that is, the rules are repeatedly
	 * applied until either none is available or the goal is closed. If the
	 * first (negated) disjunct is the target term, the proof is finished with
	 * a binary split rule. If not, the left-hand side of the disjunction is
	 * dropped and the search goes on recursively in the right-hand side.
	 * 
	 * NOTE: If the target term is the rightmost (negated) disjunct,
	 *       the proof rule finishes with the obligation '~P ==> ~P'.
	 *       This is automatically solved by the 'by' command in Isabelle.
	 *       But it can be the case that the rightmost disjunct is itself a
	 *       disjunction. To prevent elimination there, another rule is
	 *       necessary for this special case.
	 * 
	 * More attention is payed towards the translation. Note that this is not
	 * necessary, but only for better performance.
	 * Alternatively, both the binary finishing rules could be added to the
	 * 'elim' arguments list.
	 */
	private class NotOrRule implements IRule {
		@Override
		public void convert(final ApplicationTerm negDisjunction,
				final ApplicationTerm result) {
			assert ((negDisjunction.getFunction() == m_theory.m_Not) &&
					(negDisjunction.getParameters().length == 1) &&
					(negDisjunction.getParameters()[0] instanceof
							ApplicationTerm));
			final ApplicationTerm disjunction = (ApplicationTerm)
					((ApplicationTerm)negDisjunction).getParameters()[0];
			assert ((disjunction.getFunction() == m_theory.m_Or) &&
					(disjunction.getParameters().length > 1) &&
					(result.getFunction() == m_theory.m_Not) &&
					(result.getParameters().length == 1));
			final Term last = disjunction.getParameters()[disjunction.
		                                        getParameters().length - 1];
			
			// the result is the rightmost disjunct
			if (last == result.getParameters()[0]) {
					writeString("(elim split_notOr_finR split_notOr_elim)\n");
			}
			// the result should be somewhere else
			else {
				writeString("(elim split_notOr_finL split_notOr_elim)\n");
			}
		}
	}
	
	// [end] rules //
	
	/**
	 * This method converts the split rule.
	 * The transformation rules only need one application of a lemma.
	 * Only the :notOr rule (real splitting, mostly occurs) needs more effort.
	 * 
	 * @param negDisjunction the (negated) disjunction
	 * @param result the (negated) disjunct that is split away
	 * @param annotation the specific rule that is used
	 */
	public void convert(final ApplicationTerm negDisjunction,
			final ApplicationTerm result, final String annotation) {
		m_converter.convert(result);
		writeString("\" by ");
		
		assert (m_annot2Rule.get(annotation) != null);
		m_annot2Rule.get(annotation).convert(negDisjunction, result);
	}
}