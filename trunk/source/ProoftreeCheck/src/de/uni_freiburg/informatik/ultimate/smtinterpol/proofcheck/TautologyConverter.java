package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.*;

/**
 * This class is used to convert a tautology proof node (@tautology).
 * A tautology is used to justify a contradiction.
 * 
 * @author Christian Schilling
 */
public class TautologyConverter extends AConverter {
	// map for the rules
	private final HashMap<String, IRule> m_annot2Rule;
	
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 */
	public TautologyConverter(final Appendable appendable, final Theory theory,
			final TermConverter converter,
			final ComputationSimplifier simplifier) {
		super(appendable, theory, converter, simplifier);
		
		// fill rule map
		m_annot2Rule = new HashMap<String, TautologyConverter.IRule>(
				(int)(21 / 0.75) + 1);
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
		// CC disequality of 'True' and 'False'
		m_annot2Rule.put(":trueNotFalse",
				new SimpleRule("(rule HOL.True_not_False)\n"));
		/*
		 * excluded middle for a binary disjunction of a negated :quoted
		 * disjunction and its non-quoted version
		 */
		m_annot2Rule.put(":or+",
				new SimpleRule("(rule HOL.excluded_middle)\n"));
		// disjunction of a disjunction and one of its disjuncts negated
		m_annot2Rule.put(":or-",
				new OrMinusRule());
		/*
		 * disjunction of negated if-then-else, negative condition, and
		 * positive first case
		 */
		m_annot2Rule.put(":ite+1",
				new SimpleRule("(rule taut_iteP1)\n"));
		/*
		 * disjunction of negated if-then-else, positive condition, and
		 * positive second case
		 */
		m_annot2Rule.put(":ite+2",
				new SimpleRule("(rule taut_iteP2)\n"));
		/*
		 * disjunction of negated if-then-else, positive first case, and
		 * positive second case
		 */
		m_annot2Rule.put(":ite+red",
				new SimpleRule("(rule taut_itePRed)\n"));
		/*
		 * disjunction of if-then-else, negative condition, and
		 * negative first case
		 */
		m_annot2Rule.put(":ite-1",
				new SimpleRule("(rule taut_iteM1)\n"));
		/*
		 * disjunction of if-then-else, positive condition, and
		 * negative second case
		 */
		m_annot2Rule.put(":ite-2",
				new SimpleRule("(rule taut_iteM2)\n"));
		/*
		 * disjunction of if-then-else, negative first case, and
		 * negative second case
		 */
		m_annot2Rule.put(":ite-red",
				new SimpleRule("(rule taut_iteMRed)\n"));
		/*
		 * disjunction of negated Boolean equality, first term positive, and
		 * second term negative
		 */
		m_annot2Rule.put(":=+1",
				new SimpleRule("(rule taut_EqP1)\n"));
		/*
		 * disjunction of negated Boolean equality, first term negative, and
		 * second term positive
		 */
		m_annot2Rule.put(":=+2",
				new SimpleRule("(rule taut_EqP2)\n"));
		// disjunction of Boolean equality and both terms positive
		m_annot2Rule.put(":=-1",
				new SimpleRule("(rule taut_EqM1)\n"));
		// disjunction of Boolean equality and both terms negative
		m_annot2Rule.put(":=-2",
				new SimpleRule("(rule taut_EqM2)\n"));
		// excluded middle with equality with 'True'
		m_annot2Rule.put(":excludedMiddle1",
				new ExcludedMiddle1Rule());
		// excluded middle with equality with 'False'
		m_annot2Rule.put(":excludedMiddle2",
				new ExcludedMiddle2Rule());
		// non-Boolean if-then-else
		m_annot2Rule.put(":termITE",
				new TermIteRule());
		// lower bound for div
		m_annot2Rule.put(":divLow",
				new DivLowRule());
		// upper bound for div
		m_annot2Rule.put(":divHigh",
				new DivHighRule());
		// lower bound for mixed logic conversion
		m_annot2Rule.put(":toIntLow",
				new ToIntLowRule());
		// upper bound for mixed logic conversion
		m_annot2Rule.put(":toIntHigh",
				new ToIntHighRule());
		/*
		 * excluded middle for equality in canonical sum
		 * NOTE: The simplifier is too weak, for instance the formula
		 *       '(y + (- x) = (0::int)) | (~ x = y)' with x, y integers
		 *       cannot be proven.
		 */
		m_annot2Rule.put(":eq",
				new SimpleRule("auto\n"));
	}
	
	/**
	 * This interface is used for the rule translation.
	 */
	private interface IRule {
		/**
		 * @param tautology the tautology
		 */
		void convert(final ApplicationTerm tautology);
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
		public void convert(final ApplicationTerm tautology) {
			writeString(m_rule);
		}
	}
	
	/**
	 * This class translates the :or- rule.
	 * 
	 * The tautology has the form of a binary disjunction, where the first
	 * disjunct is a :quoted disjunction itself and the second disjunct is a
	 * negated term (possibly doubly negated). The second term without the
	 * negation can be found in the :quoted disjunction.
	 * 
	 * The translation is based on the 'intro' method in Isabelle.
	 * 
	 * If the disjunct can be found in the lowest level of the disjunction,
	 * a slightly faster translation is used.
	 * 
	 * But the :quoted disjunction may have to be flattened (that is, inner
	 * disjunctions have to be unpacked). This case is also possible with
	 * 'intro', but needs more rule arguments.
	 */
	private class OrMinusRule implements IRule {
		@Override
		public void convert(final ApplicationTerm tautology) {
			final Term[] disjunction = tautology.getParameters();
			assert ((disjunction.length == 2) &&
					(disjunction[0] instanceof AnnotatedTerm) &&
					(((AnnotatedTerm)disjunction[0]).getSubterm() instanceof
							ApplicationTerm) &&
					(((ApplicationTerm)((AnnotatedTerm)disjunction[0]).
							getSubterm()).getFunction() == m_theory.m_Or) &&
					(disjunction[1] instanceof ApplicationTerm) &&
					(((ApplicationTerm)disjunction[1]).getFunction() ==
							m_theory.m_Not));
			final Term[] quotedDisjunction =
					((ApplicationTerm)((AnnotatedTerm)disjunction[0]).
							getSubterm()).getParameters();
			final Term target =
					((ApplicationTerm)disjunction[1]).getParameters()[0];
			
			// find the single disjunct (without negation)
			for (int i = 0; i < quotedDisjunction.length; ++i) {
				// disjunct was found
				if (quotedDisjunction[i] == target) {
					// disjunct is the last one, use different final rule
					if (i == quotedDisjunction.length - 1) {
						writeString("(intro taut_orM_fin_bin " +
								"taut_orM_intro)\n");
					}
					// disjunct is not the last one, shortcut after finding it
					else {
						writeString("(intro taut_orM_fin taut_orM_intro)\n");
					}
					return;
				}
			}
			
			// the disjunct was not found, so flatten the quoted disjunction
			writeString("(intro taut_orM_fin taut_orM_fin_bin taut_orM_flat " +
					"taut_orM_intro)\n");
		}
	}
	
	/**
	 * This class converts the :excludedMiddle1 rule.
	 * 
	 * This is a variation of the 'rule of the excluded middle', where a
	 * disjunction consists of a negated formula '~F' and the equality
	 * 'F = True'.
	 * 
	 * The reason why the translation is not possible with a static rule is
	 * that the order in the equality is not fixed.
	 * Note that this is not necessary, but only for better performance.
	 * Alternatively, both rules could be added to an alternative choice ('|')
	 * like '(rule r1 | rule r2)'.
	 */
	private class ExcludedMiddle1Rule implements IRule {
		@Override
		public void convert(final ApplicationTerm tautology) {
			assert ((tautology.getFunction() == m_theory.m_Or) &&
					(tautology.getParameters().length == 2));
			

			final Term[] equality;
			// unquoted term
			if (tautology.getParameters()[1] instanceof ApplicationTerm) {
				assert (((ApplicationTerm)tautology.getParameters()[1]).
						getFunction().getName() == "=");
				equality = ((ApplicationTerm)tautology.getParameters()[1]).
						getParameters();
			}
			// quoted term
			else {
				assert ((tautology.getParameters()[1] instanceof AnnotatedTerm)
						&&
						(((AnnotatedTerm)tautology.getParameters()[1]).
								getAnnotations().length == 1) &&
						(((AnnotatedTerm)tautology.getParameters()[1]).
								getAnnotations()[0].getKey() == ":quoted") &&
						(((AnnotatedTerm)tautology.getParameters()[1]).
								getSubterm() instanceof ApplicationTerm) &&
						(((ApplicationTerm)((AnnotatedTerm)tautology.
								getParameters()[1]).getSubterm()).
								getFunction().getName() == "="));
				equality = ((ApplicationTerm)((AnnotatedTerm)tautology.
						getParameters()[1]).getSubterm()).getParameters();
			}
			assert (equality.length == 2);
			
			// 'True' is on the right-hand side in the equality
			if (equality[0] == m_theory.TRUE) {
				writeString("(rule taut_exclMid_tl)\n");
			}
			// 'True' is on the left-hand side in the equality
			else {
				assert (equality[1] == m_theory.TRUE);
				writeString("(rule taut_exclMid_tr)\n");
			}
		}
	}
	
	/**
	 * This class converts the :excludedMiddle2 rule.
	 * 
	 * This is a variation of the 'rule of the excluded middle', where a
	 * disjunction consists of a positive formula 'F' and the equality
	 * 'F = False'.
	 * 
	 * The reason why the translation is not possible with a static rule is
	 * that the order in the equality is not fixed.
	 * Note that this is not necessary, but only for better performance.
	 * Alternatively, both rules could be added to an alternative choice ('|')
	 * like '(rule r1 | rule r2)'.
	 */
	private class ExcludedMiddle2Rule implements IRule {
		@Override
		public void convert(final ApplicationTerm tautology) {
			assert ((tautology.getFunction() == m_theory.m_Or) &&
					(tautology.getParameters().length == 2));
			
			final Term[] equality;
			// unquoted term
			if (tautology.getParameters()[1] instanceof ApplicationTerm) {
				assert (((ApplicationTerm)tautology.getParameters()[1]).
						getFunction().getName() == "=");
				equality = ((ApplicationTerm)tautology.getParameters()[1]).
						getParameters();
			}
			// quoted term
			else {
				assert ((tautology.getParameters()[1] instanceof AnnotatedTerm)
						&&
						(((AnnotatedTerm)tautology.getParameters()[1]).
								getAnnotations().length == 1) &&
						(((AnnotatedTerm)tautology.getParameters()[1]).
								getAnnotations()[0].getKey() == ":quoted") &&
						(((AnnotatedTerm)tautology.getParameters()[1]).
								getSubterm() instanceof ApplicationTerm) &&
						(((ApplicationTerm)((AnnotatedTerm)tautology.
								getParameters()[1]).getSubterm()).
								getFunction().getName() == "="));
				equality = ((ApplicationTerm)((AnnotatedTerm)tautology.
						getParameters()[1]).getSubterm()).getParameters();
			}
			assert (equality.length == 2);
			
			// 'False' is on the right-hand side in the equality
			if (equality[0] == m_theory.FALSE) {
				writeString("(rule taut_exclMid_fl)\n");
			}
			// 'False' is on the left-hand side in the equality
			else {
				assert (equality[1] == m_theory.FALSE);
				writeString("(rule taut_exclMid_fr)\n");
			}
		}
	}
	
	/**
	 * This class converts the :termITE rule.
	 * 
	 * The tautology has the form of an (n+1)-ary disjunction.
	 * It justifies the simplification of an if-then-else tree
	 * ((n+1)-th disjunct), where the i-th disjunct corresponds the i-th
	 * condition.
	 * 
	 * The translation is based on the 'intro' method in Isabelle.
	 * 
	 * The binary case is just a shorter version of the n-ary case.
	 */
	private class TermIteRule implements IRule {
		@Override
		public void convert(final ApplicationTerm tautology) {
			assert ((tautology.getFunction() == m_theory.m_Or) &&
					(tautology.getParameters().length > 1));
			final Term[] disjuncts = tautology.getParameters();
			
			// n-ary case
			if (disjuncts.length > 2) {
				writeString("(intro taut_termITE_unroll, intro " +
						"taut_termITE_then taut_termITE_else, " +
						"intro taut_termITE_then_last " +
						"taut_termITE_else_last)\n");
			}
			else {
				writeString("(intro taut_termITE_then_last " +
						"taut_termITE_else_last)\n");
			}
		}
	}
	
	/**
	 * This class handles identical steps for the rules :divLow and :divHigh.
	 */
	private abstract class ADivRule implements IRule {
		/**
		 * There are several problems with this rule:
		 * SMTInterpol does not use this rule for the constant zero, but
		 * Isabelle has to prove this.
		 * The left-hand side of the inequality can be permuted, which is why
		 * the simplifier is used to capture all possible cases. Also, to find
		 * the constant and the term (which must be given to Isabelle) becomes
		 * harder.
		 * Identifying the correct 'div' term is not trivial, since two
		 * summands can have this form.
		 */
		@Override
		public abstract void convert(final ApplicationTerm tautology);
		
		/**
		 * This method finds the correct terms.
		 * It can be the case that the other summand also has the form
		 * 'd * (x div d)'.
		 * 
		 * NOTE: In the end the rule uses the simplifier to show that the
		 *       constant is different from zero, but this is no problem, since
		 *       a constant cannot be unpacked.
		 * 
		 * @param first the first summand
		 * @param second the second summand
		 * @param isLow true iff rule is 'Low', else rule is 'High'
		 */
		protected void findDiv(final ApplicationTerm first,
				final ApplicationTerm second, final boolean isLow) {
			ApplicationTerm product = null;
			
			if ((first.getFunction().getName() == "*") &&
					(first.getParameters().length == 2)) {
				// further investigation
				if ((second.getFunction().getName() == "*") &&
						(second.getParameters().length == 2)) {
					// look into first summand
					final Term factor = first.getParameters()[1];;
					if ((factor instanceof ApplicationTerm) &&
							(((ApplicationTerm)factor).getFunction().
									getName() == "div")) {
						final ApplicationTerm div = (ApplicationTerm)factor;
						assert ((div.getParameters().length == 2) &&
								(div.getParameters()[0] instanceof
								ApplicationTerm) &&
								(((ApplicationTerm)div.getParameters()[0]).
										getFunction().getName() == "*") &&
								(((ApplicationTerm)div.getParameters()[0]).
										getParameters().length == 2));
						final ApplicationTerm divFirst =
								(ApplicationTerm)div.getParameters()[0];
						
						// first summand is the target product
						if ((divFirst.getFunction().getName() == "*") &&
								(divFirst.getParameters().length == 2) &&
								(divFirst.getParameters()[1] ==
										second.getParameters()[1])) {
							product = first;
						}
					}
					// second summand is the target product
					if (product == null) {
						product = second;
					}
				}
				// first summand is the product
				else {
					product = first;
				}
			}
			// second summand is the product
			else {
				assert ((second.getFunction().getName() == "*") &&
						(second.getParameters().length == 2));
				product = second;
			}
			
			// print swap
			if (product == first) {
				if (isLow) {
					writeString("(rule taut_divLow");
				}
				else {
					writeString("(rule taut_divHigh");
				}
			}
			else {
				if (isLow) {
					writeString("(rule taut_swap_sum_bin, rule taut_divLow");
				}
				else {
					writeString("(rule taut_swap_sum_ter, rule taut_divHigh");
				}
			}
			
			// found the target product, extract the terms
			assert ((product != null) &&
					(product.getParameters().length == 2) &&
					(product.getParameters()[1] instanceof ApplicationTerm) &&
					(((ApplicationTerm)product.getParameters()[1]).
							getFunction().getName() == "div"));
			final ApplicationTerm div =
					(ApplicationTerm)product.getParameters()[1];
			assert ((div.getParameters().length == 2) &&
					(div.getParameters()[0] instanceof ApplicationTerm) &&
					(product.getParameters()[0] == div.getParameters()[1]));
			
			final ApplicationTerm term =
					(ApplicationTerm)div.getParameters()[0];
			final String function = term.getFunction().getName();
			// factor is -1 (special syntax)
			if (function == "-") {
				writeString("_neg1, ");
			}
			// factor is > 1 or < -1, use a different rule
			else if (function == "*") {
				boolean negative = false;
				
				assert (term.getParameters().length > 1);
				final Term firstFactor = term.getParameters()[0];
				if (firstFactor instanceof ApplicationTerm) {
					final ApplicationTerm aFirstFactor =
							(ApplicationTerm)firstFactor;
					if (aFirstFactor.getFunction().getName() == "-") {
						assert (aFirstFactor.getParameters().length > 0);
						// factor is < -1
						if (aFirstFactor.getParameters()[0] instanceof
								ConstantTerm) {
							negative = true;
							writeString("_neg2, ");
						}	
					}
				}
				// factor is > 1
				if (! negative) {
					writeString("_pos2, ");
				}
			}
			// factor is 1 (special syntax)
			else {
				writeString("_pos1, ");
			}
			writeString(m_simplifier.getRule());
			writeString(")\n");
		}
	}
	
	/**
	 * This class converts the :divLow rule.
	 */
	private class DivLowRule extends ADivRule {
		@Override
		public void convert(final ApplicationTerm tautology) {
			assert ((tautology.getFunction().getName() == "<=") &&
					(tautology.getParameters().length == 2) &&
					(tautology.getParameters()[0] instanceof ApplicationTerm)
					&&
					(((ApplicationTerm)tautology.getParameters()[0]).
							getFunction().getName() == "+"));
			final Term[] summands = ((ApplicationTerm)tautology.
					getParameters()[0]).getParameters();
			assert ((summands.length == 2) &&
					(summands[0] instanceof ApplicationTerm) &&
					(summands[1] instanceof ApplicationTerm));
			super.findDiv((ApplicationTerm)summands[0],
					(ApplicationTerm)summands[1], true);
		}
	}
	
	/**
	 * This class converts the :divHigh rule.
	 */
	private class DivHighRule extends ADivRule {
		/**
		 * {@inheritDoc}
		 * Also, the absolute value of the constant has to be explicitly
		 * computed (again, this is not problematic).
		 */
		@Override
		public void convert(final ApplicationTerm tautology) {
			assert ((tautology.getFunction() == m_theory.m_Not) &&
					(tautology.getParameters().length == 1) &&
					(tautology.getParameters()[0] instanceof ApplicationTerm));
			final ApplicationTerm inequality =
					(ApplicationTerm)tautology.getParameters()[0];
			assert ((inequality.getFunction().getName() == "<=") &&
					(inequality.getParameters().length == 2) &&
					(inequality.getParameters()[0] instanceof ApplicationTerm)
					&&
					(((ApplicationTerm)inequality.getParameters()[0]).
							getFunction().getName() == "+"));
			final Term[] summands = ((ApplicationTerm)inequality.
					getParameters()[0]).getParameters();
			
			// NOTE: The constant 1 is always the right-most term in the sum.
			assert ((summands.length == 3) &&
					(summands[0] instanceof ApplicationTerm) &&
					(summands[1] instanceof ApplicationTerm) &&
					(summands[2] instanceof ConstantTerm));
			super.findDiv((ApplicationTerm)summands[0],
					(ApplicationTerm)summands[1], false);
		}
	}
	
	/**
	 * This class handles identical steps for the rules :divLow and :divHigh.
	 */
	private abstract class AToIntRule implements IRule {
		/**
		 * There are several problems with this rule:
		 * The left-hand side of the inequality can be permuted.
		 * Identifying the correct outer term is not trivial, since both
		 * summands can have the form 'to_real(to_int(x))'.
		 */
		@Override
		public abstract void convert(final ApplicationTerm tautology);
		
		/**
		 * This method finds the correct term.
		 * It can be the case that the other summand also has the form
		 * 'to_real(to_int(x))'.
		 * 
		 * @param first the first summand
		 * @param second the second summand
		 * @param isLow true iff rule is 'Low', else rule is 'High'
		 */
		private void findToInt(final ApplicationTerm first,
				final ApplicationTerm second, final boolean isLow) {
			ApplicationTerm toReal = null;
			
			if (first.getFunction().getName() == "to_real") {
				assert (first.getParameters().length == 1);
				// further investigation
				if (second.getFunction().getName() == "to_real") {
					assert (second.getParameters().length == 1);
					
					// look into first summand
					if (first.getParameters()[0] instanceof ApplicationTerm) {
						final ApplicationTerm toInt =
								(ApplicationTerm)first.getParameters()[0];
						if (toInt.getFunction().getName() == "to_int") {
							assert (toInt.getParameters().length == 1);
							if (toInt.getParameters()[0] instanceof
									ApplicationTerm) {
								final ApplicationTerm subTerm =
										(ApplicationTerm)toInt.
										getParameters()[0];
								if (subTerm.getFunction().getName() == "-") {
									assert (subTerm.getParameters().length ==
											1);
									// first summand is the target term
									if (subTerm.getParameters()[0] == second) {
										toReal = first;
									}
								}
							}
						}
					}
					// second summand is the target term
					if (toReal == null) {
						toReal = second;
					}
				}
				// first summand is the target term
				else {
					toReal = first;
				}
			}
			// second summand is the target term
			else {
				assert ((second.getFunction().getName() == "to_real") &&
						(second.getParameters().length == 1));
				toReal = second;
			}
			
			// print swap
			if (toReal == first) {
				if (isLow) {
					writeString("(rule taut_toIntLow");
				}
				else {
					writeString("(rule taut_toIntHigh");
				}
			}
			else {
				if (isLow) {
					writeString("(rule taut_swap_sum_bin, rule taut_toIntLow");
				}
				else {
					writeString(
							"(rule taut_swap_sum_ter, rule taut_toIntHigh");
				}
			}
			
			// found the target term, extract the sub-term
			assert ((toReal != null) &&
					(toReal.getFunction().getName() == "to_real") &&
					(toReal.getParameters().length == 1) &&
					(toReal.getParameters()[0] instanceof ApplicationTerm) &&
					(((ApplicationTerm)toReal.getParameters()[0]).
							getFunction().getName() == "to_int") &&
					(((ApplicationTerm)toReal.getParameters()[0]).
							getParameters().length == 1) &&
					(((ApplicationTerm)toReal.getParameters()[0]).
							getParameters()[0] instanceof ApplicationTerm));
			
			final ApplicationTerm term = (ApplicationTerm)((ApplicationTerm)
					toReal.getParameters()[0]).getParameters()[0];
			
			final String function = term.getFunction().getName();
			// factor is -1 (special syntax)
			if (function == "-") {
				writeString("_neg1)\n");
			}
			// factor is > 1 or < -1, use a different rule
			else if (function == "*") {
				assert (term.getParameters().length > 1);
				Term firstFactor = term.getParameters()[0];
				if (firstFactor instanceof ApplicationTerm) {
					ApplicationTerm aFirstFactor =
							(ApplicationTerm)firstFactor;
					if (aFirstFactor.getFunction().getName() == "-") {
						assert (aFirstFactor.getParameters().length > 0);
						// factor is < -1
						if (aFirstFactor.getParameters()[0] instanceof
								ConstantTerm) {
							writeString("_neg2)\n");
							return;
						}	
					}
				}
				// factor is > 1
				writeString("_pos2)\n");
			}
			// factor is 1 (special syntax)
			else {
				writeString("_pos1)\n");
			}
		}
	}
	
	/**
	 * This class converts the :toIntLow rule.
	 */
	private class ToIntLowRule extends AToIntRule {
		@Override
		public void convert(final ApplicationTerm tautology) {
			assert ((tautology.getFunction().getName() == "<=") &&
					(tautology.getParameters().length == 2) &&
					(tautology.getParameters()[0] instanceof ApplicationTerm)
					&&
					(((ApplicationTerm)tautology.getParameters()[0]).
							getFunction().getName() == "+"));
			final Term[] summands = ((ApplicationTerm)tautology.
					getParameters()[0]).getParameters();
			assert ((summands.length == 2) &&
					(summands[0] instanceof ApplicationTerm) &&
					(summands[1] instanceof ApplicationTerm));
			super.findToInt((ApplicationTerm)summands[0],
					(ApplicationTerm)summands[1], true);
		}
	}
	
	/**
	 * This class converts the :toIntHigh rule.
	 */
	private class ToIntHighRule extends AToIntRule {
		@Override
		public void convert(final ApplicationTerm tautology) {
			assert ((tautology.getFunction() == m_theory.m_Not) &&
					(tautology.getParameters().length == 1) &&
					(tautology.getParameters()[0] instanceof ApplicationTerm));
			final ApplicationTerm inequality =
					(ApplicationTerm)tautology.getParameters()[0];
			assert ((inequality.getFunction().getName() == "<=") &&
					(inequality.getParameters().length == 2) &&
					(inequality.getParameters()[0] instanceof ApplicationTerm)
					&&
					(((ApplicationTerm)inequality.getParameters()[0]).
							getFunction().getName() == "+"));
			final Term[] summands = ((ApplicationTerm)inequality.
					getParameters()[0]).getParameters();
			
			// NOTE: The constant 1 is always the right-most term in the sum.
			assert ((summands.length == 3) &&
					(summands[0] instanceof ApplicationTerm) &&
					(summands[1] instanceof ApplicationTerm) &&
					(summands[2] instanceof ConstantTerm));
			super.findToInt((ApplicationTerm)summands[0],
					(ApplicationTerm)summands[1], false);
		}
	}
	
	// [end] rules //
	
	/**
	 * This method converts the tautology rule.
	 * Many rules only need one application of a lemma.
	 * Only the rules :or-, :excludedMiddle1, :excludedMiddle2, :termITE,
	 * :divLow, :divHigh, :toIntLow, and :toIntHigh need more effort.
	 * 
	 * @param tautology the tautology
	 * @param annotation the specific rule that is used
	 */
	public void convert(final ApplicationTerm tautology,
			final String annotation) {
		m_converter.convert(tautology);
		writeString("\" by ");
		
		assert (m_annot2Rule.get(annotation) != null);
		m_annot2Rule.get(annotation).convert(tautology);
	}
}