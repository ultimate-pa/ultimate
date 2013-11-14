package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.*;

/**
 * This class is used to convert a lemma of linear arithmetic (LA).
 * 
 * @author Christian Schilling
 */
public class LemmaLAConverter extends AConverter {
	// true iff fast proofs shall be printed
	private final boolean m_fastProofs;
	// appendable for the lemmata
	private final Appendable m_lemmaAppendable;
	// index number of the pattern lemmata
	private int m_lemmaNumber;
	// strings for handling fast proofs
	private final String m_startLine;
	private final String m_endLine;
	// variable name in the pattern proof
	private static final String LA_LEMMA_VAR = "x";
	
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 * @param fastProofs true iff fast proofs shall be printed
	 * @param lemmaAppendable the theory file for the lemmata
	 */
	public LemmaLAConverter(final Appendable appendable,
			final Theory theory, final TermConverter converter,
			final ComputationSimplifier simplifier,	final boolean fastProofs,
			final Appendable lemmaAppendable) {
		super(appendable, theory, converter, simplifier);
		m_fastProofs = fastProofs;
		m_startLine = m_fastProofs ? "" : "apply (";
		m_endLine = m_fastProofs ? ",\n" : ")\n";
		m_lemmaAppendable = lemmaAppendable;
		m_lemmaNumber = 0;
	}
	
	/**
	 * This method converts a lemma of linear arithmetic (LA).
	 * 
	 * First a copy of the disjunction (the pattern) is created where the
	 * variable terms are replaced by pattern variables. Then the lemma is
	 * proven as a pattern lemma and in the actual proof file just a recall
	 * of the pattern lemma is applied.
	 * 
	 * The proof goes by contraposition. The following steps are applied
	 * stepwise to the first two literals:
	 * - de Morgan's rule
	 * - multiplication with Farkas coefficient
	 * - calculation with distributivity rule
	 * - raw merging of the first two literals
	 * - simplification of merged terms
	 * 
	 * @param lemma the disjunction of linear inequalities
	 * @param factors factors to multiply the disjuncts with
	 */
	public void convert(final ApplicationTerm lemma, final Object[] factors) {
		final Term[] disjuncts = lemma.getParameters();
		assert ((disjuncts.length == factors.length) &&
				(disjuncts.length > 1));
		
		// find the correct theory: integer, real, or mixed
		final EArith arithType;
		switch (m_theory.getLogic()) {
			case AUFLIA:
			case QF_AUFLIA:
			case QF_LIA:
			case QF_NIA:
			case QF_UFLIA:
			case UFNIA:
				arithType = EArith.integer;
				break;
			case LRA:
			case QF_LRA:
			case QF_NRA:
			case QF_UFLRA:
			case QF_UFNRA:
			case UFLRA:
				arithType = EArith.real;
				break;
			case AUFLIRA:
			case AUFNIRA:
			case QF_UFLIRA:
				arithType = EArith.mixed;
				break;
			default:
				throw new IllegalArgumentException(
						"The current logic is not supported");
		}
		
		// data structure for the literals
		final IneqInfo ineqs = new IneqInfo(disjuncts.length, factors,
				arithType);
		final ApplicationTerm patternLemma =
				createPatternLemma(disjuncts, ineqs, arithType);
		
		// header (proof by contraposition)
		writeLemmaString("\nlemma ");
		writeLemmaString(LA_LEMMA_PREFIX);
		writeLemmaString(Integer.toString(++m_lemmaNumber));
		writeLemmaString(": \"");
		m_converter.convertWithTypes(patternLemma, m_lemmaAppendable);
		writeLemmaString("\"\nproof (rule classical)\nassume \"~?thesis\"" +
				"\nhence \"False\"\n");
		
		// map from term to factor
		final Var2FactorMap map = new Var2FactorMap();
				
		// keep track of the order sign ('<' vs. '<=') to use the correct rule
		FarkasResult farkas = new FarkasResult(false, EOrder.le_le,
				ineqs.m_literals[0].m_isIntegral);
		
		/*
		 * The first literal has no predecessor and hence cannot be merged.
		 * That is why it is handled differently.
		 */
		deMorgan(ineqs, 0);
		farkas = farkasCoefficient(ineqs, 0, farkas, arithType);
		distributivity(ineqs, 0, map, farkas, arithType);
		
		// binary processing of the literals
		for (int i = 1; i < disjuncts.length; ++i) {
			// apply de Morgan's rule
			deMorgan(ineqs, i);
			
			// multiplication with Farkas coefficients
			farkas = farkasCoefficient(ineqs, i, farkas, arithType);
			
			// eliminate distributivity */
			distributivity(ineqs, i, map, farkas, arithType);
			
			// merge literals
			farkas = mergeLiterals(ineqs, i, farkas, arithType);
			
			// simplify expressions
			simplify(ineqs, i, farkas.m_order, map);
		}	
		
		/*
		 * Removing zero factors is trivial for Isabelle, so the simplifier
		 * without any rules is used here.
		 * 
		 * NOTE: This is always the last rule, so there is no special case
		 *       treatment necessary.
		 */
		if (! m_fastProofs) {
			writeLemmaString("by ");
			writeLemmaString(m_simplifier.getRule());
		}
		else {
			writeLemmaString(m_simplifier.getRule());
			writeLemmaString(")");
		}
		
		// finish proof
		writeLemmaString("\nthus ?thesis by (rule HOL.FalseE)\nqed\n");
		
		// real proof
		m_converter.convert(lemma);
		writeString("\"\nby (rule ");
		writeString(LA_LEMMA_PREFIX);
		writeString(Integer.toString(m_lemmaNumber));
		writeString(")\n");
	}
	
	/**
	 * This method creates the pattern from the lemma. It has to be created
	 * anyway to write it to the output, but this way also no term mapping to
	 * pattern variables is needed.
	 * The procedure is to unpack the term up to the summands level of the
	 * canonical sum, then insert the according pattern variables, and finally
	 * pack the term again. 
	 * 
	 * @param disjuncts the original disjuncts
	 * @param ineqs data structure
	 * @param arithType type of logic
	 * @return the disjunction with the terms replaced by pattern variables
	 */
	private ApplicationTerm createPatternLemma(Term[] disjuncts,
			final IneqInfo ineqs, final EArith arithType) {
		final Term[] newDisjuncts = new Term[disjuncts.length];
		
		// map for pattern variable indices
		final HashMap<Term, Integer> term2index = new HashMap<Term, Integer>();
		
		final Term[] params = new Term[0];
		final Sort[] paramSorts = new Sort[0];
		
		// unpack terms and pack them again
		for (int i = 0; i < disjuncts.length; ++i) {
			Term next = disjuncts[i];
			final boolean isNegated = next instanceof ApplicationTerm;
			
			// unpack negation to handle terms equally
			if (isNegated) {
				assert ((((ApplicationTerm)next).getFunction() ==
								m_theory.m_Not) &&
						(((ApplicationTerm)next).getParameters().length == 1));
				next = ((ApplicationTerm)next).getParameters()[0];
			}
			
			// unpack :quoted literal
			assert ((next instanceof AnnotatedTerm) &&
					(((AnnotatedTerm)next).getAnnotations().length == 1) &&
					(((AnnotatedTerm)next).getAnnotations()[0].getKey() ==
							":quoted") &&
					(((AnnotatedTerm)next).getSubterm() instanceof
							ApplicationTerm));
			final ApplicationTerm laTerm =
					(ApplicationTerm)((AnnotatedTerm)next).getSubterm();
			
			// unpack (in)equality
			assert (laTerm.getParameters().length == 2);
			final Term lhs = laTerm.getParameters()[0];
			
			// go through summands
			final Term[] summands;
			final FunctionSymbol plus;
			if (lhs instanceof ApplicationTerm) {
				final ApplicationTerm aLhs = (ApplicationTerm)lhs;
				plus = aLhs.getFunction();
				
				// sum
				if (plus.getName() != "+") {
					summands = new Term[1];
					summands[0] = lhs;
				}
				// single summand
				else {
					summands = aLhs.getParameters();
				}
			}
			// single summand
			else {
				plus = null;
				summands = new Term[1];
				summands[0] = lhs;
			}
			
			// unpack factors and minus and replace variable, then pack again
			final Term[] newSummands = new Term[summands.length];
			for (int j = 0; j < summands.length; ++j) {
				final Term summand = summands[j];
				
				// last summand could be the constant
				if (j == summands.length - 1) {
					if (summand instanceof ConstantTerm) {
						newSummands[j] = summand;
						break;
					}
					else if (summand instanceof ApplicationTerm) {
						final ApplicationTerm aSummand =
								(ApplicationTerm)summand;
						// negative constant
						if ((aSummand.getFunction().getName() == "-") &&
							(aSummand.getParameters()[0] instanceof
									ConstantTerm)) {
							assert (((ApplicationTerm)summand).
									getParameters().length == 1);
							newSummands[j] = summand;
							break;
						}
						// constant fraction
						else if (aSummand.getFunction().getName() == "/") {
							assert (((ApplicationTerm)summand).
									getParameters().length == 2);
							if (aSummand.getParameters()[1] instanceof
									ConstantTerm) {
								assert ((aSummand.getParameters()[0] instanceof
										ConstantTerm) ||
										((aSummand.getParameters()[0]
												instanceof ApplicationTerm) &&
										(((ApplicationTerm)aSummand.
												getParameters()[0]).
												getFunction().getName() ==
												"-")));
								newSummands[j] = summand;
								break;
							}
						}
					}
				}
				
				if (summand instanceof ApplicationTerm) {
					final ApplicationTerm aSummand = (ApplicationTerm)summand;
					final FunctionSymbol summandSymbol =
							aSummand.getFunction();
					final String summandName = summandSymbol.getName();
					
					// factor
					if (summandName == "*") {
						final Term[] factors = aSummand.getParameters();
						assert (factors.length == 2);
						newSummands[j] = m_theory.term(summandSymbol,
								factors[0], getPatternVar(term2index,
										factors[1], params, paramSorts,
										arithType));
					}
					// minus
					else if (summandName == "-") {
						assert (aSummand.getParameters().length == 1);
						newSummands[j] =
								m_theory.term(summandSymbol,
										getPatternVar(term2index,
												aSummand.getParameters()[0],
												params, paramSorts,
												arithType));
					}
					else {
						newSummands[j] = getPatternVar(term2index, summand,
								params, paramSorts, arithType);
					}
				}
			}
			
			// pack sum again, but not if no sum before
			final Term newLhs;
			if (newSummands.length == 1) {
				newLhs = newSummands[0];
			}
			else {
				assert (newSummands.length > 1);
				newLhs = m_theory.term(plus, newSummands);
			}
			
			// pack LA term
			final ApplicationTerm newLaTerm =
					m_theory.term(laTerm.getFunction(), newLhs,
							laTerm.getParameters()[1]);
			// pack :quoted annotation
			Term newNext = m_theory.annotatedTerm(
					((AnnotatedTerm)next).getAnnotations(), newLaTerm);
			// pack negation if existent before
			if (isNegated) {
				newNext = m_theory.not(newNext);
			}
			
			newDisjuncts[i] = newNext;
			
			/*
			 * NOTE: The negation is set in the counter-intuitive way,
			 *       because it will be inverted by de Morgan's rule later.
			 */
			ineqs.add(i, newLaTerm, ! isNegated, arithType); 
		}
		
		return m_theory.term(m_theory.m_Or, newDisjuncts);
	}
	
	/**
	 * This method returns the variable term given the original term and a map.
	 * 
	 * @param term2index map from original terms to indices
	 * @param term original term
	 * @param parameters parameters
	 * @param parameterSorts parameter sorts
	 * @return the pattern variable
	 */
	private ApplicationTerm getPatternVar(
			final HashMap<Term, Integer> term2index,
			Term term, final Term[] parameters,
			final Sort[] parameterSorts, final EArith arithType) {
		// ignore 'to_real' prefix to talk about the same terms
		FunctionSymbol toReal = null;
		if ((arithType == EArith.mixed) &&
				(term instanceof ApplicationTerm)) {
			final ApplicationTerm aTerm = (ApplicationTerm)term;
			toReal = aTerm.getFunction();
			if (toReal.getName() == "to_real") {
				assert (aTerm.getParameters().length == 1);
				term = aTerm.getParameters()[0];
			}
			else {
				toReal = null;
			}
		}
		
		Integer index = term2index.get(term);
		if (index == null) {
			index = term2index.size() + 1;
			term2index.put(term, index);
		}
		
		final String name = LA_LEMMA_VAR + index;
		ApplicationTerm result = m_theory.term(name, parameters);
		
		if (result == null) {
			result = m_theory.term(
					m_theory.declareFunction(
							name, parameterSorts, term.getSort()), parameters);
		}
		
		// add to_real again
		if (toReal != null) {
			result = m_theory.term(toReal, result);
		}
		
		return result;
	}
	
	/**
	 * This method translates one step of de Morgan's rule without any use of
	 * substitution.
	 * 
	 * Note that the negation is swapped here and hence its internal status was
	 * already set to the inverted value before. That is why the flag in the
	 * data structure seems to be set wrong, but it is correct.
	 * 
	 * @param ineqs data structure
	 * @param index index
	 */
	private void deMorgan(final IneqInfo ineqs, final int index) {
		IneqInfo.IneqLiteral literal = ineqs.m_literals[index];
		
		/*
		 * NOTE: The first 'apply rule' works like a later 'apply erule',
		 * so no 'erule' here. This only works, since this is the first rule
		 * in the lemma proof.
		 * Also, in the fast proof the first 'apply' has to be executed outside
		 * the 'by'.
		 */
		if (index == 0) {
			if (literal.isNegated()) {
				writeLemmaString("apply (rule de_Morgan_disj_pos_first)\n");
			}
			else {
				writeLemmaString("apply (rule de_Morgan_disj_neg_first)\n");
			}
			
			// start fast proof here
			if (m_fastProofs) {
				writeLemmaString("by (");
			}
		}
		else if (ineqs.isLast(index)) {
			if (! literal.isNegated()) {
				writeRule("erule de_Morgan_disj_neg_last");
			}
		}
		else {
			if (literal.isNegated()) {
				writeRule("erule de_Morgan_disj_pos");
			}
			else {
				writeRule("erule de_Morgan_disj_neg");
			}
		}
	}
	
	/**
	 * This method multiplies a linear inequality with a coefficient
	 * (the Farkas coefficient).
	 * 
	 * @param ineqs data structure
	 * @param index index
	 * @param fRes farkas result wrapper
	 * @param arithType type of logic
	 * @return tuple: (true iff factor is not 1; order signs of the literals)
	 */
	private FarkasResult farkasCoefficient(final IneqInfo ineqs,
			final int index, final FarkasResult fRes, final EArith arithType) {
		final Term factor = ineqs.getFactorTerm(index);
		EOrder order = fRes.m_order;
		
		// ignore factor 1
		if (factor instanceof ConstantTerm) {
			final ConstantTerm cFactor = (ConstantTerm)factor;
			assert (cFactor.getValue() instanceof BigInteger);
			
			if (((BigInteger)cFactor.getValue()).equals(BigInteger.ONE)) {
				switch (ineqs.m_literals[index].m_ineqType) {
					case pos_le:
						if (index == 0) {
							return new FarkasResult(false, EOrder.le_le,
									fRes.m_firstInt);
						}
						else {
							return new FarkasResult(false,
									convertOrder(order, true),
									fRes.m_firstInt);
						}
					case pos_less:
						switch (arithType) {
						case real:
							if (index == 0) {
								return new FarkasResult(false, EOrder.less_le,
										fRes.m_firstInt);
							}
							else {
								return new FarkasResult(false,
										convertOrder(order, false),
										fRes.m_firstInt);
							}
						case mixed:
							if (index == 0) {
								return new FarkasResult(false,
									(ineqs.m_literals[index].m_isIntegral) ?
												EOrder.le_le :
												EOrder.less_le,
									fRes.m_firstInt);
							}
							else {
								return new FarkasResult(false,
										convertOrder(order,
												ineqs.m_literals[index].
												m_isIntegral),
										fRes.m_firstInt);
							}
						default:
							assert false;
							throw new IllegalArgumentException(
									"For integers '<' never occurs.");
						}
						
					// do not return here, since equality has to be unpacked
					case eq:
						if (index == 0) {
							order = EOrder.le_le;
						}
						else {
							order = convertOrder(order, true);
						}
						break;
					default:
						assert false;
						throw new IllegalArgumentException(
								"for factor '1' the literal can only be " +
								"positive or equality.");
				}
			}
		}
		
		final String rule;
		switch (ineqs.m_literals[index].m_ineqType) {
		case pos_le:
			assert (factor instanceof ConstantTerm);
			rule = "farkas_pos_le";
			order = convertOrder(order, true);
			break;
		case neg_le:
			assert (factor instanceof ApplicationTerm);
			switch (arithType) {
				case integer:
					rule = "int_farkas_neg_le";
					order = convertOrder(order, true);
					break;
				case real:
					rule = "real_farkas_neg_le";
					order = convertOrder(order, false);
					break;
				case mixed:
					if (ineqs.m_literals[index].m_isIntegral) {
						rule = "int_farkas_neg_le";
						order = convertOrder(order, true);
					}
					else {
						rule = "real_farkas_neg_le";
						order = convertOrder(order, false);
					}
					break;
				default:
					assert false;
					throw new IllegalArgumentException(
							"The logics type is unknown.");
			}
			break;
		case pos_less:
			assert (factor instanceof ConstantTerm);
			
			switch (arithType) {
				case integer:
					rule = "int_farkas_pos_less";
					order = convertOrder(order, true);
					break;
				case real:
					rule = "real_farkas_pos_less";
					order = convertOrder(order, false);
					break;
				case mixed:
					if (ineqs.m_literals[index].m_isIntegral) {
						rule = "int_farkas_pos_less";
						order = convertOrder(order, true);
					}
					else {
						rule = "real_farkas_pos_less";
						order = convertOrder(order, false);
					}
					break;
				default:
					assert false;
					throw new IllegalArgumentException(
							"The logics type is unknown.");
			}
			break;
		case neg_less:
			assert (factor instanceof ApplicationTerm);
			rule = "farkas_neg_less";
			order = convertOrder(order, true);
			break;
		// equality is handled differently
		case eq:
			rule = "farkas_eq";
			order = convertOrder(order, true);
			break;
		default:
			assert false;
			throw new IllegalArgumentException(
					"The ordering type is unknown.");
		}
		
		// all inequalities are handled very similarly
		
		writeLemmaString(m_startLine);
		writeLemmaString("erule ");
		writeLemmaString(rule);
		if (index == 0) {
			writeLemmaString("_first");
		}
		else if (ineqs.isLast(index)) {
			writeLemmaString("_last");
		}
		writeLemmaString(" [where c = \"");
		
		/*
		 * Do not annotate the number with a type since Isabelle then adds a
		 * cast and messes up everything.
		 */
		if (factor instanceof ApplicationTerm) {
			assert (((ApplicationTerm)factor).getFunction().getName() == "-");
			writeLemmaString("- ");
			writeLemmaString(((ApplicationTerm)factor).getParameters()[0].
					toString());
		}
		else {
			assert (factor instanceof ConstantTerm);
			writeLemmaString(((ConstantTerm)factor).getValue().toString());
		}
		writeLemmaString("\"]");
		writeLemmaString(m_endLine);
		
		// additional simplifier application for inequalities
		if (ineqs.m_literals[index].m_ineqType != EIneqType.eq) {
			writeRule(m_simplifier.getRule());
		}
		
		return new FarkasResult(true, order, fRes.m_firstInt);
	}
	
	/**
	 * This method applies the distributivity rule. Constant factors are
	 * charged against each other to have a resulting normal form.
	 * 
	 * Since the factors are the Farkas coefficients, they can only be
	 * integers.
	 * 
	 * In a simplified version (no corner cases) this looks as follows:
	 * 
	 * Before: c * (s1 + ... + sn + d)
	 * After:  c1 * x1 + ... + cn * xn + e
	 *         where 'si = (ci/c) * xi' and 'e = c * d' 
	 * 
	 * @param ineqs data structure
	 * @param index index
	 * @param map maps terms to factors
	 * @param fRes farkas result wrapper
	 * @param arithType type of logic
	 */
	private void distributivity(final IneqInfo ineqs, final int index,
			final Var2FactorMap map, final FarkasResult fRes,
			final EArith arithType) {
		final boolean write = fRes.m_applyDistributivity;
		final EOrder order = fRes.m_order;
		final Term[] summands = ineqs.m_literals[index].m_summands;
		StringBuilder firstLine = null;
		
		if (write) {
			firstLine = new StringBuilder();
			// first step
			firstLine.append(m_startLine);
			firstLine.append("erule dist");
			
			// <= or < ?
			if (index == 0) {
				switch (order) {
					case le_le:
					case le_less:
						firstLine.append("_le");
						break;
					default:
						firstLine.append("_less");
				}
			}
			else {
				switch (order) {
					case le_le:
					case less_le:
						firstLine.append("_le");
						break;
					default:
						firstLine.append("_less");
				}
			}
			
			// first or last literal?
			if (index == 0) {
				firstLine.append("_first");
			}
			else if (ineqs.isLast(index)) {
				firstLine.append("_last");
			}
			firstLine.append(m_endLine);
		}
		
		// Farkas coefficient
		final BigInteger factor;
		if (ineqs.m_factors[index] instanceof ConstantTerm) {
			factor = (BigInteger)
					((ConstantTerm)ineqs.m_factors[index]).getValue();
		}
		else {
			assert ((ineqs.m_factors[index] instanceof ApplicationTerm) &&
					(((ApplicationTerm)ineqs.m_factors[index]).getFunction().
							getName() == "-") &&
					(((ApplicationTerm)ineqs.m_factors[index]).getParameters().
							length == 1));
			factor = ((BigInteger)
					((ConstantTerm)((ApplicationTerm)ineqs.m_factors[index]).
							getParameters()[0]).getValue()).negate();
		}
		
		// prefix 
		final String prefix;
		if (factor.compareTo(BigInteger.ZERO) == 1) {
			prefix = "subst s_dist_pos_";
		}
		else {
			prefix = "subst s_dist_neg_";
		}
		
		// for integers, a constant has been added, so process this first
		switch (arithType) {
			// if literal is integral, exploit non-breaking switch
			case mixed:
				if (! ineqs.m_literals[index].m_isIntegral) {
					break;
				}
			case integer:
				switch (ineqs.m_literals[index].m_ineqType) {
					case pos_less:
						map.updateConstant(Rational.valueOf(factor,
								BigInteger.ONE));
						if (write) {
							writeLemmaString(firstLine.toString());
							firstLine = null;
							writeLemmaString(m_startLine);
							writeLemmaString(prefix);
							writeLemmaString("pos");
							writeLemmaString(m_endLine);
						}
						break;
					case neg_le:
						map.updateConstant(Rational.valueOf(factor,
								BigInteger.ONE).negate());
						if (write) {
							writeLemmaString(firstLine.toString());
							firstLine = null;
							writeLemmaString(m_startLine);
							writeLemmaString(prefix);
							writeLemmaString("neg");
							writeLemmaString(m_endLine);
						}
						break;
					default:
				}
				break;
			case real:
				break;
			default:
				assert false;
				throw new IllegalArgumentException(
						"The logics type is unknown.");
		}
		
		// first line may only be written if there is a distributivity
		if (write && (firstLine != null) &&
				((summands.length > 1) || ineqs.hasIntegerConstant(index))) {
			writeLemmaString(firstLine.toString());
			firstLine = null;
		}
		
		final Term falseTerm = m_theory.FALSE;
		
		// distributivity steps (from right to left)
		for (int i = summands.length - 1; i >= 0; --i) {
			// remember inner term ('False' for constants)
			Term innerTerm;
			final FactorWrapper summandFactor;
			
			/* find factor and inner term */
			
			// positive constant
			if (summands[i] instanceof ConstantTerm) {
				innerTerm = falseTerm;
				final ConstantTerm cTerm = (ConstantTerm)summands[i];
				if (cTerm.getValue() instanceof BigInteger) {
					summandFactor = new FactorWrapper((BigInteger)
							((ConstantTerm)summands[i]).getValue());
				}
				else {
					assert (cTerm.getValue() instanceof BigDecimal);
					summandFactor = new FactorWrapper((BigDecimal)
							((ConstantTerm)summands[i]).getValue());
				}
				
				if (write && (i > 0)) {
					writeLemmaString(m_startLine);
					writeLemmaString(prefix);
					writeLemmaString("pos");
					writeLemmaString(m_endLine);
				}
			}
			else {
				assert (summands[i] instanceof ApplicationTerm);
				final ApplicationTerm summand = (ApplicationTerm)summands[i];
				// negative summand
				if (summand.getFunction().getName() == "-") {
					assert (summand.getParameters().length == 1);
					innerTerm = summand.getParameters()[0];
					// negative constant
					if (innerTerm instanceof ConstantTerm) {
						if (((ConstantTerm)innerTerm).getValue() instanceof
								BigInteger) {
							summandFactor = new FactorWrapper(
									((BigInteger)((ConstantTerm)innerTerm).
											getValue()).negate());
						}
						else {
							assert (((ConstantTerm)innerTerm).getValue()
									instanceof BigDecimal);
							summandFactor = new FactorWrapper(
									((BigDecimal)((ConstantTerm)innerTerm).
											getValue()).negate());
						}
						innerTerm = falseTerm;
					}
					// negative variable
					else {
						summandFactor =
								new FactorWrapper(Rational.ONE.negate());
					}
					
					if (write) {
						if (i == 0) {
							if (factor.compareTo(BigInteger.ZERO) == 1) {
								writeRule("subst s_plus_minus");
							}
							else {
								writeRule("subst s_minus_minus");
							}
						}
						else {
							writeLemmaString(m_startLine);
							writeLemmaString(prefix);
							writeLemmaString("neg");
							writeLemmaString(m_endLine);
						}
					}
				}
				// variable with factor
				else if (summand.getFunction().getName() == "*") {
					assert (summand.getParameters().length == 2);
					// temporarily bind the factor here
					innerTerm = summand.getParameters()[0];
					// positive factor
					if (innerTerm instanceof ConstantTerm) {
						final ConstantTerm cTerm = (ConstantTerm)innerTerm;
						if (cTerm.getValue() instanceof BigInteger) {
							summandFactor = new FactorWrapper((BigInteger)
									cTerm.getValue());
						}
						else {
							assert (cTerm.getValue() instanceof BigDecimal);
							summandFactor = new FactorWrapper((BigDecimal)
									cTerm.getValue());
						}
					}
					else {
						assert (innerTerm instanceof ApplicationTerm);
						final ApplicationTerm aInnerTerm =
								(ApplicationTerm)innerTerm;
						// negative factor
						if (aInnerTerm.getFunction().getName() == "-") {
							assert ((aInnerTerm.getParameters().length == 1) &&
								(aInnerTerm.getParameters()[0] instanceof
										ConstantTerm));
							final ConstantTerm cTerm = (ConstantTerm)
									aInnerTerm.getParameters()[0];
							if (cTerm.getValue() instanceof BigInteger) {
								summandFactor = new FactorWrapper((BigInteger)
										cTerm.getValue());
							}
							else {
								assert (cTerm.getValue() instanceof
										BigDecimal);
								summandFactor = new FactorWrapper((BigDecimal)
										cTerm.getValue());
							}
							summandFactor.negate();
						}
						// fraction factor
						else {
							assert ((aInnerTerm.getFunction().getName() == "/")
									&&
									(aInnerTerm.getParameters().length == 2) &&
									(aInnerTerm.getParameters()[1] instanceof
											ConstantTerm) &&
									(((ConstantTerm)aInnerTerm.
													getParameters()[1]).
													getValue()
													instanceof BigInteger));
							// temporarily bind the factor here
							innerTerm = aInnerTerm.getParameters()[0];
							final BigInteger denominator =
									(BigInteger)((ConstantTerm)
											aInnerTerm.getParameters()[1]).
											getValue();
							
							// negative fraction
							if (innerTerm instanceof ApplicationTerm) {
								assert ((((ApplicationTerm)innerTerm).
										getFunction().getName() == "-") &&
										(((ApplicationTerm)innerTerm).
												getParameters().length == 1) &&
										(((ApplicationTerm)innerTerm).
												getParameters()[0] instanceof
												ConstantTerm) &&
										(((ConstantTerm)
												((ApplicationTerm)innerTerm).
												getParameters()[0]).getValue()
												instanceof BigInteger));
								summandFactor = new FactorWrapper(
										Rational.valueOf(
											(BigInteger)((ConstantTerm)
												((ApplicationTerm)innerTerm).
												getParameters()[0]).
												getValue(),
											denominator));
								summandFactor.negate();
							}
							// positive fraction
							else {
								assert ((innerTerm instanceof ConstantTerm) &&
										((ConstantTerm)innerTerm).getValue()
										instanceof BigInteger);
								summandFactor = new FactorWrapper(
										Rational.valueOf((BigInteger)
											((ConstantTerm)innerTerm).
												getValue(),
											denominator));
							}
						}
					}
					innerTerm = summand.getParameters()[1];
					
					if (write) {
						if (i == 0) {
							writeRule("subst s_factor");
						}
						else {
							writeRule("subst s_dist_factor");
						}
						writeRule(m_simplifier.getRule());
					}
				}
				// constant fraction
				else if (summand.getFunction().getName() == "/") {
					assert ((summand.getParameters().length == 2) &&
							(summand.getParameters()[1] instanceof
									ConstantTerm) &&
							(((ConstantTerm)summand.
									getParameters()[1]).
									getValue()
									instanceof BigInteger) &&
							(i > 0));
					
					// temporarily bind the factor here
					innerTerm = summand.getParameters()[0];
					final BigInteger denominator =
							(BigInteger)((ConstantTerm)
									summand.getParameters()[1]).
									getValue();
					
					// negative fraction
					if (innerTerm instanceof ApplicationTerm) {
						assert ((((ApplicationTerm)innerTerm).getFunction().
								getName() == "-") &&
								(((ApplicationTerm)innerTerm).getParameters().
										length == 1) &&
								(((ApplicationTerm)innerTerm).
										getParameters()[0] instanceof
										ConstantTerm) &&
								(((ConstantTerm)
										((ApplicationTerm)innerTerm).
										getParameters()[0]).getValue()
										instanceof BigInteger));
						
						summandFactor = new FactorWrapper(
								Rational.valueOf(
									(BigInteger)((ConstantTerm)
										((ApplicationTerm)innerTerm).
										getParameters()[0]).
										getValue(),
									denominator));
						summandFactor.negate();
					}
					else {
						assert ((innerTerm instanceof ConstantTerm) &&
								((ConstantTerm)innerTerm).getValue()
								instanceof BigInteger);
						summandFactor = new FactorWrapper(
								Rational.valueOf((BigInteger)
									((ConstantTerm)innerTerm).
										getValue(),
									denominator));
					}
					
					// fractions have minus sign inside, so always use pos rule
					if (write) {
						writeLemmaString(m_startLine);
						writeLemmaString(prefix);
						writeLemmaString("pos");
						writeLemmaString(m_endLine);
					}
					
					innerTerm = falseTerm;
				}
				// positive variable
				else {
					innerTerm = summand;
					summandFactor = new FactorWrapper(Rational.ONE);
					
					if (write && (i > 0)) {
						writeLemmaString(m_startLine);
						writeLemmaString(prefix);
						writeLemmaString("pos");
						writeLemmaString(m_endLine);
					}
				}
			}
			
			summandFactor.mul((Rational.valueOf(factor, BigInteger.ONE)));
			// constant
			if (innerTerm == falseTerm) {
				map.updateConstant(summandFactor.m_factor);
			}
			// variable
			else {
				// ignore 'to_real' prefix to talk about the same terms
				if ((arithType == EArith.mixed) &&
					(innerTerm instanceof ApplicationTerm)) {
					final ApplicationTerm aTerm = (ApplicationTerm)innerTerm;
					final String function = aTerm.getFunction().getName();
					if (function == "to_real") {
						assert (aTerm.getParameters().length == 1);
						map.update((ApplicationTerm)aTerm.getParameters()[0],
								summandFactor.m_factor);
					}
					else {
						map.update(innerTerm, summandFactor.m_factor);
					}
				}
				else {
					map.update(innerTerm, summandFactor.m_factor);
				}
			}
		}
		
		/*
		 * Only write this in case the distributivity is needed, i.e., there
		 * are at least two summands. This can also be the case if there is a
		 * single term, but the integer constant (1) was inserted.
		 */
		if (write &&
				((summands.length > 1) || ineqs.hasIntegerConstant(index))) {
			writeRule("rule HOL.refl");
		}
	}
	
	/**
	 * This method merges two literals. This is very easy, since the rule
	 * does everything automatically. Only for the last two literals the
	 * rule slightly differs.
	 * 
	 * @param ineqs data structure
	 * @param index index
	 * @param fRes farkas result wrapper
	 * @param arithType type of logic
	 * @return 'le_le' iff the sign stays '<=', 'less_less' otherwise
	 */
	private FarkasResult mergeLiterals(final IneqInfo ineqs, final int index,
			final FarkasResult fRes, final EArith arithType)
			{
		// keeps track of the type of the sum so far in mixed logic
		final boolean resultIsInt;
		writeLemmaString(m_startLine);
		
		// special rule for mixed case: adding integer and real literals
		if (arithType == EArith.mixed) {
			assert (index > 0);
			boolean secondInt = ineqs.m_literals[index].m_isIntegral;
			if (fRes.m_firstInt && (! secondInt)) {
				writeLemmaString("erule ir_merge_ineqs_");
				resultIsInt = false;
			}
			else if ((! fRes.m_firstInt) && secondInt) {
				writeLemmaString("erule ri_merge_ineqs_");
				resultIsInt = false;
			}
			else {
				writeLemmaString("erule merge_ineqs_");
				resultIsInt = true;
			}
		}
		else {
			writeLemmaString("erule merge_ineqs_");
			resultIsInt = true;
		}
		
		final EOrder order;
		switch (fRes.m_order) {
		case le_le:
			writeLemmaString("le_le");
			order = EOrder.le_le;
			break;
		case le_less:
			writeLemmaString("le_less");
			order = EOrder.less_less;
			break;
		case less_le:
			writeLemmaString("less_le");
			order = EOrder.less_less;
			break;
		case less_less:
			writeLemmaString("less_less");
			order = EOrder.less_less;
			break;
		default:
			assert false;
			throw new IllegalArgumentException(
					"The ordering type is unknown.");
		}
		
		if (ineqs.isLast(index)) {
			writeLemmaString("_last");
		}
		writeLemmaString(m_endLine);
		
		return new FarkasResult(fRes.m_applyDistributivity, order,
				fRes.m_firstInt && resultIsInt);
	}
	
	/**
	 * This method computes the simplified sum after merging two literals.
	 * For that a map has been updated with the new factors before, so the
	 * only thing that happens here is extracting the data and writing the
	 * resulting term in Isabelle syntax.
	 * 
	 * The equality of the old and the new (simplified) term is proven with
	 * the simplifier.
	 * 
	 * @param ineqs data structure
	 * @param index index
	 * @param order order sign of the literals
	 * @param map maps terms to factors
	 */
	private void simplify(final IneqInfo ineqs, final int index,
			final EOrder order, final Var2FactorMap map) {
		writeLemmaString(m_startLine);
		
		if (order == EOrder.le_le) {
			writeLemmaString("erule simplify_le");
		}
		else {
			writeLemmaString("erule simplify_less");
		}
		
		if (ineqs.isLast(index)) {
			writeLemmaString("_last");
		}
		writeLemmaString(" [where y = \"");
		m_converter.convertFactorMap(
				map.m_constant, map.m_map.entrySet(), m_lemmaAppendable);
		writeLemmaString("\"]");
		writeLemmaString(m_endLine);
		
		writeRule(m_simplifier.getRule());
	}
	
	/**
	 * This class is used as a data structure for the LA lemma conversion.
	 * It represents the literals in the conjunction of literals (after
	 * applying de Morgan's rule), and the Farkas coefficients. 
	 * 
	 */
	private class IneqInfo {
		/**
		 * This class represents a literal (see {@link IneqInfo}).
		 * It consists of a summand array and an (in)equality type. The
		 * right-hand-side is known to be always zero.
		 */
		private class IneqLiteral {
			// summands
			final Term[] m_summands;
			// type of inequality
			final EIneqType m_ineqType;
			// integrality cache for not computing it more than once
			boolean m_isIntegral;
			
			/**
			 * @param summands the summands
			 * @param ineqType type of inequality
			 * @param arithType arithType type of logic
			 */
			public IneqLiteral(final Term[] summands, final EIneqType ineqType,
					final EArith arithType) {
				m_summands = summands;
				m_ineqType = ineqType;
				if (arithType == EArith.mixed) {
					final Sort intSort = m_theory.getNumericSort();
					m_isIntegral = true;
					for (int i = 0; i < summands.length; ++i) {
						if (! summands[i].getSort().equals(intSort)) {
								m_isIntegral = false;
								break;
						}
					}
				}
				else {
					m_isIntegral = (arithType == EArith.integer);
				}
			}
			
			/**
			 * This method tells if the literal is negated.
			 * 
			 * @return true iff the literal is negated
			 */
			public boolean isNegated() {
				switch (m_ineqType) {
				case neg_le:
				case neg_less:
					return true;
				case pos_le:
				case pos_less:
				case eq:
					return false;
				default:
					assert false;
					throw new IllegalArgumentException(
							"The ordering type is unknown.");
				}
			}
			
			@Override
			public String toString() {
				final StringBuilder builder = new StringBuilder();
				String append = "";
				builder.append((isNegated() ? "[(+ " : "[(+ "));
				for (int i = 0; i < m_summands.length; ++i) {
					builder.append(append);
					append = ", ";
					builder.append(m_summands[i]);
				}
				switch (m_ineqType) {
				case neg_le:
				case pos_le:
					builder.append(") <= 0]");
					break;
				case neg_less:
				case pos_less:
					builder.append(") < 0]");
					break;
				case eq:
					builder.append(") = 0]");
					break;
				default:
					assert false;
					throw new IllegalArgumentException(
							"The ordering type is unknown.");
				}
				return builder.toString();
			}
		}
		
		// literals
		final IneqLiteral[] m_literals;
		// factors
		final Object[] m_factors;
		
		/**
		 * @param length length of the disjuncts
		 * @param factors the Farkas coefficients 
		 * @param arithType type of logic
		 */
		public IneqInfo(final int length, final Object[] factors,
				final EArith arithType) {
			m_factors = factors;
			m_literals = new IneqLiteral[factors.length];
		}
		
		/**
		 * This method tells if an index is the last one in the conjunction.
		 * 
		 * @param index index
		 * @return true iff the index is the last one
		 */
		public boolean isLast(final int index) {
			return (index == m_literals.length - 1);
		}
		
		/**
		 * This method adds a new literal.
		 * 
		 * @param index the index
		 * @param literal the literal
		 * @param isNegated true iff literal is negated
		 * @param arithType type of logic
		 */
		public void add(final int index, final ApplicationTerm literal,
				final boolean isNegated, final EArith arithType) {
			final String function = literal.getFunction().getName();
			final EIneqType ineqType;
			if (function == "<=") {
				if (isNegated) {
					ineqType = EIneqType.neg_le;
				}
				else {
					ineqType = EIneqType.pos_le;
				}
			}
			else if (function == "<") {
				if (isNegated) {
					ineqType = EIneqType.neg_less;
				}
				else {
					ineqType = EIneqType.pos_less;
				}
			}
			else {
				assert ((function == "=") && (! isNegated));
				ineqType = EIneqType.eq;
			}
			
			// left-hand side is either a sum or a term seen as a variable
			assert ((literal.getParameters().length == 2) &&
					(literal.getParameters()[0] instanceof ApplicationTerm));
			
			if (((ApplicationTerm)literal.getParameters()[0]).getFunction().
					getName() == "+") {
				m_literals[index] = new IneqLiteral(
						((ApplicationTerm)literal.getParameters()[0]).
								getParameters(), ineqType,
								arithType);
			}
			else {
				final Term[] unarySummand = new Term[1];
				unarySummand[0] = literal.getParameters()[0];
				m_literals[index] = new IneqLiteral(unarySummand, ineqType,
						arithType);
			}
		}
		
		/**
		 * This method gives the Farkas coefficient as a term.
		 * 
		 * @param i index
		 * @return Farkas coefficient as a term
		 */
		public Term getFactorTerm(final int i) {
			return (Term)m_factors[i];
		}
		
		/**
		 * This method indicates whether a literal has inserted the integer
		 * constant 1.
		 * 
		 * @param index the index of the literal
		 * @return true iff the literal inserted the integer constant
		 */
		public boolean hasIntegerConstant(final int index) {
			return (m_literals[index].m_isIntegral) &&
					((m_literals[index].m_ineqType == EIneqType.pos_less) ||
						(m_literals[index].m_ineqType == EIneqType.neg_le));
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			String append = "";
			builder.append("{");
			for (int i = 0; i < m_literals.length; ++i) {
				builder.append(append);
				append = ", ";
				builder.append(m_factors[i]);
				builder.append(" * ");
				builder.append(m_literals[i]);
			}
			builder.append("}");
			return builder.toString();
		}
	}
	
	/**
	 * This enum gives the type of linear inequality of the LA lemma literals.
	 */
	private enum EIneqType {
		/**
		 * positive less-equal
		 */
		pos_le,
		/**
		 * negative less-equal
		 */
		neg_le,
		/**
		 * positive less
		 */
		pos_less,
		/**
		 * negative less
		 */
		neg_less,
		/**
		 * positive equality
		 */
		eq,
	}
	
	/**
	 * type of arithmetic logics
	 */
	private enum EArith {
		integer, real, mixed;
	}
	
	/**
	 * type of order signs ('<' vs. '<=') of the first and the second literal
	 */
	private enum EOrder {
		/**
		 * <=, <=
		 */
		le_le,
		/**
		 * <=, <
		 */
		le_less,
		/**
		 * <, <=
		 */
		less_le,
		/**
		 * <, <
		 */
		less_less
	}
	
	/**
	 * This method converts the order sign according to the next one.
	 * 
	 * @param order the old order
	 * @param isLe true iff second order sign shall become '<='
	 * @return changed order
	 */
	private EOrder convertOrder(final EOrder order, final boolean isLe) {
		switch (order) {
			case le_le:
				if (! isLe) {
					return EOrder.le_less;
				}
				break;
			case le_less:
				if (isLe) {
					return EOrder.le_le;
				}
				break;
			case less_le:
				if (! isLe) {
					return EOrder.less_less;
				}
				break;
			case less_less:
				if (isLe) {
					return EOrder.less_le;
				}
				break;
			default:
				assert false;
				throw new IllegalArgumentException(
						"The ordering type is unknown.");
		}
		return order;
	}
	
	/**
	 * This class wraps the result of the methods, especially inserting Farkas
	 * coefficients, since Java uses call-by-value for booleans and enums.
	 */
	private class FarkasResult {
		// true iff distributivity has to be used
		final boolean m_applyDistributivity;
		// order sign of the literals
		final EOrder m_order;
		// true iff sum so far is of type integer in mixed logic
		final boolean m_firstInt;
		
		/**
		 * @param applyDistributivity true iff distributivity has to be used
		 * @param order order sign of the literals
		 * @param firstInt true iff sum so far is of type integer (mixed logic)
		 */
		public FarkasResult(final boolean applyDistributivity,
				final EOrder order, final boolean firstInt) {
			m_applyDistributivity = applyDistributivity;
			m_order = order;
			m_firstInt = firstInt;
		}
		
		@Override
		public String toString() {
			return "(" + m_applyDistributivity + ", " + m_order + ")";
		}
	}
	
	/**
	 * This class represents a factor of a variable in LA literals.
	 * It is mainly used to convert integers and decimals with polymorphism.
	 */
	class FactorWrapper {
		// factor
		Rational m_factor;
		
		/**
		 * @param bigInt the integer factor
		 */
		public FactorWrapper(final BigInteger bigInt) {
			m_factor = toRational(bigInt);
		}
		
		/**
		 * @param bigDec the decimal factor
		 */
		public FactorWrapper(final BigDecimal bigDec) {
			m_factor = toRational(bigDec);
		}
		
		/**
		 * @param rational the rational factor
		 */
		public FactorWrapper(final Rational rational) {
			m_factor = rational;
		}
		
		/**
		 * This method converts a BigInteger to a Rational.
		 * 
		 * @param bigInt the BigInteger number
		 * @return the converted Rational
		 */
		private Rational toRational(final BigInteger bigInt) {
			return Rational.valueOf(bigInt, BigInteger.ONE);
		}
		
		/**
		 * This method converts a BigDecimal to a Rational.
		 * 
		 * @param bigDec the BigDecimal number
		 * @return the converted Rational
		 */
		private Rational toRational(final BigDecimal bigDec) {
			final int scale = bigDec.scale();
			if (scale == 0) {
				return Rational.valueOf(bigDec.toBigIntegerExact(),
						BigInteger.ONE);
			}
			else {
				assert (scale > 0);
				return Rational.valueOf(
						bigDec.scaleByPowerOfTen(scale).toBigIntegerExact(),
						BigInteger.TEN.pow(scale));
			}
		}
		
		/**
		 * This method tells if the rational number is integral.
		 * 
		 * @return true iff the rational is integral
		 */
		public boolean isIntegral() {
			return m_factor.isIntegral();
		}
		
		/**
		 * This method adds a number to the factor.
		 * 
		 * @param summand the additional factor
		 */
		public void add(final Rational summand) {
			m_factor = m_factor.add(summand);
		}
		
		/**
		 * This method negates the value of the factor.
		 */
		public void negate() {
			assert (! m_factor.isNegative());
			m_factor = m_factor.negate();
		}
		
		/**
		 * This method multiplies the factor with another factor.
		 * 
		 * @param factor the additional factor
		 */
		public void mul(Rational factor) {
			m_factor = m_factor.mul(factor);
		}
		
		@Override
		public String toString() {
			return m_factor.toString();
		}
	}
	
	/**
	 * This class abstracts a map from terms to factors.
	 */
	class Var2FactorMap {
		// map: term -> factor
		final HashMap<Term, FactorWrapper> m_map;
		// constant
		Rational m_constant;
		
		public Var2FactorMap() {
			m_map = new HashMap<Term, FactorWrapper>();
			m_constant = Rational.ZERO;
		}
		
		/**
		 * This method updates the constant number (addition).
		 * 
		 * @param summand summand
		 */
		public void updateConstant(final Rational summand) {
			m_constant = m_constant.add(summand);
		}
		
		/**
		 * This method updates the factor in the map associated to the given
		 * term (addition), if it exists, or inserts it otherwise.
		 * 
		 * @param term term
		 * @param summand summand
		 */
		public void update(final Term term, final Rational summand) {
			FactorWrapper wrapper = m_map.get(term);
			if (wrapper == null) {
				wrapper = new FactorWrapper(summand);
				m_map.put(term, wrapper);
			}
			else {
				wrapper.add(summand);
			}
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("{");
			if (m_map.size() > 0) {
				for (Map.Entry<Term, FactorWrapper> tuple :
						m_map.entrySet()) {
					builder.append(tuple);
					builder.append(", ");
				}
			}
			builder.append("constant=");
			builder.append(m_constant.toString());
			builder.append("}");
			return builder.toString();
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
	
	/**
	 * This method is used to have shorter code with the fast proof option.
	 * 
	 * @param rule the rule string
	 */
	private void writeRule(String rule) {
		writeLemmaString(m_startLine);
		writeLemmaString(rule);
		writeLemmaString(m_endLine);
	}
}