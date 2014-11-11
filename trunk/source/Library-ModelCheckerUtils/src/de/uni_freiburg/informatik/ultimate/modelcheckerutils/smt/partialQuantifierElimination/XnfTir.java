package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Cnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Dnf;

/**
 * Transitive inequality resolution (TIR) for terms in XNF.
 * @author Matthias Heizmann
 */
public class XnfTir extends XnfPartialQuantifierElimination {

	public XnfTir(Script script, IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "transitive inequality resolution";
	}

	@Override
	public String getAcronym() {
		return "TIR";
	}
	
	public enum BoundType { UPPER, LOWER }

	@Override
	public Term[] tryToEliminate(int quantifier, Term[] inputDisjuncts,
			Set<TermVariable> eliminatees) {
		List<Term> currentDisjuncts = new ArrayList<Term>(Arrays.asList(inputDisjuncts));
		Iterator<TermVariable> it = eliminatees.iterator();
		while (it.hasNext()) {
			List<Term> nextDisjuncts = new ArrayList<Term>();
			TermVariable eliminatee = it.next();
			if (!eliminatee.getSort().isNumericSort()) {
				// this technique is not applicable
				nextDisjuncts = currentDisjuncts;
				continue;
			}
			boolean unableToRemoveEliminatee = false;
			for (Term oldDisjunct : currentDisjuncts) {
				List<Term> elimResultDisjuncts = tryToEliminate_singleDisjuct(quantifier, oldDisjunct, eliminatee);
				if (elimResultDisjuncts == null) {
					// unable to eliminate
					unableToRemoveEliminatee = true;
					nextDisjuncts.add(oldDisjunct);
				} else {
					nextDisjuncts.addAll(elimResultDisjuncts);
				}
			}
			if (unableToRemoveEliminatee) {
				// not eliminated :-(
			} else {
				it.remove();
			}
			currentDisjuncts = nextDisjuncts;
		}
		return currentDisjuncts.toArray(new Term[currentDisjuncts.size()]);
	}

	private List<Term> tryToEliminate_singleDisjuct(int quantifier, Term disjunct,
			TermVariable eliminatee) {
		Term[] conjuncts = PartialQuantifierElimination.getXjunctsInner(quantifier, disjunct);
		List<Term> result = tryToEliminate_Conjuncts(quantifier, conjuncts, eliminatee);
//		Following lines used for debugging - remove them
//		Term term = SmtUtils.or(m_Script, (Collection<Term>) result);
//		term = SmtUtils.simplify(m_Script, term, m_Services);
//		result = Arrays.asList(PartialQuantifierElimination.getXjunctsOuter(quantifier, term));
//		
		return result;
	}
	
	private List<Term> tryToEliminate_Conjuncts(int quantifier, Term[] inputAtoms,
			TermVariable eliminatee) {
		List<Term> termsWithoutEliminatee = new ArrayList<Term>();
		List<Bound> upperBounds = new ArrayList<Bound>();
		List<Bound> lowerBounds = new ArrayList<Bound>();
		List<Term> antiDer = new ArrayList<Term>();

		
		for (Term term : inputAtoms) {
			if (!Arrays.asList(term.getFreeVars()).contains(eliminatee)) {
				termsWithoutEliminatee.add(term);
			} else {
				Term eliminateeOnLhs;
				AffineRelation rel;
				try {
					TransformInequality transform;
					if (quantifier == QuantifiedFormula.EXISTS) {
						transform = TransformInequality.STRICT2NONSTRICT;
					} else if (quantifier == QuantifiedFormula.FORALL) {
						transform = TransformInequality.NONSTRICT2STRICT;
					} else {
						throw new AssertionError("unknown quantifier");
					}
					 rel = new AffineRelation(term, transform);
				} catch (NotAffineException e) {
					// no chance to eliminate the variable
					return null;
				}
				if (!rel.isVariable(eliminatee)) {
					// eliminatee occurs probably only in select
					return null;
				}
				try {
					eliminateeOnLhs = rel.onLeftHandSideOnly(m_Script, eliminatee);
				} catch (NotAffineException e) {
					// no chance to eliminate the variable
					return null;
				}
				try {
					BinaryNumericRelation bnr = new BinaryNumericRelation(eliminateeOnLhs);
					switch (bnr.getRelationSymbol()) {
					case DISTINCT:
						if (quantifier == QuantifiedFormula.EXISTS) {
							 antiDer.add(bnr.getRhs());
						} else {
							throw new AssertionError("should have been removed by DER");
						}
						break;
					case EQ:
						if (quantifier == QuantifiedFormula.FORALL) {
							 antiDer.add(bnr.getRhs());
						} else {
							throw new AssertionError("should have been removed by DER");
						}
						break;
					case GEQ:
						lowerBounds.add(new Bound(false, bnr.getRhs()));
						break;
					case GREATER:
						lowerBounds.add(new Bound(true, bnr.getRhs()));
						break;
					case LEQ:
						upperBounds.add(new Bound(false, bnr.getRhs()));
						break;
					case LESS:
						upperBounds.add(new Bound(true, bnr.getRhs()));
						break;
					default:
						throw new AssertionError();
					}
				} catch (NoRelationOfThisKindException e) {
					throw new AssertionError();
				}
			}
		}
		BuildingInstructions bi = new BuildingInstructions(quantifier,
				eliminatee.getSort(),
				termsWithoutEliminatee, 
				upperBounds, 
				lowerBounds, 
				antiDer);
		List<Term> resultAtoms = new ArrayList<Term>();
		for (Bound lowerBound : lowerBounds) {
			for (Bound upperBound : upperBounds) {
				resultAtoms.add(buildInequality(quantifier, lowerBound, upperBound));
			}
		}
		for (Bound lowerBound : lowerBounds) {
			for (Bound upperBound : upperBounds) {
				resultAtoms.add(buildInequality(quantifier, lowerBound, upperBound));
			}
		}
		resultAtoms.addAll(termsWithoutEliminatee);
		final List<Term> resultDisjunctions;
		if (antiDer.isEmpty()) {
			resultDisjunctions = new ArrayList<Term>();
			Term tmp = PartialQuantifierElimination.composeXjunctsInner(m_Script, quantifier, resultAtoms.toArray(new Term[resultAtoms.size()]));
			assert !Arrays.asList(tmp.getFreeVars()).contains(eliminatee) : "not eliminated";
			resultDisjunctions.add(tmp);
		} else {
			resultAtoms.add(bi.computeAdDisjunction());
			Term tmp = PartialQuantifierElimination.composeXjunctsInner(m_Script, quantifier, resultAtoms.toArray(new Term[resultAtoms.size()]));
			Term disjunction;
			if (quantifier == QuantifiedFormula.EXISTS) {
				disjunction = (new Dnf(m_Script, m_Services)).transform(tmp);
			} else if (quantifier == QuantifiedFormula.FORALL) {
				disjunction = (new Cnf(m_Script, m_Services)).transform(tmp);
			} else {
				throw new AssertionError("unknown quantifier");
			}
			assert !Arrays.asList(disjunction.getFreeVars()).contains(eliminatee) : "not eliminated";
			resultDisjunctions = Arrays.asList(PartialQuantifierElimination.getXjunctsOuter(quantifier, disjunction));
		}
		return resultDisjunctions;
	}
	
	private Term buildInequality(String symbol, Term lhs, Term rhs) {
		Term term = m_Script.term(symbol, lhs, rhs);
		AffineRelation rel;
		try {
			rel = new AffineRelation(term);
		} catch (NotAffineException e) {
			throw new AssertionError("should be affine");
		}
		return rel.positiveNormalForm(m_Script);
	}
	
	private Term buildInequality(int quantifier, Bound lowerBound, Bound upperBound) {
		final boolean isStrict;
		if (quantifier == QuantifiedFormula.EXISTS) {
			isStrict = lowerBound.isIsStrict() || upperBound.isIsStrict();
			assert !(lowerBound.isIsStrict() && upperBound.isIsStrict()) || 
			!lowerBound.getTerm().getSort().getName().equals("Int") : "unsound if int and both are strict";
		} else if (quantifier == QuantifiedFormula.FORALL) {
			isStrict = lowerBound.isIsStrict() && upperBound.isIsStrict();
			assert !(!lowerBound.isIsStrict() && !upperBound.isIsStrict()) || 
			!lowerBound.getTerm().getSort().getName().equals("Int") : "unsound if int and both are non-strict";
		} else {
			throw new AssertionError("unknown quantifier");
		}
		String symbol = (isStrict ? "<" : "<=");
		Term term = m_Script.term(symbol, lowerBound.getTerm(), upperBound.getTerm());
		AffineRelation rel;
		try {
			rel = new AffineRelation(term);
		} catch (NotAffineException e) {
			throw new AssertionError("should be affine");
		}
		return rel.positiveNormalForm(m_Script);
	}


	private class BuildingInstructions {
		private final int m_quantifier;
		private final Sort m_Sort;
		private final List<Term> m_termsWithoutEliminatee;
		private final List<Bound> m_UpperBounds;
		private final List<Bound> m_LowerBounds;
		private final List<Term> m_antiDer;
		public BuildingInstructions(int quantifier, Sort sort,
				List<Term> termsWithoutEliminatee, List<Bound> upperBounds,
				List<Bound> lowerBounds, List<Term> antiDer) {
			super();
			m_quantifier = quantifier;
			m_Sort = sort;
			m_termsWithoutEliminatee = termsWithoutEliminatee;
			m_UpperBounds = upperBounds;
			m_LowerBounds = lowerBounds;
			m_antiDer = antiDer;
		}
		

		Term computeAdDisjunction() {
			ArrayList<Term> resultXJuncts = new ArrayList<Term>();
			for (int i=0; i<Math.pow(2,m_antiDer.size()); i++) {
				ArrayList<Term> resultAtoms = new ArrayList<Term>();
				ArrayList<Bound> adLowerBounds = new ArrayList<Bound>();
				ArrayList<Bound> adUpperBounds = new ArrayList<Bound>();
				for (int k=0; k<m_antiDer.size(); k++) {
					// zero means lower -  one means upper
					if (BigInteger.valueOf(i).testBit(k)) {
						Bound upperBound = computeBound(m_antiDer.get(k), 
								m_quantifier, BoundType.UPPER);
						adUpperBounds.add(upperBound);
					} else {
						Bound lowerBound = computeBound(m_antiDer.get(k), 
								m_quantifier, BoundType.LOWER);
						adLowerBounds.add(lowerBound);

					}
				}
				
				for (Bound adLower : adLowerBounds) {
					for (Bound adUpper : adUpperBounds) {
						resultAtoms.add(buildInequality(m_quantifier, adLower, adUpper));
					}
					for (Bound upperBound : m_UpperBounds) {
						resultAtoms.add(buildInequality(m_quantifier, adLower, upperBound));
					}
				}
				for (Bound adUpper : adUpperBounds) {
					for (Bound lowerBound : m_LowerBounds) {
						resultAtoms.add(buildInequality(m_quantifier, lowerBound, adUpper));
					}
				}
				resultXJuncts.add(PartialQuantifierElimination.composeXjunctsInner(m_Script, m_quantifier, resultAtoms.toArray(new Term[resultAtoms.size()])));
			}
			return PartialQuantifierElimination.composeXjunctsOuter(m_Script, m_quantifier, resultXJuncts.toArray(new Term[resultXJuncts.size()]));
		}

		private Bound computeBound(Term term,
				int quantifier, BoundType boundType) {
			final Bound result;
			if (term.getSort().getName().equals("Real")) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					return new Bound(true, term); 
				} else if (quantifier == QuantifiedFormula.FORALL) {
					return new Bound(false, term);
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else if (term.getSort().getName().equals("Int")) {
				Term one = m_Script.numeral(BigInteger.ONE);
				if (quantifier == QuantifiedFormula.EXISTS) {
					// transform terms such that
					//     lower < x /\ x < upper
					// becomes
					//     lower+1 <= x /\ x <= upper-1
					if (boundType == BoundType.LOWER) {
						result = new Bound(false, m_Script.term("+", term, one));
					} else if (boundType == BoundType.UPPER) {
						result = new Bound(false, m_Script.term("-", term, one));
					} else {
						throw new AssertionError("unknown BoundType" + boundType);
					}
				} else if (quantifier == QuantifiedFormula.FORALL) {
					// transform terms such that
					// lower <= x \/ x <= upper becomes
					// lower-1 < x \/ x < upper+1
					if (boundType == BoundType.LOWER) {
						result = new Bound(true, m_Script.term("-", term, one));
					} else if (boundType == BoundType.UPPER) {
						result = new Bound(true, m_Script.term("+", term, one));
					} else {
						throw new AssertionError("unknown BoundType" + boundType);
					}
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else {
				throw new AssertionError("unknown sort " + term.getSort());
			}
			return result;
		}


		private String computeRelationSymbol(int quantifier, Sort sort) {
			if (quantifier == QuantifiedFormula.FORALL) {
				return "<=";
			} else {
				switch (m_Sort.getName()) {
				case "Int":
					return "<=";
				case "Real":
					return "<";
				default:
					throw new UnsupportedOperationException("unknown Sort");
				}
			}
		}
		


		/**
		 * Add Term summand2 
		 * @param adUpperBounds
		 * @param term
		 * @return
		 */
		private ArrayList<Term> add(ArrayList<Term> terms, Term summand) {
			assert summand.getSort().getName().equals("Int");
			ArrayList<Term> result = new ArrayList<Term>();
			for (Term term : terms) {
				assert term.getSort().getName().equals("Int");
				result.add(m_Script.term("+", term, summand));
			}
			return result;
		}

		
		
	}
	
	
	private static class Bound {
		private final boolean m_IsStrict;
		private final Term m_Term;
		public Bound(boolean isStrict, Term term) {
			super();
			m_IsStrict = isStrict;
			m_Term = term;
		}
		public boolean isIsStrict() {
			return m_IsStrict;
		}
		public Term getTerm() {
			return m_Term;
		}
		@Override
		public String toString() {
			return "Bound [m_IsStrict=" + m_IsStrict + ", m_Term=" + m_Term
					+ "]";
		}
	}
	

	


}
