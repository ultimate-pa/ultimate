package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryNumericRelation;
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
		return result;
	}
	
	private List<Term> tryToEliminate_Conjuncts(int quantifier, Term[] inputAtoms,
			TermVariable eliminatee) {
		List<Term> termsWithoutEliminatee = new ArrayList<Term>();
		List<Term> nonStrictUpperBounds = new ArrayList<Term>();
		List<Term> strictUpperBounds = new ArrayList<Term>();
		List<Term> nonStrictLowerBounds = new ArrayList<Term>();
		List<Term> strictLowerBounds = new ArrayList<Term>();
		List<Term> antiDer = new ArrayList<Term>();

		
		for (Term term : inputAtoms) {
			if (!Arrays.asList(term.getFreeVars()).contains(eliminatee)) {
				termsWithoutEliminatee.add(term);
			} else {
				Term eliminateeOnLhs;
				AffineRelation rel;
				try {
					 rel = new AffineRelation(term, true);
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
						nonStrictLowerBounds.add(bnr.getRhs());
						break;
					case GREATER:
						strictLowerBounds.add(bnr.getRhs());
						break;
					case LEQ:
						nonStrictUpperBounds.add(bnr.getRhs());
						break;
					case LESS:
						strictUpperBounds.add(bnr.getRhs());
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
				nonStrictUpperBounds, 
				strictUpperBounds, 
				nonStrictLowerBounds, 
				strictLowerBounds, 
				antiDer);
		List<Term> resultAtoms = new ArrayList<Term>();
		for (Term nonStrictlowerBound : nonStrictLowerBounds) {
			for (Term nonStrictUpperBound : nonStrictUpperBounds) {
				resultAtoms.add(buildInequality("<=", nonStrictlowerBound, nonStrictUpperBound));
			}
			for (Term strictUpperBound : strictUpperBounds) {
				resultAtoms.add(buildInequality("<", nonStrictlowerBound, strictUpperBound));
			}
		}
		for (Term strictlowerBound : strictLowerBounds) {
			for (Term nonStrictUpperBound : nonStrictUpperBounds) {
				resultAtoms.add(buildInequality("<", strictlowerBound, nonStrictUpperBound));
			}
			for (Term strictUpperBound : strictUpperBounds) {
				assert !strictlowerBound.getSort().getName().equals("Int") : "unsound for Int";
				resultAtoms.add(buildInequality("<", strictlowerBound, strictUpperBound));
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
			rel = new AffineRelation(term, false);
		} catch (NotAffineException e) {
			throw new AssertionError("should be affine");
		}
		return rel.positiveNormalForm(m_Script);
	}


	private class BuildingInstructions {
		private final int m_quantifier;
		private final Sort m_Sort;
		private final List<Term> m_termsWithoutEliminatee;
		private final List<Term> m_nonStrictUpperBounds;
		private final List<Term> m_strictUpperBounds;
		private final List<Term> m_nonStrictLowerBounds;
		private final List<Term> m_strictLowerBounds;
		private final List<Term> m_antiDer;
		public BuildingInstructions(int quantifier,
				Sort sort,
				List<Term> termsWithoutEliminatee,
				List<Term> nonStrictUpperBounds, List<Term> strictUpperBounds,
				List<Term> nonStrictLowerBounds, List<Term> strictLowerBounds,
				List<Term> antiDer) {
			super();
			m_quantifier = quantifier;
			m_Sort = sort;
			m_termsWithoutEliminatee = termsWithoutEliminatee;
			m_nonStrictUpperBounds = nonStrictUpperBounds;
			m_strictUpperBounds = strictUpperBounds;
			m_nonStrictLowerBounds = nonStrictLowerBounds;
			m_strictLowerBounds = strictLowerBounds;
			m_antiDer = antiDer;
		}
		
		Term computeAdDisjunction() {
			ArrayList<Term> resultXJuncts = new ArrayList<Term>();
			for (int i=0; i<Math.pow(2,m_antiDer.size()); i++) {
				ArrayList<Term> resultAtoms = new ArrayList<Term>();
				ArrayList<Term> adLowerBounds = new ArrayList<Term>();
				ArrayList<Term> adUpperBounds = new ArrayList<Term>();
				for (int k=0; k<m_antiDer.size(); k++) {
					// zero means lower -  one means upper
					if (BigInteger.valueOf(i).testBit(k)) {
						adUpperBounds.add(m_antiDer.get(k));
					} else {
						adLowerBounds.add(m_antiDer.get(k));
					}
				}
				if (m_quantifier == QuantifiedFormula.EXISTS) {
					switch (m_Sort.getName()) {
					case "Int":
						adUpperBounds = add(adUpperBounds, m_Script.numeral("-1"));
						adLowerBounds = add(adLowerBounds, m_Script.numeral("1"));
						break;
					case "Real":
						// do nothing
						break;
					default:
						break;
					}
				}
				String relSymb = computeRelationSymbol(m_quantifier, m_Sort);
				for (Term adLower : adLowerBounds) {
					for (Term adUpper : adUpperBounds) {
						resultAtoms.add(buildInequality(
								relSymb, adLower, adUpper));
					}
					
				}
				
				for (Term adLower : adLowerBounds) {
					for (Term nonStrictUpperBound : m_nonStrictUpperBounds) {
						resultAtoms.add(buildInequality(relSymb, adLower, nonStrictUpperBound));
					}
					for (Term strictUpperBound : m_strictUpperBounds) {
						resultAtoms.add(buildInequality(relSymb, adLower, strictUpperBound));
					}
				}
				for (Term adUpper : adUpperBounds) {
					for (Term nonStrictLowerBound : m_nonStrictLowerBounds) {
						resultAtoms.add(buildInequality(relSymb, nonStrictLowerBound, adUpper));
					}
					for (Term strictLowerBound : m_strictLowerBounds) {
						resultAtoms.add(buildInequality(relSymb, strictLowerBound, adUpper));
					}
				}
				resultXJuncts.add(PartialQuantifierElimination.composeXjunctsInner(m_Script, m_quantifier, resultAtoms.toArray(new Term[resultAtoms.size()])));
			}
			return PartialQuantifierElimination.composeXjunctsOuter(m_Script, m_quantifier, resultXJuncts.toArray(new Term[resultXJuncts.size()]));
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
	

	


}
