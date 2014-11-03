package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

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
	public Term[] tryToEliminate(int quantifier, Term[] inputAtoms,
			Set<TermVariable> eliminatees) {
		Iterator<TermVariable> it = eliminatees.iterator();
		Term[] resultAtoms = inputAtoms;
		while (it.hasNext()) {
			TermVariable tv = it.next();
			if (!SmtUtils.getFreeVars(Arrays.asList(resultAtoms)).contains(tv)) {
				// case where var does not occur
				it.remove();
				continue;
			} else {
				Term[] withoutTv = tryToEliminate(quantifier, resultAtoms, tv);
				if (withoutTv != null) {
					resultAtoms = withoutTv;
					it.remove();
				}
			}
		}
		return resultAtoms;
	}


	private Term[] tryToEliminate(int quantifier, Term[] inputAtoms,
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
		if (!antiDer.isEmpty()) {
			throw new AssertionError("not yet implemented");
		}
		return resultAtoms.toArray(new Term[resultAtoms.size()]);
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

	public static Term[] derSimple(Script script, int quantifier, Term[] inputAtoms, TermVariable tv, Logger logger) {
		final Term[] resultAtoms;
		EqualityInformation eqInfo = EqualityInformation.getEqinfo(script, tv, inputAtoms, null, quantifier, logger);
		if (eqInfo == null) {
			logger.debug(new DebugMessage("not eliminated quantifier via DER for {0}", tv));
			resultAtoms = null;
		} else {
			logger.debug(new DebugMessage("eliminated quantifier via DER for {0}", tv));
			resultAtoms = new Term[inputAtoms.length - 1];
			Map<Term, Term> substitutionMapping = Collections.singletonMap(eqInfo.getVariable(), eqInfo.getTerm());
			SafeSubstitution substitution = new SafeSubstitution(script, substitutionMapping);
			for (int i = 0; i < eqInfo.getIndex(); i++) {
				resultAtoms[i] = substitution.transform(inputAtoms[i]);
			}
			for (int i = eqInfo.getIndex() + 1; i < inputAtoms.length; i++) {
				resultAtoms[i - 1] = substitution.transform(inputAtoms[i]);
			}
		}
		return resultAtoms;
	}
	
	

	


}
