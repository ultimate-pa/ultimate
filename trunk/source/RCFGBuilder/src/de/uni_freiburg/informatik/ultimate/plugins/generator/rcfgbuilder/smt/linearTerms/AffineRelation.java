package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.util.Util;
import de.uni_freiburg.informatik.ultimate.logic.util.UtilExperimental;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms.BinaryNumericRelation.NotBinaryNumericRelationException;

/**
 * TODO documentation 
 * @author Matthias Heizmann
 */
public class AffineRelation {
	private final Term m_OriginalTerm;
	private final String m_FunctionSymbolName;
	private final AffineTerm m_AffineTerm;

	
	public AffineRelation(Term term) throws NotAffineException {
		m_OriginalTerm = term;
		BinaryNumericRelation bnr = null;
		try {
			bnr = new BinaryNumericRelation(term);
		} catch (NotBinaryNumericRelationException e) {
			throw new NotAffineException("Relation is not affine"); 
		}
		m_FunctionSymbolName = bnr.getRelationSymbol();
		Term lhs = bnr.getLhs();
		Term rhs = bnr.getRhs();
		AffineTerm affineLhs = (AffineTerm) (new AffineTermTransformer()).transform(lhs);
		AffineTerm affineRhs = (AffineTerm) (new AffineTermTransformer()).transform(rhs);
		if (affineLhs.isErrorTerm() || affineRhs.isErrorTerm()) {
			throw new NotAffineException("Relation is not affine"); 
		} else {
			m_AffineTerm = new AffineTerm(affineLhs, new AffineTerm(affineRhs, Rational.MONE));
		}
	}
	
	/**
	 * Return if term is variable (possibly with coefficient 0) in this affine 
	 * relation.
	 */
	public boolean isVariable(Term term) {
		return m_AffineTerm.getVariable2Coefficient().containsKey(term);
	}
	
	/**
	 * Returns a term representation of this AffineTerm where each summand that
	 * has a negative coefficient is moved to the right hand side. 
	 */
	public Term positiveNormalForm(Script script) {
		List<Term> lhsSummands = new ArrayList<Term>();
		List<Term> rhsSummands = new ArrayList<Term>();
		for(Entry<Term, Rational> entry : m_AffineTerm.getVariable2Coefficient().entrySet()) {
			if (entry.getValue().isNegative()) {
				rhsSummands.add(product(script, entry.getValue().abs(), entry.getKey()));
			} else {
				lhsSummands.add(product(script, entry.getValue(), entry.getKey()));
			}
		}
		if (m_AffineTerm.getConstant() != Rational.ZERO) {
			if (m_AffineTerm.getConstant().isNegative()) {
				rhsSummands.add(m_AffineTerm.getConstant().abs().toTerm(m_AffineTerm.getSort()));
			} else {
				lhsSummands.add(m_AffineTerm.getConstant().toTerm(m_AffineTerm.getSort()));
			}
		}
		Term lhsTerm = UtilExperimental.sum(script, m_AffineTerm.getSort(), 
				lhsSummands.toArray(new Term[0]));
		Term rhsTerm = UtilExperimental.sum(script, m_AffineTerm.getSort(), 
				rhsSummands.toArray(new Term[0]));
		Term result = script.term(m_FunctionSymbolName, lhsTerm, rhsTerm);
		assert isEquivalent(script, m_OriginalTerm, result) == LBool.UNSAT : 
			"transformation to positive normal form unsound";
		return result;
	}
	
	public ApplicationTerm onLeftHandSideOnly(Script script, Term term) throws NotAffineException {
		assert m_AffineTerm.getVariable2Coefficient().containsKey(term);
		Rational termsCoeff = m_AffineTerm.getVariable2Coefficient().get(term);
		if (termsCoeff.equals(Rational.ZERO)) {
			throw new NotAffineException("No affine representation " +
					"where desired variable is on left hand side");
		}
		List<Term> rhsSummands = new ArrayList<Term>(m_AffineTerm.getVariable2Coefficient().size());
		for (Entry<Term, Rational> entry : m_AffineTerm.getVariable2Coefficient().entrySet()) {
			if (term == entry.getKey()) {
				// do nothing
			} else {
				Rational newCoeff = entry.getValue().div(termsCoeff);
				if (newCoeff.isIntegral()) {
					Rational negated = newCoeff.negate();
					rhsSummands.add(product(script, negated, entry.getKey()));
				} else {
					throw new NotAffineException("No affine representation " +
							"where desired variable is on left hand side");
				}
			}
		}
		{
			Rational newConstant = m_AffineTerm.getConstant().div(termsCoeff);
			if (newConstant.isIntegral()) {
				Rational negated = newConstant.negate();
				rhsSummands.add(negated.toTerm(m_AffineTerm.getSort()));
			} else {
				throw new NotAffineException("No affine representation " +
						"where desired variable is on left hand side");
			}
		}
		Term rhsTerm = UtilExperimental.sum(script, m_AffineTerm.getSort(), 
				rhsSummands.toArray(new Term[0]));
		ApplicationTerm result = (ApplicationTerm) script.term(
										m_FunctionSymbolName, term, rhsTerm);
		assert isEquivalent(script, m_OriginalTerm, result) == LBool.UNSAT;
		return result;
	}
	
	private static LBool isEquivalent(Script script, Term term1, Term term2) {
		Term comp = script.term("=", term1,term2);
		comp = script.term("not", comp);
		LBool sat = Util.checkSat(script, comp);
		return sat;
	}
	
	private static Term product(Script script, Rational rational, Term term) {
		if (rational.equals(Rational.ONE)) {
			return term;
		} else if (rational.equals(Rational.MONE)) {
			return script.term("-", term);
		} else {
			return script.term("*", rational.toTerm(term.getSort()), term);
		}
	}

}
