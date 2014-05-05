package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.UtilExperimental;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;

/**
 * Represents an term of the form ψ ▷ φ, where ψ and φ are affine terms and
 * ▷ is a binary relation symbol.
 * Allows to return this relation as an SMT term in the following two forms:
 * - positive normal form
 * - the form where a specific variable is on the left hand side and all other
 * summand are moved to the right hand side.
 * 
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
		} catch (NoRelationOfThisKindException e) {
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
	 * Returns the name of the function symbol which is one of the following
	 * {=, <=, >=, <, >, distinct }.
	 * @return
	 */
	public String getFunctionSymbolName() {
		return m_FunctionSymbolName;
	}

	/**
	 * Return if term is variable (possibly with coefficient 0) in this affine 
	 * relation.
	 */
	public boolean isVariable(Term term) {
		return m_AffineTerm.getVariable2Coefficient().containsKey(term);
	}
	
	/**
	 * Returns a term representation of this AffineRelation where each summand 
	 * that has a negative coefficient is moved to the right hand side. 
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
	
	/**
	 * Returns a term representation of this AffineRelation where the variable
	 * var (note that in our AffineTerms the variables may be SMT terms like
	 * e.g., a select term) is on the left hand side with coeffcient one.
	 * Throw a NotAffineException if no such representation is possible
	 * (e.g, if the variable does not occur in the term, or the variable is x, 
	 * its sort is Int and the term is 2x=1.)
	 */
	public ApplicationTerm onLeftHandSideOnly(Script script, Term var) throws NotAffineException {
		assert m_AffineTerm.getVariable2Coefficient().containsKey(var);
		Rational termsCoeff = m_AffineTerm.getVariable2Coefficient().get(var);
		if (termsCoeff.equals(Rational.ZERO)) {
			throw new NotAffineException("No affine representation " +
					"where desired variable is on left hand side");
		}
		List<Term> rhsSummands = new ArrayList<Term>(m_AffineTerm.getVariable2Coefficient().size());
		for (Entry<Term, Rational> entry : m_AffineTerm.getVariable2Coefficient().entrySet()) {
			if (var == entry.getKey()) {
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
										m_FunctionSymbolName, var, rhsTerm);
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
