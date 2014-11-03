package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.RelationSymbol;

/**
 * Represents an term of the form ψ ▷ φ, where ψ and φ are affine terms and ▷ is
 * a binary relation symbol. Allows to return this relation as an SMT term in
 * the following two forms: - positive normal form - the form where a specific
 * variable is on the left hand side and all other summand are moved to the
 * right hand side.
 * 
 * @author Matthias Heizmann
 */
public class AffineRelation {
	private final Term m_OriginalTerm;
	private RelationSymbol m_RelationSymbol;
	/**
	 * Affine term ψ such that the relation ψ ▷ 0 is equivalent to the
	 * m_OriginalTerm.
	 * 
	 */
	private AffineTerm m_AffineTerm;

	/**
	 * Transform Term into AffineRelation.
	 * @param term Term to which the resulting AffineRelation is equivalent.
	 * @param makeNonStrict if true and sort is Int, the resulting 
	 * AffineRelation does not have strict inequalities.
	 * @throws NotAffineException Thrown if Term is not affine.
	 */
	public AffineRelation(Term term, boolean makeNonStrict) throws NotAffineException {
		m_OriginalTerm = term;
		BinaryNumericRelation bnr = null;
		try {
			bnr = new BinaryNumericRelation(term);
		} catch (NoRelationOfThisKindException e) {
			throw new NotAffineException("Relation is not affine");
		}
		
		Term lhs = bnr.getLhs();
		Term rhs = bnr.getRhs();
		AffineTerm affineLhs = (AffineTerm) (new AffineTermTransformer()).transform(lhs);
		AffineTerm affineRhs = (AffineTerm) (new AffineTermTransformer()).transform(rhs);
		AffineTerm difference;
		if (affineLhs.isErrorTerm() || affineRhs.isErrorTerm()) {
			throw new NotAffineException("Relation is not affine");
		} else {
			difference = new AffineTerm(affineLhs, new AffineTerm(affineRhs, Rational.MONE));
		}
		if (makeNonStrict && difference.getSort().getName().equals("Int")) {
			switch (bnr.getRelationSymbol()) {
			case DISTINCT:
			case EQ:
			case GEQ:
			case LEQ:
				// relation symbol is not strict anyway
				m_AffineTerm = difference; 
				m_RelationSymbol = bnr.getRelationSymbol();
				break;
			case LESS:
				// decrement affine term by one
				m_RelationSymbol = RelationSymbol.LEQ;
				m_AffineTerm = new AffineTerm(m_AffineTerm, 
						new AffineTerm(m_AffineTerm.getSort(), Rational.ONE));
				break;
			case GREATER:
				// increment affine term by one
				m_RelationSymbol = RelationSymbol.GEQ;
				m_AffineTerm = new AffineTerm(difference, 
						new AffineTerm(difference.getSort(), Rational.MONE));
				break;
			default:
				throw new AssertionError("unknown symbol");
			}
		} else {
			m_AffineTerm = difference; 
			m_RelationSymbol = bnr.getRelationSymbol();

		}
	}
	
	
	public void makeNonStrict() {
		if (!m_AffineTerm.getSort().getName().equals("Int")) {
			throw new UnsupportedOperationException("can only make Int terms non strict");
		}
		switch (m_RelationSymbol) {
		case DISTINCT:
		case EQ:
		case GEQ:
		case LEQ:
			throw new UnsupportedOperationException("can only make strict symbols non-strict");
		case LESS:
			// dencrement affine term by one
			m_RelationSymbol = RelationSymbol.LEQ;
			m_AffineTerm = new AffineTerm(m_AffineTerm, 
					new AffineTerm(m_AffineTerm.getSort(), Rational.MONE));
			break;
		case GREATER:
			// increment affine term by one
			m_RelationSymbol = RelationSymbol.GEQ;
			m_AffineTerm = new AffineTerm(m_AffineTerm, 
					new AffineTerm(m_AffineTerm.getSort(), Rational.ONE));
			break;
		default:
			throw new AssertionError("unknown symbol");
		}
	}

	/**
	 * Returns the name of the function symbol which is one of the following {=,
	 * <=, >=, <, >, distinct }.
	 * 
	 * @return
	 */
	public String getFunctionSymbolName() {
		return m_RelationSymbol.toString();
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
		for (Entry<Term, Rational> entry : m_AffineTerm.getVariable2Coefficient().entrySet()) {
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
		Term lhsTerm = SmtUtils.sum(script, m_AffineTerm.getSort(), lhsSummands.toArray(new Term[lhsSummands.size()]));
		Term rhsTerm = SmtUtils.sum(script, m_AffineTerm.getSort(), rhsSummands.toArray(new Term[rhsSummands.size()]));
		Term result = script.term(m_RelationSymbol.toString(), lhsTerm, rhsTerm);
		assert isEquivalent(script, m_OriginalTerm, result) == LBool.UNSAT : "transformation to positive normal form unsound";
		return result;
	}

	/**
	 * Returns a term representation of this AffineRelation where the variable
	 * var (note that in our AffineTerms the variables may be SMT terms like
	 * e.g., a select term) is on the left hand side with coeffcient one. Throw
	 * a NotAffineException if no such representation is possible (e.g, if the
	 * variable does not occur in the term, or the variable is x, its sort is
	 * Int and the term is 2x=1.)
	 */
	public ApplicationTerm onLeftHandSideOnly(Script script, Term var) throws NotAffineException {
		assert m_AffineTerm.getVariable2Coefficient().containsKey(var);
		final Rational termsCoeff = m_AffineTerm.getVariable2Coefficient().get(var);
		if (termsCoeff.equals(Rational.ZERO)) {
			throw new NotAffineException("No affine representation " + "where desired variable is on left hand side");
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
					throw new NotAffineException("No affine representation "
							+ "where desired variable is on left hand side");
				}
			}
		}
		{
			Rational newConstant = m_AffineTerm.getConstant().div(termsCoeff);
			if (newConstant.isIntegral()) {
				Rational negated = newConstant.negate();
				rhsSummands.add(negated.toTerm(m_AffineTerm.getSort()));
			} else {
				throw new NotAffineException("No affine representation "
						+ "where desired variable is on left hand side");
			}
		}
		Term rhsTerm = SmtUtils.sum(script, m_AffineTerm.getSort(), rhsSummands.toArray(new Term[rhsSummands.size()]));

		// if coefficient is negative we have to use the "swapped"
		// RelationSymbol
		boolean useRelationSymbolForSwappedTerms = termsCoeff.isNegative();
		RelationSymbol relSymb = useRelationSymbolForSwappedTerms ? BinaryRelation.swapParameters(m_RelationSymbol)
				: m_RelationSymbol;
		ApplicationTerm result = (ApplicationTerm) script.term(relSymb.toString(), var, rhsTerm);
		assert isEquivalent(script, m_OriginalTerm, result) == LBool.UNSAT : "transformation to AffineRelation unsound";
		return result;
	}

	private static LBool isEquivalent(Script script, Term term1, Term term2) {
		Term comp = script.term("=", term1, term2);
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
