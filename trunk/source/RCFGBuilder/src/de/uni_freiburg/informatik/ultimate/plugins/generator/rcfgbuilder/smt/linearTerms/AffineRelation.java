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

/**
 * TODO documentation 
 * @author Matthias Heizmann
 */
public class AffineRelation {
	private final Term m_OriginalTerm;
	private final String m_FunctionSymbolName;
	private final AffineTerm m_AffineTerm;
	private final static String NOT_EQUALS = "!=";
	
	
	public AffineRelation(ApplicationTerm term) {
		m_OriginalTerm = term;
		String functionSymbolName = term.getFunction().getName();
		Term[] params = term.getParameters();
		AffineTerm affineLhs;
		AffineTerm affineRhs;
		if (functionSymbolName.equals("not")) {
			assert params.length == 1;
			if (params[0] instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) params[0];
				functionSymbolName = appTerm.getFunction().getName();
				if (functionSymbolName.equals("=")) {
					params = appTerm.getParameters();
					m_FunctionSymbolName = NOT_EQUALS;
				} else {
					throw new UnsupportedOperationException("if not then =");	
				}
			} else {
				throw new UnsupportedOperationException("if not then =");
			}
		} else {
			if (functionSymbolName.equals("=") ||
					functionSymbolName.equals("distinct") ||
					functionSymbolName.equals("<") ||
					functionSymbolName.equals(">") ||
					functionSymbolName.equals("<=") ||
					functionSymbolName.equals(">=")) {
				m_FunctionSymbolName = functionSymbolName;
			} else {
				throw new UnsupportedOperationException("unsupported function symbol");
			}
		}
		if (params.length != 2) {
			throw new UnsupportedOperationException("exactly two parameters expected");
		}
		affineLhs = (AffineTerm) (new AffineTermTransformer()).transform(params[0]);
		affineRhs = (AffineTerm) (new AffineTermTransformer()).transform(params[1]);
		if (affineLhs.isErrorTerm() || affineRhs.isErrorTerm()) {
			m_AffineTerm = null;
		} else {
			m_AffineTerm = new AffineTerm(affineLhs, new AffineTerm(affineRhs, Rational.MONE));
		}
	}
	
	public boolean translationFailed() {
		return m_AffineTerm == null;
	}
	
	public Term negationNormalForm(Script script) {
		List<Term> lhsSummands = new ArrayList<Term>();
		List<Term> rhsSummands = new ArrayList<Term>();
		for(Entry<Term, Rational> entry : m_AffineTerm.getVariable2Coefficient().entrySet()) {
			if (entry.getValue().isNegative()) {
				Term coeff = entry.getValue().abs().toTerm(m_AffineTerm.getSort());
				rhsSummands.add(script.term("*", coeff, entry.getKey()));
			} else {
				Term coeff = entry.getValue().toTerm(m_AffineTerm.getSort());
				lhsSummands.add(script.term("*", coeff, entry.getKey()));
			}
			if (m_AffineTerm.getConstant().isNegative()) {
				rhsSummands.add(m_AffineTerm.getConstant().toTerm(m_AffineTerm.getSort()));
			} else {
				lhsSummands.add(m_AffineTerm.getConstant().toTerm(m_AffineTerm.getSort()));
			}
		}
		Term lhsTerm = Util.sum(script, lhsSummands.toArray(new Term[0]));
		Term rhsTerm = Util.sum(script, rhsSummands.toArray(new Term[0]));
		Term result = constuctTerm(script, m_FunctionSymbolName, lhsTerm, rhsTerm);
		assert isEquivalent(script, m_OriginalTerm, result) == LBool.UNSAT;
		return result;
	}
	
	public Term onLeftHandSideOnly(Script script, Term term) {
		assert m_AffineTerm.getVariable2Coefficient().containsKey(term);
		Rational termsCoeff = m_AffineTerm.getVariable2Coefficient().get(term);
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
					throw new UnsupportedOperationException();
				}
			}
		}
		{
			Rational newConstant = m_AffineTerm.getConstant().div(termsCoeff);
			if (newConstant.isIntegral()) {
				Rational negated = newConstant.negate();
				rhsSummands.add(negated.toTerm(m_AffineTerm.getSort()));
			} else {
				throw new UnsupportedOperationException();
			}
		}
		Term rhsTerm = Util.sum(script, rhsSummands.toArray(new Term[0]));
		Term result = constuctTerm(script, m_FunctionSymbolName, term, rhsTerm);
		assert isEquivalent(script, m_OriginalTerm, result) == LBool.UNSAT;
		return result;
	}
	
	private Term constuctTerm(Script script, String functionSymbolName, Term lhs, Term rhs) {
		Term result;
		if (functionSymbolName.equals(NOT_EQUALS)) {
			result = script.term("=", lhs, rhs);
			result = script.term("not", result);
		} else {
			result = script.term(functionSymbolName, lhs, rhs);
		}
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
			return rational.toTerm(term.getSort());
		}
	}

}
