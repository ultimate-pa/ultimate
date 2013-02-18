package local.stalin.plugins.generator.traceabstraction;

import java.util.Map;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Formula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.NumeralTerm;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.ProgramVariableTerm;
import local.stalin.logic.RationalTerm;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.logic.VariableTerm;
import local.stalin.logic.FormulaWalker.SymbolVisitor;


/**
 * Replaces constant symbols by constant symbols according to the Map
 * substitution. 
 * @author heizmann@informatik.uni-freiburg.de
 */

public class ConstantSubstitutionVisitor implements SymbolVisitor {

	Theory m_Theory;
	Map<ApplicationTerm, ApplicationTerm> m_Substitution;


	
	
	public ConstantSubstitutionVisitor(
						Theory theory,
						Map<ApplicationTerm, ApplicationTerm> substitution)
	{
		m_Theory = theory;
		m_Substitution = substitution;
	}

	@Override
	public void done(Term input) {}

	@Override
	public void done(PredicateAtom pa) {}

	@Override
	public void endscope(TermVariable tv) {}

	@Override
	public void endscopes(TermVariable[] tvs) {}

	@Override
	public void let(TermVariable tv, Term mval) {}

	@Override
	public Formula predicate(PredicateAtom pa) {
		return null;
	}

	public void quantifier(TermVariable[] tvs) {}

	@Override
	public Term term (Term input) {
		if (input instanceof ApplicationTerm) {
			ApplicationTerm constant = (ApplicationTerm) input;
			if (m_Substitution.containsKey(input)) {
				return m_Substitution.get(constant);
			}
			else {
				return null;
			}
		}
		else if (input instanceof ITETerm) {
			return null;
		}
		else if (input instanceof NumeralTerm) {
			return input;
		}
		else if (input instanceof ProgramVariableTerm) {
			return input;
		}
		else if (input instanceof RationalTerm) {
			return input;
		}
		else if (input instanceof VariableTerm) {
			return input;
		}
		else {
			throw new IllegalArgumentException("unknown type of Term");
		}
	}

	@Override
	public boolean unflet() {
		return false;
	}

	@Override
	public boolean unlet() {
		return false;
	}
	
}
