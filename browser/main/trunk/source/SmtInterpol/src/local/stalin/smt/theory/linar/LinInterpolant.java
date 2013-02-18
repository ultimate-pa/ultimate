/**
 * 
 */
package local.stalin.smt.theory.linar;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.PredicateSymbol;
import local.stalin.logic.Sort;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.logic.VariableTerm;

public class LinInterpolant {
	AffinTerm affinTerm;
	Formula equalFormula;
	Set<BoundConstraint> mixedAtoms;
	
	public LinInterpolant(MutableAffinTerm maffin, Set<BoundConstraint> mixed) {
		this.affinTerm = new AffinTerm(maffin);
		equalFormula = maffin.constant.mb.compareTo(Rational.ZERO) > 0 ? Atom.FALSE : Atom.TRUE; 
		mixedAtoms = mixed;
	}

	public LinInterpolant(AffinTerm affin, Formula formula, Set<BoundConstraint> mixed) {
		this.affinTerm = affin;
		equalFormula = formula;
		mixedAtoms = mixed;
	}
	
	private static int laictr = 0;
	
	LinInterpolant merge(Theory theory, LinInterpolant other, BoundConstraint pivotConstraint) {
		System.out.println("MERGE "+this+" and "+ other);
		HashSet<BoundConstraint> newMixed = new HashSet<BoundConstraint>(mixedAtoms.size()+other.mixedAtoms.size()-2);
		assert mixedAtoms.contains(pivotConstraint) && other.mixedAtoms.contains(pivotConstraint); 
		newMixed.addAll(mixedAtoms);
		newMixed.addAll(other.mixedAtoms);
		newMixed.remove(pivotConstraint);
		LinVar pivot = pivotConstraint.mvar.mixedVar;
		Formula form = theory.and(equalFormula, other.equalFormula);
		if (affinTerm.isConstant()) {
			/* This is a Nelson-Oppen clause or a simple propagate
			 * clause.
			 */
			return new LinInterpolant(other.affinTerm, form, newMixed);
		} else if (other.affinTerm.isConstant()) {
			return new LinInterpolant(affinTerm, form, newMixed);
		}
		
		Rational factor = other.affinTerm.factors.get(pivot);
		MutableAffinTerm sharedTerm = new MutableAffinTerm(other.affinTerm.isIntegral());
		sharedTerm.add(factor.inverse().negate(), other.affinTerm);
		sharedTerm.add(Rational.ONE, pivot);
		TermVariable tv = ((VariableTerm) pivot.mname).getVariable();
		System.out.println("LET "+tv+" = "+ sharedTerm+ 
				(sharedTerm.isIntegral() ? " (integer)" : " (real)"));
		if (sharedTerm.isIntegral()) {
			Rational norm = sharedTerm.isConstant() ? Rational.ONE : sharedTerm.getGCD();
			norm = norm.gcd(sharedTerm.constant.ma);
			norm = norm.gcd(Rational.ONE);
			if (!norm.equals(Rational.ONE)) {
				Sort intSort = theory.getSort("Int");
				sharedTerm.div(norm);
				FunctionSymbol times = theory.getFunction("*", intSort, intSort);
				TermVariable newtv = theory.createTermVariable("laipl"+laictr++, intSort);
				Term lhs = theory.term(times,
						theory.numeral(norm.denominator()),
						theory.term(newtv));
				Term rhs = sharedTerm.toSMTLib(theory);
				form = theory.and(theory.equals(lhs, rhs), form); 
				form = theory.let(tv, theory.term(newtv), form);
				form = theory.exists(new TermVariable[] {newtv}, form);
			} else {
				form = theory.let(tv, sharedTerm.toSMTLib(theory), form);
			}
		} else {
			form = theory.let(tv, sharedTerm.toSMTLib(theory), form);
		}

		MutableAffinTerm newsum = new MutableAffinTerm(affinTerm.isIntegral());
		Rational fact1 = other.affinTerm.factors.get(pivot).abs();
		Rational fact2 = affinTerm.factors.get(pivot).abs();
		newsum.add(fact1, affinTerm);
		newsum.add(fact2, other.affinTerm);
		assert !newsum.summands.containsKey(pivot);

		return new LinInterpolant(new AffinTerm(newsum), form, newMixed);
	}
	
	Formula createFormula(Theory theory) {
		if (affinTerm.isConstant()) {
			int signum = affinTerm.getConstant().signum();
			return signum == -1 ? Atom.TRUE : 
				signum == 0 ? equalFormula : Atom.FALSE;
		}
		
		boolean isInt = affinTerm.isIntegral();
		MutableAffinTerm lhs = new MutableAffinTerm(isInt);
		MutableAffinTerm rhs = new MutableAffinTerm(isInt);
		Rational constant = affinTerm.constant;
		Rational norm = constant.abs();
		if (constant.isNegative())
			rhs.add(constant.negate());
		else
			lhs.add(constant);
		
		for (Map.Entry<LinVar, Rational> entry : affinTerm.factors.entrySet()) {
			Rational value = entry.getValue();
			norm = norm.gcd(value.abs());
			if (value.isNegative()) {
				rhs.add(value.negate(), entry.getKey());
			} else {
				lhs.add(value, entry.getKey());
			}
		}
		lhs.div(norm);
		rhs.div(norm);
		Term lhsTerm = lhs.toSMTLib(theory);
		Term rhsTerm = rhs.toSMTLib(theory);
		Sort smtSort = lhsTerm.getSort();
		Sort[] binfunc = new Sort[] {smtSort, smtSort};
		PredicateSymbol leq = theory.getPredicate("<=",binfunc);
		PredicateSymbol less = theory.getPredicate("<",binfunc);
		Atom lessPart = theory.atom(less, lhsTerm, rhsTerm);
		if (equalFormula == Atom.FALSE)
			return lessPart;
		Atom leqPart = theory.atom(leq, lhsTerm, rhsTerm); 
		return theory.and(leqPart, theory.or(lessPart, equalFormula));
	}
	
	public String toString() {
		return "["+affinTerm+" <= 0 eq: "+equalFormula+"]";
	}
}