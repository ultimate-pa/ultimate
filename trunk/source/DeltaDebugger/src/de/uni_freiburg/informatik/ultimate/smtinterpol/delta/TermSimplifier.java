package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class TermSimplifier extends TermTransformer {
	public enum Mode {
		NEUTRALS,
		BINDINGS
	}
	private Mode m_Mode;
	
	public TermSimplifier(Mode mode) {
		m_Mode = mode;
	}
	
	private boolean isZero(Term t) {
		if (t instanceof ConstantTerm) {
			ConstantTerm ct = (ConstantTerm) t;
			Object val = ct.getValue();
			if (val instanceof BigInteger)
				return BigInteger.ZERO.equals(val);
			if (val instanceof BigDecimal)
				return BigDecimal.ZERO.equals(val);
			if (val instanceof Rational)
				return Rational.ZERO.equals(val);
		}
		return false;
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		if (m_Mode != Mode.NEUTRALS) {
			super.convertApplicationTerm(appTerm, newArgs);
			return;
		}
		Theory t = appTerm.getTheory();
		FunctionSymbol fs = appTerm.getFunction();
		if (appTerm.getSort() == t.getBooleanSort()) {
			if (appTerm.getFunction() == t.m_And || 
					appTerm.getFunction() == t.m_Or) {
				Term neutral = fs == t.m_And ? t.TRUE : t.FALSE;
				LinkedHashSet<Term> newParams = new LinkedHashSet<Term>();
				for (Term p : newArgs) {
					if (p != neutral)
						newParams.add(p);
				}
				if (newParams.size() != newArgs.length) {
					// Otherwise replace by true/false should succeed...
					assert newParams.size() > 0;
					if (newParams.size() == 1)
						setResult(newParams.iterator().next());
					else
						setResult(t.term(fs,
							newParams.toArray(new Term[newParams.size()])));
					return;
				}
			}
			setResult(t.term(appTerm.getFunction(), newArgs));
		} else if (appTerm.getSort().isNumericSort()) {
			int start = 0;
			if (fs.getName().equals("-"))
				start = 1;
			else if (!fs.getName().equals("+")) {
				super.convertApplicationTerm(appTerm, newArgs);
				return;
			}
			ArrayList<Term> simp = new ArrayList<Term>();
			for (int i = 0; i < start; ++i)
				simp.add(newArgs[i]);
			for (; start < newArgs.length; ++start)	{
				if (!isZero(newArgs[start]))
					simp.add(newArgs[start]);
			}
			if (newArgs.length != simp.size())
				newArgs = simp.toArray(new Term[simp.size()]);
			setResult(appTerm.getTheory().term(fs, newArgs));
		} else
			super.convertApplicationTerm(appTerm, newArgs);
	}

	@Override
	public void postConvertLet(LetTerm oldLet, Term[] newValues, Term newBody) {
		if (m_Mode != Mode.BINDINGS) {
			super.postConvertLet(oldLet, newValues, newBody);
			return;
		}
		Set<TermVariable> freeVars = new HashSet<TermVariable>(
				Arrays.asList(newBody.getFreeVars()));
		ArrayList<TermVariable> tvs = new ArrayList<TermVariable>();
		ArrayList<Term> vals = new ArrayList<Term>();
		for (int i = 0; i < newValues.length; ++i) {
			TermVariable var = oldLet.getVariables()[i];
			if (freeVars.contains(var)) {
				tvs.add(var);
				vals.add(newValues[i]);
			}
		}
		if (tvs.size() == 0)
			setResult(newBody);
		else if (tvs.size() == newValues.length &&
				newBody == oldLet.getSubTerm())
			setResult(oldLet);
		else
			setResult(newBody.getTheory().let(
					tvs.toArray(new TermVariable[tvs.size()]), 
					vals.toArray(new Term[vals.size()]), newBody));
	}

	@Override
	public void postConvertQuantifier(QuantifiedFormula old, Term newBody) {
		if (m_Mode != Mode.BINDINGS) {
			super.postConvertQuantifier(old, newBody);
			return;
		}
		Set<TermVariable> freeVars = new HashSet<TermVariable>(
				Arrays.asList(newBody.getFreeVars()));
		ArrayList<TermVariable> tvs = new ArrayList<TermVariable>();
		for (TermVariable tv : old.getVariables())
			if (freeVars.contains(tv))
				tvs.add(tv);
		if (tvs.size() == 0)
			setResult(newBody);
		else if (tvs.size() == old.getVariables().length &&
				newBody == old.getSubformula())
			setResult(old);
		else {
			Theory t = old.getTheory();
			setResult(old.getQuantifier() == QuantifiedFormula.EXISTS ?
					t.exists(tvs.toArray(
							new TermVariable[tvs.size()]), newBody) :
					t.forall(tvs.toArray(
							new TermVariable[tvs.size()]), newBody));
		}
	}
}
