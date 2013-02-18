/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;


/**
 *  Represents a modifiable affin term, i.e. SUM_i c_i * x_i + c, 
 *  where the x_i are initially nonbasic variable.
 *    
 *  @author hoenicke.
 */
public class InterpolatorAffineTerm {
	Map<Term, Rational> m_summands = new HashMap<Term, Rational>();
	InfinitNumber m_constant;
	
	public InterpolatorAffineTerm() {
		m_constant = InfinitNumber.ZERO;
	}

	public InterpolatorAffineTerm(InterpolatorAffineTerm iat) {
		m_constant = iat.getConstant();
		m_summands.putAll(iat.getSummands());
	}

	public InterpolatorAffineTerm(Map<LinVar, Rational> sum, InfinitNumber c) {
		m_constant = c;
		for (Entry<LinVar, Rational> entry : sum.entrySet())
			m_summands.put(entry.getKey().getSharedTerm().getTerm(), entry.getValue());
	}

	public InterpolatorAffineTerm(MutableAffinTerm mat) {
		this(mat.getSummands(), mat.getConstant());
	}

	public InterpolatorAffineTerm add(Rational c) {
		m_constant = m_constant.add(new InfinitNumber(c, 0));
		return this;
	}
	
	public InterpolatorAffineTerm add(InfinitNumber c) {
		m_constant = m_constant.add(c);
		return this;
	}

	public InterpolatorAffineTerm add(Rational c, MutableAffinTerm a) {
		if (c != Rational.ZERO) {
			addLinVarMap(c, a.getSummands());
			m_constant = m_constant.add(a.getConstant().mul(c));
		}
		return this;
	}

	public InterpolatorAffineTerm add(Rational c, Term term) {
		if (!c.equals(Rational.ZERO))
		addSimple(c, term);
		return this;
	}
	public InterpolatorAffineTerm add(Rational c, SharedTerm term) {
		if (c.equals(Rational.ZERO))
			return this;
		if (term.getTerm() instanceof SMTAffineTerm)
			add(c, term.getClausifier().createMutableAffinTerm(term));
		else
			addSimple(c, term.getLinVar());
		return this;
	}
	public InterpolatorAffineTerm add(Rational c, LinVar var) {
		if (c.equals(Rational.ZERO))
			return this;
		if (var.isInitiallyBasic()) {
			for (Map.Entry<LinVar, BigInteger> me : var.getLinTerm().entrySet())
				add(c.mul(me.getValue()), me.getKey());
		} else {
			addSimple(c, var);
		}
		return this;
	}

	private void addLinVarMap(Rational c, Map<LinVar, Rational> linterm) {
		for (Map.Entry<LinVar, Rational> summand : linterm.entrySet())
			addSimple(c.mul(summand.getValue()), summand.getKey());
	}

	private void addMap(Rational c, Map<Term, Rational> linterm) {
		for (Map.Entry<Term, Rational> summand : linterm.entrySet())
			addSimple(c.mul(summand.getValue()), summand.getKey());
	}
	
	private void addSimple(Rational c, LinVar term) {
		addSimple(c, term.getSharedTerm().getRealTerm());
	}
	
	private void addSimple(Rational c, Term term) {
		assert (/*!term.getLinVar().isInitiallyBasic() &&*/ !c.equals(Rational.ZERO));
		Rational oldc = m_summands.remove(term);
		if (oldc != null) {
			c = oldc.add(c);
			if (c.equals(Rational.ZERO))
				return;
		}
		m_summands.put(term,c);
	}

	public InterpolatorAffineTerm add(Rational c, InterpolatorAffineTerm a) {
		if (c != Rational.ZERO) {
			addMap(c, a.m_summands);
			m_constant = m_constant.add(a.m_constant.mul(c));
		}
		return this;
	}

	public InterpolatorAffineTerm mul(Rational c) {
		if (c.equals(Rational.ZERO))
			m_summands.clear();
		else if (!c.equals(Rational.ONE)) {
			for (Map.Entry<Term, Rational> summand : m_summands.entrySet()) {
				summand.setValue(c.mul(summand.getValue()));
			}
			m_constant = m_constant.mul(c);
		}
		return this;
	}
	
	public InterpolatorAffineTerm div(Rational c) {
		return mul(c.inverse());
	}
	public InterpolatorAffineTerm negate() {
		return mul(Rational.MONE);
	}
	public boolean isConstant() {
		return m_summands.isEmpty();
	}
	public InfinitNumber getConstant() {
		return m_constant;
	}
	public Map<Term,Rational> getSummands() {
		return m_summands;
	}
	
	public Rational getGCD() {
		assert (!m_summands.isEmpty());
		Iterator<Rational> it = m_summands.values().iterator();
		Rational gcd = it.next(); 
		boolean firstSign = gcd.isNegative();
		gcd = gcd.abs();
		while (it.hasNext()) {
			gcd = gcd.gcd(it.next().abs());
		}
		if (firstSign)
			gcd = gcd.negate();
		return gcd;
	}
	
	/**
	 * For integer valued interpolants, convert Rationals to integer valued
	 * Rational by dividing by the rational greatest common divisor.
	 */
	void normalize() {
		mul(getGCD().inverse());
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		boolean isFirst = true;
		for (Entry<Term,Rational> entry : m_summands.entrySet()) {
			Term var = entry.getKey();
			Rational fact = entry.getValue();
			if (fact.isNegative()) {
				sb.append(isFirst ? "-" : " - ");
			} else {
				sb.append(isFirst ? "" : " + ");
			}
			fact = fact.abs();
			if (!fact.equals(Rational.ONE))
				sb.append(fact).append("*");
			sb.append(var);
			isFirst = false;
		}
		if (isFirst)
			sb.append(m_constant);
		else {
			int signum = m_constant.compareTo(InfinitNumber.ZERO); 
			if (signum < 0) {
				sb.append(" - ");
				sb.append(m_constant.mul(Rational.MONE));
			} else if (signum > 0){
				sb.append(" + ");
				sb.append(m_constant);
			}
		}
		return sb.toString();
	}
	
	/**
	 * Convert the affine term to a term in our core theory.
	 */ 
	public Term toSMTLib(Theory t, boolean isInt) {
		assert(m_constant.meps == 0);
		Sort numSort = isInt ? t.getSort("Int") : t.getSort("Real");
		assert(numSort != null);
		Sort[] binfunc = new Sort[] {numSort,numSort};
		FunctionSymbol times = t.getFunction("*",binfunc);
		FunctionSymbol plus = t.getFunction("+",binfunc);
		FunctionSymbol negate = t.getFunction("-", numSort);
		if (negate == null)
			negate = t.getFunction("-", numSort);
		assert (!isInt || m_constant.ma.isIntegral());
		Term comb = m_constant.ma.equals(Rational.ZERO) ? null 
				: isInt ? t.numeral(m_constant.ma.numerator())
				: t.rational(m_constant.ma.numerator(), m_constant.ma.denominator());
		for (Map.Entry<Term,Rational> me : m_summands.entrySet()) {
			Term convme = me.getKey();
			// if affine term is integral it may only add integers.
			assert (!isInt || convme.getSort().getName().equals("Int"));
			assert (!isInt || me.getValue().isIntegral());
			if (!isInt && convme.getSort().getName().equals("Int")) {
				Sort intSort = t.getSort("Int");
				FunctionSymbol toReal = t.getFunction("to_real", intSort);
				convme = t.term(toReal, convme);
			}
			if (me.getValue().equals(Rational.MONE)) {
				convme = t.term(negate, convme);
			} else if (!me.getValue().equals(Rational.ONE)) {
				Term convfac = isInt ? t.numeral(me.getValue().numerator())
						: t.rational(me.getValue().numerator(),me.getValue().denominator());
				convme = t.term(times, convfac, convme);
			}
			if (comb == null)
				comb = convme;
			else
				comb = t.term(plus, convme, comb);
		}
		if (comb == null)
			return isInt ? t.numeral(BigInteger.ZERO) : t.rational(BigInteger.ZERO, BigInteger.ONE);
		return comb;
	}
	
	public boolean isInt() {
		for (Term v : m_summands.keySet())
			if (!v.getSort().getName().equals("Int"))
				return false;
		return true;
	}
	
	/**
	 * Create the term <code>this <= val</code>.
	 * @param t   Theory used in conversion.
	 * @return A term for <code>this <= val</code>.
	 */
	public Term toLeq0(Theory t) {
		assert(m_constant.meps >= 0);
		if (isConstant())
			return m_constant.compareTo(InfinitNumber.ZERO) <= 0 ? t.TRUE : t.FALSE; 
		boolean isInt = isInt();
		Sort numSort = isInt ? t.getSort("Int") : t.getSort("Real");
		assert(numSort != null);
		Sort[] binfunc = new Sort[] {numSort,numSort};
		FunctionSymbol times = t.getFunction("*",binfunc);
		FunctionSymbol plus = t.getFunction("+",binfunc);
		ArrayList<Term> lcomb = new ArrayList<Term>();
		ArrayList<Term> rcomb = new ArrayList<Term>();
		for (Map.Entry<Term,Rational> me : m_summands.entrySet()) {
			Term convme = me.getKey();
			// if affine term is integral it may only add integers.
			assert (!isInt || convme.getSort().getName().equals("Int"));
			assert (!isInt || me.getValue().isIntegral());
			if (!isInt && convme.getSort().getName().equals("Int")) {
				Sort intSort = t.getSort("Int");
				FunctionSymbol toReal = t.getFunction("to_real", intSort);
				convme = t.term(toReal, convme);
			}
			if (me.getValue().equals(Rational.MONE))
				rcomb.add(convme);
			else if (me.getValue().signum() < 0) {
				Rational cf = me.getValue().abs();
				Term convfac = isInt ? t.numeral(cf.numerator())
						: t.rational(cf.numerator(),cf.denominator());
				rcomb.add(t.term(times, convfac, convme));
			} else if (me.getValue().equals(Rational.ONE))
				lcomb.add(convme);
			else if (me.getValue().signum() > 0) {
				Rational cf = me.getValue();
				Term convfac = isInt ? t.numeral(cf.numerator())
						: t.rational(cf.numerator(),cf.denominator());
				lcomb.add(t.term(times, convfac, convme));
			}
		}
		InfinitNumber constant = isInt ? m_constant.ceil() : m_constant;
		if (!constant.ma.equals(Rational.ZERO)) 
			rcomb.add(isInt ? t.numeral(constant.ma.numerator().negate())
			: t.rational(constant.ma.numerator().negate(), constant.ma.denominator()));
		if (lcomb.isEmpty() && rcomb.isEmpty())
			// We either have 0<=0 or 0<0
			return constant.meps == 0 ? t.TRUE : t.FALSE;
		Term tlcomb, trcomb;
		switch (lcomb.size()) {
		case 0:
			tlcomb = isInt ?
				t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
			break;
		case 1:
			tlcomb = lcomb.get(0);
			break;
		default:
			tlcomb = t.term(plus, lcomb.toArray(new Term[lcomb.size()]));
		}
		switch (rcomb.size()) {
		case 0:
			trcomb = isInt ?
				t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
			break;
		case 1:
			trcomb = rcomb.get(0);
			break;
		default:
			trcomb = t.term(plus, rcomb.toArray(new Term[rcomb.size()]));
		}				
		return t.term(constant.meps == 0 ? "<=" : "<",
				tlcomb, trcomb);
	}
	
	public int hashCode() {
		return m_constant.hashCode() + 1021 * m_summands.hashCode();
	}
}
