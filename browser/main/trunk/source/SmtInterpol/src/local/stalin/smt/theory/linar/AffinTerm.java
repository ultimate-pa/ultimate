package local.stalin.smt.theory.linar;

import java.math.BigInteger;
import java.util.Collections;
import java.util.Map;
import java.util.TreeMap;
import java.util.Map.Entry;

import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.Sort;
import local.stalin.logic.Term;
import local.stalin.logic.Theory;


/**
 *  Represents an AffinTerm, i.e. SUM_i c_i * x_i + c, where x_i is an initially
 *  nonbasic variable.
 *    
 *  @author hoenicke.
 */
public class AffinTerm {
	private boolean isIntegral;
	Map<LinVar, Rational> factors;
	Rational constant;
	
	public AffinTerm(Rational rat, boolean isInt) {
		factors = Collections.emptyMap();
		constant = rat;
		isIntegral = isInt;
	}
	
	public AffinTerm(LinVar linVar) {
		this(Rational.ONE, linVar);
	}
	public AffinTerm(LinTerm linTerm, boolean isInt) {
		isIntegral = isInt;
		constant = Rational.ZERO;
		factors = linTerm.mcoeffs;
	}
	public AffinTerm(Rational factor, LinVar linVar) {
		isIntegral = linVar.misint;
		if (factor.equals(Rational.ZERO))
			factors = Collections.emptyMap();
		else
			factors = Collections.singletonMap(linVar, factor);
		constant = Rational.ZERO;
	}
	public AffinTerm(AffinTerm a1, AffinTerm a2) {
		assert (a1.isIntegral == a2.isIntegral);
		this.isIntegral = a1.isIntegral;
		this.constant = a1.constant.add(a2.constant);
		this.factors = new TreeMap<LinVar, Rational>();
		this.factors.putAll(a1.factors);
		for (LinVar var : a2.factors.keySet()) {
			if (factors.containsKey(var)) {
				Rational r = factors.get(var).add(a2.factors.get(var));
				if (r.equals(Rational.ZERO))
					factors.remove(var);
				else
					factors.put(var, r);
			} else
				factors.put(var, a2.factors.get(var));
		}
	}
	
	public AffinTerm(AffinTerm a, Rational c) {
		this.isIntegral = a.isIntegral;
		this.constant = a.constant.mul(c);
		this.factors = new TreeMap<LinVar, Rational>();
		if (c != Rational.ZERO) {
			for (Map.Entry<LinVar,Rational> me : a.factors.entrySet()) {
				factors.put(me.getKey(), me.getValue().mul(c));
			}
		}
	}
	
	public AffinTerm(MutableAffinTerm maffin) {
		factors = maffin.summands;
		constant = maffin.constant.ma;
		isIntegral = maffin.isIntegral();
	}
	
	public AffinTerm add(AffinTerm l) {
		return new AffinTerm(this, l);
	}
	
	public AffinTerm mul(Rational c) {
		return new AffinTerm(this, c);
	}
	public AffinTerm div(Rational c) {
		return mul(Rational.ONE.div(c));
	}
	public AffinTerm negate() {
		return mul(Rational.MONE);
	}
	public boolean isConstant() {
		return factors.isEmpty();
	}
	public Rational getConstant() {
		return constant;
	}
	
	public boolean isIntegral() {
		return isIntegral;
	}
	
	public int hashCode() {
		return constant.hashCode()*11 + factors.hashCode();
	}
	
	public boolean equals(Object o) {
		if (!(o instanceof AffinTerm))
			return false;
		AffinTerm l = (AffinTerm) o;
		return isIntegral == l.isIntegral 
			&& constant.equals(l.constant)
			&& factors.equals(l.factors);
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		boolean isFirst = true;
		for (Entry<LinVar,Rational> entry : factors.entrySet()) {
			LinVar var = entry.getKey();
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
		if (constant.equals(Rational.ZERO)) {
			if (isFirst)
				sb.append("0");
		} else {
			if (constant.isNegative()) {
				sb.append(isFirst ? "-" : " - ");
			} else {
				sb.append(isFirst ? "" : " + ");
			}
			sb.append(constant.abs());
		}
		return sb.toString();
	}
	/**
	 * Convert the affin term to SMT lib
	 * 
	 */ 
	public Term toSMTLib(Theory t) {
		boolean integral = isIntegral();
		Sort numSort = integral ? t.getSort("Int") : t.getSort("Real");
		assert(numSort != null);
		Sort[] binfunc = new Sort[] {numSort,numSort};
		FunctionSymbol times = t.getFunction("*",binfunc);
		FunctionSymbol plus = t.getFunction("+",binfunc);
		FunctionSymbol negate = t.getFunction("~", numSort);
		if (negate == null)
			negate = t.getFunction("-", numSort);
		Term comb = constant.equals(Rational.ZERO) ? null 
				: integral ? t.numeral(constant.numerator())
				: t.rational(constant.numerator(), constant.denominator());
		for( Map.Entry<LinVar,Rational> me : factors.entrySet() ) {
			Term convme;
			if (me.getKey().isInitiallyBasic())
				convme = (new AffinTerm((LinTerm)me.getKey().mname,isIntegral).mul(me.getValue())).toSMTLib(t);
			else
				convme = (Term)me.getKey().mname;
			if (me.getValue().equals(Rational.MONE)) {
				convme = t.term(negate, convme);
			} else if (!me.getValue().equals(Rational.ONE)) {
				Term convfac = integral ? t.numeral(me.getValue().numerator())
						: t.rational(me.getValue().numerator(),me.getValue().denominator());
				convme = t.term(times, convfac, convme);
			}
			if (comb == null)
				comb = convme;
			else
				comb = t.term(plus, convme, comb);
		}
		if (comb == null)
			return integral ? t.numeral(BigInteger.ZERO) : t.rational(BigInteger.ZERO, BigInteger.ONE);
		return comb;
	}
	
	public void occursIn(int formulaNr) {
		for (LinVar lv : factors.keySet())
			lv.occursIn(formulaNr);
	}
	public int getFirstFormulaNr() {
		int fnr = 0;
		for (LinVar lv : factors.keySet())
			fnr = Math.max(fnr, lv.getFirstFormulaNr());
		return fnr;
	}
	public int getLastFormulaNr() {
		int fnr = Integer.MAX_VALUE;
		for (LinVar lv : factors.keySet())
			fnr = Math.min(fnr, lv.getLastFormulaNr());
		return fnr;
	}
}