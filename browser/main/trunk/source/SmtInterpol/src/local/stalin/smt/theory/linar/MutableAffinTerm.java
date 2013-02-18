package local.stalin.smt.theory.linar;

import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;

import local.stalin.logic.Term;
import local.stalin.logic.Theory;


/**
 *  Represents a modifiable affin term, i.e. SUM_i c_i * x_i + c, 
 *  where the x_i are initially nonbasic variable.
 *    
 *  @author hoenicke.
 */
public class MutableAffinTerm {
	private boolean isIntegral;
	Map<LinVar, Rational> summands = new TreeMap<LinVar, Rational>();
	InfinitNumber constant;
	
	public MutableAffinTerm(boolean isInt) {
		constant = InfinitNumber.ZERO;
		isIntegral = isInt;
	}

	public MutableAffinTerm add(Rational c) {
		constant = constant.add(new InfinitNumber(c, Rational.ZERO));
		return this;
	}
	
	public MutableAffinTerm add(InfinitNumber c) {
		constant = constant.add(c);
		return this;
	}
	public MutableAffinTerm add(Rational c, LinVar linVar) {
		if (c.equals(Rational.ZERO))
			return this;
		if (linVar.mname instanceof LinTerm) {
			addMap(c, ((LinTerm)linVar.mname).mcoeffs);
		} else {
			addSimple(c, linVar);
		}
		return this;
	}

	public void addALocal(Rational c, LinVar linVar, int cutpos) {
		if (linVar.mname instanceof LinTerm) {
			for (Map.Entry<LinVar, Rational> summand : ((LinTerm)linVar.mname).mcoeffs.entrySet()) {
				if (summand.getKey().getLastFormulaNr() <= cutpos)
					addSimple(c.mul(summand.getValue()), summand.getKey());
			}
		} else {
			if (linVar.getLastFormulaNr() <= cutpos)
				addSimple(c, linVar);
		}
	}
	
	private void addMap(Rational c, Map<LinVar, Rational> linterm) {
		for (Map.Entry<LinVar, Rational> summand : linterm.entrySet())
			addSimple(c.mul(summand.getValue()), summand.getKey());
	}
	
	public void addSimple(Rational c, LinVar linVar) {
		// This assertion should not hold for cut generation
//		assert (!linVar.isInitiallyBasic() && !c.equals(Rational.ZERO));
		assert !isIntegral || linVar.misint;
		Rational oldc = summands.remove(linVar);
		if (oldc != null) {
			c = oldc.add(c);
			if (c.equals(Rational.ZERO))
				return;
		}
		summands.put(linVar,c);
	}

	public MutableAffinTerm add(Rational c, AffinTerm a) {
		if (c != Rational.ZERO) {
			addMap(c, a.factors);
			constant = constant.add(new InfinitNumber(a.constant.mul(c), Rational.ZERO));
		}
		return this;
	}
	public MutableAffinTerm add(Rational c, MutableAffinTerm a) {
		if (c != Rational.ZERO) {
			addMap(c, a.summands);
			constant = constant.add(a.constant.mul(c));
		}
		return this;
	}

	public MutableAffinTerm mul(Rational c) {
		if (c.equals(Rational.ZERO))
			summands.clear();
		else if (!c.equals(Rational.ONE)) {
			for (Map.Entry<LinVar, Rational> summand : summands.entrySet()) {
				summand.setValue(c.mul(summand.getValue()));
			}
			constant = constant.mul(c);
		}
		return this;
	}
	
	public MutableAffinTerm div(Rational c) {
		return mul(c.inverse());
	}
	public MutableAffinTerm negate() {
		return mul(Rational.MONE);
	}
	public boolean isConstant() {
		return summands.isEmpty();
	}
	public InfinitNumber getConstant() {
		return constant;
	}
	
	public Rational getGCD() {
		assert (!summands.isEmpty());
		Iterator<Rational> it = summands.values().iterator();
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

	public boolean isIntegral() {
		return isIntegral;
	}
	
	public String toString() {
		String s = new AffinTerm(this).toString();
		if (constant.mb.equals(Rational.ZERO))
			return s;
		return s + (constant.mb.isNegative() ? " - " : " + ")
		         + (constant.mb.abs().equals(Rational.ONE) ? "" : constant.mb.abs()+"*")
		         + "eps";
	}
	
	/**
	 * Convert the affin term to SMT lib
	 */ 
	public Term toSMTLib(Theory t) {
		assert(constant.mb.equals(Rational.ZERO));
		return new AffinTerm(this).toSMTLib(t);
	}

	public int getFirstFormulaNr() {
		int fnr = 0;
		for (LinVar lv : summands.keySet())
			fnr = Math.max(fnr, lv.getFirstFormulaNr());
		return fnr;
	}
	public int getLastFormulaNr() {
		int fnr = Integer.MAX_VALUE;
		for (LinVar lv : summands.keySet())
			fnr = Math.min(fnr, lv.getLastFormulaNr());
		return fnr;
	}
}