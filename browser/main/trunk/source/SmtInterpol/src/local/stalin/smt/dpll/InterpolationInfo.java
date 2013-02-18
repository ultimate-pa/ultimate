package local.stalin.smt.dpll;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;

/**
 * The information needed to compute one interpolant.  The default
 * behaviour is a flat information containing a single formula.
 * Furthermore for every mixed literal we have an interpolator that
 * can compute a new interpolant if we resolve on this mixed literal.   
 * 
 * Let A be the conjunction of formulae 0-n, and B the conjunction of
 * formulae n+1 ff and let c be the current clause.  Let I(c) be the 
 * formula in the nth interpolant, l(c) be the literals of c that do 
 * not appear in B (local to A or mixed) and g(c) the remaining part 
 * (global). Then the following holds:
 * 
 * A ==>  l(c) || I(c)
 * B && I(c) ==> g(c)
 * I(c) contains only symbols that appear in both formulae A and B.
 * 
 * In other words, I(c) is an interpolant of A && !l(c) and B && !g(c).
 * 
 * Every interpolant is in CNF represented as simple list of simple list
 * of literals.
 * 
 */
public class InterpolationInfo {
	public static final InterpolationInfo TRUE = new InterpolationInfo(Atom.TRUE);
	public static final InterpolationInfo FALSE = new InterpolationInfo(Atom.FALSE);
	
	protected Formula interpolant;
	protected Map<DPLLAtom, Interpolator>  mixedLiteralInterpolator;

	public InterpolationInfo(Formula interpolant) {
		this.interpolant = interpolant;
		mixedLiteralInterpolator = Collections.emptyMap();
	}
	
	public InterpolationInfo(Formula interpolant,Map<DPLLAtom, Interpolator> mixedLiteralInterpolator) {
		this.interpolant = interpolant;
		this.mixedLiteralInterpolator = mixedLiteralInterpolator;
	}

	public InterpolationInfo interpolate(DPLLEngine engine, DPLLAtom atom, int fnr, InterpolationInfo otherInfo) {
		if (atom.getLastFormulaNr() > fnr) {
			/* in second part */
			return new InterpolationInfo(
					engine.andFormula(getFormula(), otherInfo.getFormula()),mergeMixedLiteralInterpolators(otherInfo,atom));
		} else if (atom.getFirstFormulaNr() <= fnr) {
			/* local to first part */
			return new InterpolationInfo(
					engine.orFormula(getFormula(), otherInfo.getFormula()),mergeMixedLiteralInterpolators(otherInfo,atom));
		} else {
			/* Mixed literal */
			Interpolator ip1 = mixedLiteralInterpolator.get(atom);
			Interpolator ip2 = otherInfo.getMixedLiteralInterpolator(atom);
			assert ip1 != null || ip2 != null : "Interpolation info neither set for positive nor negative literal";
			return ip1 != null ? ip1.interpolate(engine, atom, fnr, this, otherInfo) :
				ip2.interpolate(engine, atom, fnr, otherInfo, this);
		}
	}
	
	public Formula getFormula() {
		return interpolant;
	}
	
	public String toString() {
		if (!mixedLiteralInterpolator.isEmpty())
			return mixedLiteralInterpolator + " applied to " + getFormula();
		return getFormula().toString();
	}
	public void setMixedLiteral(DPLLAtom atom,Interpolator ip) {
		mixedLiteralInterpolator.put(atom,ip);
	}
	public Interpolator getMixedLiteralInterpolator(DPLLAtom atom) {
		return mixedLiteralInterpolator.get(atom);
	}
	@SuppressWarnings("unchecked")
	public HashMap<DPLLAtom,Interpolator> mergeMixedLiteralInterpolators(InterpolationInfo other,DPLLAtom except) {
		HashMap<DPLLAtom,Interpolator> res = new HashMap<DPLLAtom, Interpolator>(mixedLiteralInterpolator);
		res.remove(except);
		for (Entry<DPLLAtom, Interpolator> entry : other.mixedLiteralInterpolator.entrySet()) {
			DPLLAtom key = entry.getKey();
			if (key == except)
				continue;
			if (res.containsKey(key)) {
				res.put(key, res.get(key).merge(entry.getValue()));
			} else {
				res.put(key, entry.getValue());
			}
		}
		return res;
	}

	public Map<DPLLAtom, Interpolator> getInterpolators() {
		return mixedLiteralInterpolator;
	}
}
