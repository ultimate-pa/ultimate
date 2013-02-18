package local.stalin.smt.theory.linar;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.logic.FormulaVariable;
import local.stalin.logic.Theory;
import local.stalin.smt.dpll.DPLLAtom;
import local.stalin.smt.dpll.DPLLEngine;
import local.stalin.smt.dpll.InterpolationInfo;
import local.stalin.smt.dpll.Interpolator;
import local.stalin.smt.dpll.Literal;

public class LinArInterpolator implements Interpolator {
	Theory theory;
	Map<FormulaVariable, LinInterpolant> placeholders;
	Set<Literal> activeLiterals;
	
	public LinArInterpolator(Theory t, FormulaVariable fvar, LinInterpolant term) {
		theory = t;
		placeholders = Collections.singletonMap(fvar, term);
	}

	public LinArInterpolator(Theory t, Map<FormulaVariable,LinInterpolant> map) {
		theory = t;
		placeholders = map;
	}
	
	@Override
	public Interpolator merge(Interpolator other) {
		assert (other instanceof LinArInterpolator);
		LinArInterpolator o = (LinArInterpolator) other;
		Map<FormulaVariable, LinInterpolant> newMap =
			new HashMap<FormulaVariable, LinInterpolant>();
		newMap.putAll(placeholders);
		newMap.putAll(o.placeholders);
		return new LinArInterpolator(theory, newMap);
	}
	
	@Override
	public InterpolationInfo interpolate(DPLLEngine engine, DPLLAtom atom,
			int fnr, InterpolationInfo interpolationInfo,
			InterpolationInfo otherInfo) {
		BoundConstraint bc = (BoundConstraint) atom;
		Interpolator other = otherInfo.getMixedLiteralInterpolator(atom);
		assert(other instanceof LinArInterpolator);
		LinArInterpolator otherla = (LinArInterpolator) other;
		Formula otherFormula = otherInfo.getFormula();
		HashMap<FormulaVariable, LinInterpolant> newpl =
			new HashMap<FormulaVariable, LinInterpolant>();
		Formula newForm = interpolationInfo.getFormula();
		for (Map.Entry<FormulaVariable, LinInterpolant> pl : placeholders.entrySet()) {
			assert !otherla.placeholders.containsKey(pl.getKey());
			LinInterpolant ip = pl.getValue();
			if (ip.mixedAtoms.contains(bc)) {
				Formula newsubform = otherFormula;
				for (Map.Entry<FormulaVariable, LinInterpolant> otherpl : otherla.placeholders.entrySet()) {
					LinInterpolant otherip = otherpl.getValue();
					if (otherip.mixedAtoms.contains(bc)) {
						LinInterpolant newip = ip.merge(theory, otherip, bc);
						if (newip.mixedAtoms.isEmpty()) {
							newsubform = theory.flet(otherpl.getKey(), newip.createFormula(theory), newsubform);
						} else {
							FormulaVariable newfvar = theory.createFreshFormulaVariable("LA");
							newsubform = theory.flet(otherpl.getKey(), theory.atom(newfvar), newsubform);
							newpl.put(newfvar, newip);
						}
					} else {
						newpl.put(otherpl.getKey(), otherip);
					}
				}
				newForm = theory.flet(pl.getKey(), newsubform, newForm);
			} else {
				newpl.put(pl.getKey(), ip);
			}
		}
		LinArInterpolator newInterpolator = new LinArInterpolator(theory, newpl);
		HashMap<DPLLAtom,Interpolator> interpolators = 
			new HashMap<DPLLAtom, Interpolator>();
		for (Map.Entry<DPLLAtom, Interpolator> entry : interpolationInfo.getInterpolators().entrySet())  {
			if (entry.getKey() == atom)
				continue;
			if (entry.getValue() == this) {
				interpolators.put(entry.getKey(), newInterpolator);
			} else {
				interpolators.put(entry.getKey(), entry.getValue());
			}
		}
		for (Map.Entry<DPLLAtom, Interpolator> entry : otherInfo.getInterpolators().entrySet())  {
			if (entry.getKey() == atom)
				continue;
			if (entry.getValue() == other) {
				interpolators.put(entry.getKey(), newInterpolator);
			} else {
				interpolators.put(entry.getKey(), entry.getValue());
			}
		}
		return new InterpolationInfo(newForm, interpolators);
	}
	
	public String toString() {
		return "(repl. " + placeholders + ")";
	}
}
