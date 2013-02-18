package local.stalin.smt.hack;

import java.util.Map;
import java.util.Set;

import local.stalin.logic.EqualsAtom;
import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.smt.convert.ConvertFormula;

public class GroundMap {
	private static final class GroundMapHolder {
		private static final GroundMap singleton = new GroundMap();
	}
	public static GroundMap singletonGroundMap() {
		return GroundMapHolder.singleton;
	}
	
	private Map<QuantifiedFormula,Map<TermVariable,Term>> skolemMap;
	private Map<QuantifiedFormula,Set<Instantiation>> instantiationMap;
	private Map<TermVariable,SymbolRange> localityMap;
	private Map<EqualsAtom,SymbolRange> auxeqs;
	private boolean auxeqsadded = false;
	public Map<QuantifiedFormula, Map<TermVariable,Term>> getSkolemMap() {
		return skolemMap;
	}
	public void setSkolemMap(Map<QuantifiedFormula, Map<TermVariable,Term>> skolemMap) {
		this.skolemMap = skolemMap;
	}
	public Map<QuantifiedFormula, Set<Instantiation>> getInstantiationMap() {
		return instantiationMap;
	}
	public void setInstantiationMap(
			Map<QuantifiedFormula, Set<Instantiation>> instantiationMap) {
		this.instantiationMap = instantiationMap;
	}
	public void setLocalityMap(Map<TermVariable,SymbolRange> theMap) {
		localityMap = theMap;
	}
	public void setAuxEqs(Map<EqualsAtom,SymbolRange> aeq) {
		auxeqs = aeq;
		auxeqsadded = false;
	}
	public void addAuxEqs(ConvertFormula cf) {
		if (!auxeqsadded) {
			for (Map.Entry<EqualsAtom,SymbolRange> me : auxeqs.entrySet())
				cf.addAuxEq(me.getKey(),me.getValue());
			auxeqsadded = true;
		}
	}
	public Map<TermVariable,Term> getSkolemization(QuantifiedFormula qf) {
		return skolemMap.get(qf);
	}
	public Set<Instantiation> getInstantiations(QuantifiedFormula qf,Instantiation parent) {
		return parent == null ? instantiationMap.get(qf) : parent.getChildren(qf);
	}
	public Map<TermVariable,SymbolRange> getLocalityMap() {
		return localityMap;
	}
	/**
	 * Get locality information for a TermVariable
	 * @param tv TermVariable to get locality for.
	 * @return <code>null</code> if this variable was not introduced by instantiation,
	 * 			<code>Boolean.TRUE</code> if this variable should existentially quantified,
	 * 			<code>Boolean.FALSE</code> if it should be universally quantified.
	 */
	public SymbolRange getLocality(TermVariable tv) {
		return localityMap.get(tv);
	}
}
