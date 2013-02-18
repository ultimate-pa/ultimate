package local.stalin.smt.hack;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.logic.QuantifiedFormula;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;

public class Instantiation {
	private Map<TermVariable,Term> mrealinsts;
	private Map<TermVariable,Term> minsts;
	private Instantiation parent = null;
	private Map<QuantifiedFormula,Set<Instantiation>> children = null;
	public
	Instantiation(Map<TermVariable,Term> realinsts,Map<TermVariable,Term> insts) {
		assert(realinsts != null);
		assert(insts != null);
		mrealinsts = realinsts;
		minsts = insts;
	}
	public Map<TermVariable,Term> getInstances() {
		return minsts;
	}
	public String toString() {
		return minsts.toString();
	}
	
	public int hashCode() {
		return minsts.hashCode();
	}
	
	public boolean equals(Object o) {
		if (o instanceof Instantiation) {
			Instantiation other = (Instantiation) o;
			return minsts.equals(other.minsts);
		}
		return false;
	}
	public void addChild(QuantifiedFormula qf,Instantiation inst) {
		inst.parent = this;
		if (children == null)
			children = new HashMap<QuantifiedFormula,Set<Instantiation>>();
		Set<Instantiation> insts = children.get(qf);
		if (insts == null)
			insts = new HashSet<Instantiation>();
		insts.add(inst);
		children.put(qf,insts);
	}
	public Instantiation getParent() {
		return parent;
	}
	public Set<Instantiation> getChildren(QuantifiedFormula qf) {
		return children != null ? children.get(qf) : null;
	}
	public boolean matches(Map<TermVariable,Term> realinst) {
		return mrealinsts.equals(realinst);
	}
	public Instantiation getMatchingChild(Map<TermVariable,Term> realinst, QuantifiedFormula qf) {
		if (children == null) return null;
		Set<Instantiation> qfchildren = children.get(qf);
		for (Instantiation child : qfchildren)
			if (child.matches(realinst))
				return child;
		return null;
	}
}
