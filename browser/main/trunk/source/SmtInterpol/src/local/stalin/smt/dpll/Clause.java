package local.stalin.smt.dpll;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.smt.dpll.SimpleListable;

/**
 * This class represents a clause.
 * @author hoenicke
 *
 */
public class Clause extends SimpleListable<Clause> {
	Literal[] literals;
	/**
	 * The number of the formula this clause comes from, -1 for theory induced clause.
	 */
	int formulaNr;
	/**
	 * The interpolants.  This is an array containing one interpolant for
	 * every formula split.  
	 */
	InterpolationInfo[] interpolants;
	Watcher firstWatch, secondWatch;
	/**
	 * The activity of a clause.  Infinity for clauses that are not inferred.
	 * If the activity drops below some point the clause is removed.
	 */
	double activity;
	int usedTimes;
	
	/**
	 * Maps term variables to the number of literals supporting this termvariable. If
	 * support drops to 0, the variable should be quantified.
	 */
	Map<TermVariable,Integer> tvsupport;
	
	/**
	 * Set of variables we still need to infer a quantifier for.
	 */
	Set<TermVariable> pendingSet;
	
	public class Watcher extends SimpleListable<Watcher> {
		Watcher() {
		}
		
		public Clause getClause() {
			return Clause.this;
		}
	}
	
	public int getSize() {
		return literals.length;
	}
	public Literal getLiteral (int i) {
		return literals[i];
	}
	
	public Clause (Literal[] literals, InterpolationInfo[] interpolants) {
		this.literals = literals;
		this.interpolants = interpolants;
		this.formulaNr = -1;
		computeSupport();
	}
	Clause (Literal[] literals, int formulaNr) {
		this.literals = literals;
		this.interpolants = null;
		this.formulaNr = formulaNr;
		computeSupport();
	}
	
	private void computeSupport() {
		tvsupport = new HashMap<TermVariable,Integer>();
		for (Literal l : literals) {
			if (l.getAtom().instantiationVars != null)
				for (TermVariable tv : l.getAtom().instantiationVars) {
					Integer oldval = tvsupport.get(tv);
					if (oldval == null)
						tvsupport.put(tv,1);
					else
						tvsupport.put(tv,oldval+1);
				}
		}
	}
	
	public void createWatchers() {
		firstWatch = new Watcher();
		secondWatch = new Watcher();
	}
	
	public String toString() {
		return Arrays.toString(literals);
	}
	public InterpolationInfo getInterpolant(int cutnr) {
		assert(cutnr >= 0);
		assert(cutnr < interpolants.length);
		return interpolants[cutnr];
	}
	public void setActivityInfinite() {
		activity = Double.POSITIVE_INFINITY;
	}
	public int getSymbolCount(Term t) {
		int res = 0;
		for( Literal lit : literals ) {
			DPLLAtom atom = lit.getAtom();
			res += atom.containsTerm(t);
		}
		return res;
	}
}
