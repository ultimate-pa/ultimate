package local.stalin.smt.theory.linar;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.logic.FormulaVariable;
import local.stalin.logic.Sort;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.smt.dpll.Clause;
import local.stalin.smt.dpll.DPLLAtom;
import local.stalin.smt.dpll.InterpolationInfo;
import local.stalin.smt.dpll.Interpolator;
import local.stalin.smt.dpll.Literal;

/**
 * Set of literals supporting a cut. Fixed variables are remembered 
 * differently.
 * @author Juergen Christ
 */
class CutSupportSet {
	private final static int TYPE_INC = 1;
	private final static int TYPE_EQ  = 0;
	private final static int TYPE_DEC = -1;
	
	int numEqs = 0;
	
	ArrayList<CutSupporter> supportset;
	Rational frac;
	
	static class CutSupporter {
		int type;
		Rational coeff;
		LinVar var;
		Rational bound;  // should be var.mcurval
		
		public CutSupporter(int t, Rational c, LinVar v) {
			type  = t;
			coeff = c;
			var   = v;
			bound = v.mcurval.ma;
		}
		
		public String toString() {
			String t = (type == TYPE_DEC ? "dec"
				: type == TYPE_EQ ? "eq" : "inc");
			return t+":"+coeff+"*("+var+"-"+bound+")";
		}
	}
	
	/**
	 * Create a new cut support set.
	 * @param f the fractional part of mcurval of the variable we cut on.
	 */
	CutSupportSet(Rational f) {
		this.frac = f;
		supportset = new ArrayList<CutSupporter>();
	}
	
	/**
	 * Add a fixed variable to this support set. Updates the formula numbers.
	 * @param v     Fixed variable.
	 * @param coeff Coefficient in the current row of the tableau.
	 */
	void addFixedVar(LinVar v,Rational coeff) {
		assert(v.mlbound.compareTo(v.mubound) == 0);
		supportset.add(new CutSupporter(TYPE_EQ, coeff, v));
		numEqs++;
	}
	
	/**
	 * Add an inequality literal. Updates the formula numbers.
	 * @param l Literal to add.
	 * @param coeff the coefficient.
	 * @param canDecrement  true if changing the variable decrements
	 *        the cut variable under consideration.
	 */
	void addIneq(LinVar v, Rational coeff, boolean canDecrement) {
		coeff = coeff.frac();
		if (canDecrement)
			coeff = coeff.add(Rational.MONE);
		if (frac.add(coeff.abs()).compareTo(Rational.ONE) < 0) {
			supportset.add(new CutSupporter(TYPE_INC, coeff, v));
		} else {
			coeff = coeff.add(coeff.isNegative() ? Rational.ONE : Rational.MONE);
			supportset.add(new CutSupporter(TYPE_DEC, coeff, v));
		}
	}
	
	public MutableAffinTerm computeCut() {
//		System.out.println("Computing cut: "+this);
		MutableAffinTerm cut = new MutableAffinTerm(true);
		Rational fracmone = frac.add(Rational.MONE);
		
		for (CutSupporter supporter: supportset) {
			if (supporter.type == TYPE_EQ)
				continue;
			
			Rational rc = supporter.type == TYPE_INC ? frac : fracmone;
			rc = rc.mul(supporter.coeff);
			cut.addSimple(rc, supporter.var);
			cut.add(rc.mul(supporter.bound.negate()));
		}
		cut.add(frac.mul(fracmone));
		cut.negate();
//		System.out.println("cut formula: "+cut);
		return cut;
	}
	
	public int getNumLiterals() {
		/* We need two literals for each equation, so add
		 * numEqs to the supportset size.
		 */
		return supportset.size() + numEqs;
	}
	
	public void fillSupportLiterals(Literal[] lits) {
		int i = 0;
		for (CutSupporter supporter : supportset) {
			if (supporter.coeff.signum() * supporter.type >= 0)
				lits[i++] = supporter.var.lowerassert.negate();
			if (supporter.coeff.signum() * supporter.type <= 0)
				lits[i++] = supporter.var.upperassert.negate();
		}
	}
	
	@SuppressWarnings("unchecked")
	public Clause interpolateUnsatCut(Theory theory, int numIpls) {
		return computeCutClause(theory, null, null, numIpls);
	}
	
	@SuppressWarnings("unchecked")
	public Clause computeCutClause(Theory theory, Literal cutLiteral, Rational normFactor, int numIpls) {
		BoundConstraint cutbc = cutLiteral == null ? null : (BoundConstraint) cutLiteral.getAtom();
		LinVar cutVar = cutLiteral == null ? null : cutbc.mvar;
		Sort sort = theory.getSort("Int");
		TermVariable yvar = theory.createFreshTermVariable("cuty", sort);
		LinVar yvarlv = new LinVar(theory.term(yvar), true);
		InterpolationInfo[] interpolants = new InterpolationInfo[numIpls];
		for (int iplNr = 0; iplNr < numIpls; iplNr++) {
			MutableAffinTerm[] shared = new MutableAffinTerm[] {
					new MutableAffinTerm(true), // dec
					new MutableAffinTerm(true), // eq
					new MutableAffinTerm(true) // inc
			};
			Set<BoundConstraint>[] litSet = new HashSet[] {
					new HashSet<BoundConstraint>(), // dec
					new HashSet<BoundConstraint>() // inc
			};
			for (CutSupporter supporter: supportset) {
				LinVar var = supporter.var;
				if (iplNr < var.getLastFormulaNr()) {
					/* nothing */
				} else if (iplNr < var.getFirstFormulaNr()) {
					shared[supporter.type+1].add(supporter.coeff.negate(), var.mixedVar);
					if (supporter.bound.equals(var.mlbound)) {
						litSet[supporter.type <= 0 ? 0 : 1]
							.add((BoundConstraint)var.lowerassert.getAtom());
					}
					if (supporter.bound.equals(var.mubound)) {
						litSet[supporter.type < 0 ? 0 : 1]
							.add((BoundConstraint)var.upperassert.getAtom());
					}
				} else {
					shared[supporter.type+1].add(supporter.coeff, var)
						.add(supporter.coeff.negate().mul(supporter.bound))
						.addALocal(supporter.coeff.negate(), var, iplNr);
				}
			}
			
			shared[1].add(Rational.ONE, yvarlv);
			shared[0].add(frac, shared[1]);
			shared[2].add(Rational.ONE.sub(frac), shared[1]).negate();
			
			if (cutVar == null || iplNr < cutVar.getLastFormulaNr()) {
				/* nothing */
			} else if (iplNr < cutVar.getFirstFormulaNr()) {
				shared[0].add(normFactor.inverse().negate(), cutVar.mixedVar);
				shared[2].add(normFactor.inverse().negate(), cutVar.mixedVar);
				litSet[0].add((BoundConstraint)cutLiteral.getAtom());
				litSet[1].add((BoundConstraint)cutLiteral.getAtom());
			} else {
				shared[0].add(normFactor.inverse().negate(), cutVar)
					.addALocal(normFactor.inverse(), cutVar, iplNr);
				shared[2].add(normFactor.inverse().negate(), cutVar)
					.addALocal(normFactor.inverse(), cutVar, iplNr);
			}
			LinInterpolant li1 = new LinInterpolant(shared[0], litSet[0]);
			LinInterpolant li2 = new LinInterpolant(shared[2], litSet[1]);
			System.out.println("  li1: "+li1);
			System.out.println("  li2: "+li2);
			Formula form1, form2;
			Map<FormulaVariable, LinInterpolant> fvarMap = new HashMap<FormulaVariable, LinInterpolant>(2);
			if (litSet[0].isEmpty()) {
				form1 = li1.createFormula(theory);
			} else {
				FormulaVariable fvar = theory.createFreshFormulaVariable("FCut");
				fvarMap.put(fvar, li1);
				form1 = theory.atom(fvar);
			}
			if (litSet[1].isEmpty()) {
				form2 = li2.createFormula(theory);
			} else {
				FormulaVariable fvar = theory.createFreshFormulaVariable("FCut");
				fvarMap.put(fvar, li2);
				form2 = theory.atom(fvar);
			}
			Formula form = theory.exists(new TermVariable[] { yvar }, theory.and(form1, form2));
			LinArInterpolator iplator = new LinArInterpolator(theory, fvarMap);
			Map<DPLLAtom, Interpolator> mixedIplators = new
				HashMap<DPLLAtom, Interpolator>();
			for (BoundConstraint bc : litSet[0])
				mixedIplators.put(bc, iplator);
			for (BoundConstraint bc : litSet[1])
				mixedIplators.put(bc, iplator);
			interpolants[iplNr] = new InterpolationInfo(form, mixedIplators);
		}
		Literal[] lits = new Literal[getNumLiterals() + (cutLiteral != null ? 1 : 0)];
		fillSupportLiterals(lits);
		if (cutLiteral != null)
			lits[lits.length-1] = cutLiteral;
		return new Clause(lits, interpolants);
	}
	
	/**
	 * Check whether the cut support set is already unsatisfiable.
	 * This is the case if it contains no inequalities, so the
	 * non-integer value cannot be made integer by any change of 
	 * the non-basic variables. 
	 * 
	 * @return true if the support set by itself is unsatisfiable. 
	 */
	public boolean unsat() {
		return supportset.size() == numEqs;
	}
	
	public String toString() {
		return "css:" + supportset + " (f = " + frac + ")";
	}
}
