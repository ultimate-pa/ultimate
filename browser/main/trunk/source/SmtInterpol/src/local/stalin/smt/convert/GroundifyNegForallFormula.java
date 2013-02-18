package local.stalin.smt.convert;

import java.util.Collections;
import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.smt.dpll.Literal;
import local.stalin.smt.util.DebugMessage;

public class GroundifyNegForallFormula extends FlatFormula {
	private GroundifyForallFormula positive;
	private boolean auxAxiomsAdded;
	public GroundifyNegForallFormula(GroundifyForallFormula positive) {
		super(positive.converter);
		this.positive = positive;
		auxAxiomsAdded = false;
	}

	@Override
	public void addAsAxiom(int formNumber) {
		if (positive.skolemForm != null) {
			converter.dpllEngine.getLogger().debug(new DebugMessage("Adding (not {0})",positive.smtForm));
			positive.skolemForm.addAsAxiom(formNumber);
		} else
			converter.dpllEngine.getLogger().debug(new DebugMessage("Trying to add skolemized form for {0} which does not exist",converter.dpllEngine.getSMTTheory().not(positive.getSMTFormula())));
	}

	public void addAuxAxioms(int formNumber) {
		if (positive.skolemForm != null) {
			converter.dpllEngine.getLogger().debug(new DebugMessage("Adding (not {0}) as aux axioms",positive.smtForm));
			Set<FlatFormula> subs = positive.skolemForm.getSubFormulas();
			Literal[] lits = new Literal[subs.size()+1];
			int dest = 0;
			lits[dest] = positive.lit;
			for (FlatFormula sub : subs) {
				Literal l = lits[++dest] = sub.getLiteral(formNumber);
				l.getAtom().setInstantiationVariables(sub.termVariables);
			}
			converter.addClause(lits,formNumber);
		} else {
			converter.dpllEngine.getLogger().debug(new DebugMessage("Trying to add skolemized form for {0} which does not exist. Marking false...",converter.dpllEngine.getSMTTheory().not(positive.getSMTFormula())));
			//converter.addClause(new Literal[]{ positive.lit }, formNumber);
		}
		auxAxiomsAdded = true;
	}
	
	@Override
	public Literal getLiteral(int formNumber) {
		if (positive.lit == null)
			positive.lit = this.converter.createAnonAtom(positive.getSMTFormula());
		positive.lit.occursIn(formNumber);
		if (!auxAxiomsAdded)
			addAuxAxioms(formNumber);
		return positive.lit.negate();
	}

	@Override
	public Formula getSMTFormula() {
		return converter.dpllEngine.getSMTTheory().not(positive.getSMTFormula());
	}

	@Override
	public FlatFormula negate() {
		return positive;
	}

	@Override
	public String toString() {
		return "(NOT "+positive+")";
	}

	@Override
	public Set<FlatFormula> getSubFormulas() {
		return Collections.singleton((FlatFormula)this);
	}

}
