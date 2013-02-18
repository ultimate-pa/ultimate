package local.stalin.smt.convert;

import java.util.Collections;
import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.smt.dpll.Literal;
import local.stalin.smt.dpll.NamedAtom;
import local.stalin.smt.util.DebugMessage;

public class GroundifyForallFormula extends FlatFormula {
	Formula smtForm;
	NamedAtom lit;
	private GroundifyNegForallFormula negated;
	private boolean auxAxiomsAdded;
	FlatFormula skolemForm;
	FlatFormula[] instances;
	
	public GroundifyForallFormula(ConvertFormula converter,Formula smtFormula,FlatFormula[] insts,FlatFormula skolem) {
		super(converter);
		smtForm = smtFormula;
		negated = new GroundifyNegForallFormula(this);
		auxAxiomsAdded = false;
		skolemForm = skolem;
		instances = insts;
	}

	@Override
	public void addAsAxiom(int formNumber) {
		if (instances != null) {
			converter.dpllEngine.getLogger().debug(new DebugMessage("Adding {0}",smtForm));
			for (FlatFormula inst : instances) {
				converter.dpllEngine.getLogger().debug(new DebugMessage("Instance: {0}",inst));
				inst.addAsAxiom(formNumber);
			}
		} else
			converter.dpllEngine.getLogger().debug(new DebugMessage("Trying to add {0} which has no instantiations",smtForm));
	}
	
	public void addAuxAxioms(int formNumber) {
		if (instances != null) {
			converter.dpllEngine.getLogger().debug(new DebugMessage("Adding {0} as aux axioms",smtForm));
			for (FlatFormula inst : instances) {
				Set<FlatFormula> clause = inst.getSubFormulas();
				Literal[] lits = new Literal[clause.size() + 1];
				int dest = 0;
				lits[dest] = lit.negate();
				for (FlatFormula instsub : clause) {
					Literal l = lits[++dest] = instsub.getLiteral(formNumber);
					l.getAtom().setInstantiationVariables(instsub.termVariables);
				}
				converter.addClause(lits,formNumber);
			}
		} else {
			converter.dpllEngine.getLogger().debug(new DebugMessage("Trying to add {0} which has no instantiations. Marking false...",smtForm));
			//converter.addClause(new Literal[]{ lit.negate() }, formNumber);
		}
		auxAxiomsAdded = true;
	}

	@Override
	public Literal getLiteral(int formNumber) {
		if (lit == null) {
			lit = converter.createAnonAtom(smtForm);
		}
		lit.occursIn(formNumber);
		if (!auxAxiomsAdded)
			addAuxAxioms(formNumber);
		return lit;
	}

	@Override
	public Formula getSMTFormula() {
		return smtForm;
	}

	@Override
	public FlatFormula negate() {
		return negated;
	}

	@Override
	public Set<FlatFormula> getSubFormulas() {
		return Collections.singleton((FlatFormula)this);
	}

	public String toString() {
		return smtForm.toString();
	}
}
