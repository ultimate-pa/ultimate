/**
 * 
 */
package local.stalin.smt.convert;

import java.util.HashSet;
import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.smt.dpll.Literal;
import local.stalin.smt.dpll.NamedAtom;

class IfThenElseFormula extends FlatFormula {
	FlatFormula cond;
	FlatFormula thenForm;
	FlatFormula elseForm;
	IfThenElseFormula negated;
	Literal lit;
	boolean auxAxiomsAdded;
	HashSet<FlatFormula> subforms;
	Formula smtFormula;
	
	public IfThenElseFormula(ConvertFormula converter, 
			FlatFormula cond, FlatFormula thenForm, FlatFormula elseForm) {
		super(converter);
		this.cond = cond;
		this.thenForm = thenForm;
		this.elseForm = elseForm;
		this.negated = new IfThenElseFormula(this);
	}
	/**
	 * Create a negated IfThenElse formula.
	 */
	private IfThenElseFormula(IfThenElseFormula negated) {
		super(negated.converter);
		this.cond = negated.cond;
		this.thenForm = negated.elseForm;
		this.elseForm = negated.thenForm;
		this.negated = negated;
	}

	public FlatFormula negate() {
		return negated;
	}
	
	//@Override
	public void addAuxAxioms(int formNumber) {
		Literal[] lits;
		int dest;
		/* "lit /\ cond ==> thenForm" and  "lit /\ !cond ==> elseForm" */
		HashSet<FlatFormula> clause = new HashSet<FlatFormula>();

		clause.addAll(cond.negate().getSubFormulas());
		clause.addAll(thenForm.getSubFormulas());
		lits = new Literal[clause.size()+1];
		dest = 0;
		lits[dest++] = lit.negate();
		for (FlatFormula ff : clause) {
			Literal l = lits[dest++] = ff.getLiteral(formNumber);
			l.getAtom().setInstantiationVariables(ff.termVariables);
		}
		converter.addClause(lits,formNumber);
		clause.clear();

		clause.addAll(cond.getSubFormulas());
		clause.addAll(elseForm.getSubFormulas());
		lits = new Literal[clause.size()+1];
		dest = 0;
		lits[dest++] = lit.negate();
		for (FlatFormula ff : clause) {
			Literal l = lits[dest++] = ff.getLiteral(formNumber);
			l.getAtom().setInstantiationVariables(ff.termVariables);
		}
		converter.addClause(lits,formNumber);
		auxAxiomsAdded = true;
	}

	//@Override
	public void addAsAxiom(int formNumber) {
		Literal[] lits;
		int dest;
		/* "lit /\ cond ==> thenForm" and  "lit /\ !cond ==> elseForm" */
		HashSet<FlatFormula> clause = new HashSet<FlatFormula>();

		clause.addAll(cond.negate().getSubFormulas());
		clause.addAll(thenForm.getSubFormulas());
		lits = new Literal[clause.size()];
		dest = 0;
		for (FlatFormula ff : clause) {
			Literal l = lits[dest++] = ff.getLiteral(formNumber);
			l.getAtom().setInstantiationVariables(ff.termVariables);
		}
		converter.addClause(lits,formNumber);
		clause.clear();

		clause.addAll(cond.getSubFormulas());
		clause.addAll(elseForm.getSubFormulas());
		lits = new Literal[clause.size()];
		dest = 0;
		for (FlatFormula ff : clause) {
			Literal l = lits[dest++] = ff.getLiteral(formNumber);
			l.getAtom().setInstantiationVariables(ff.termVariables);
		}
		converter.addClause(lits,formNumber);
	}

	public Formula getSMTFormula() {
		if (smtFormula == null) {
			if (thenForm == elseForm.negate())
				smtFormula = converter.dpllEngine.getSMTTheory().
					iff(cond.getSMTFormula(), thenForm.getSMTFormula());
			else
				smtFormula = converter.dpllEngine.getSMTTheory().
					ifthenelse(cond.getSMTFormula(), thenForm.getSMTFormula(), elseForm.getSMTFormula());
		}
		return smtFormula;
	}

	//@Override
	public Literal getLiteral(int formNumber) {
		if (lit == null) {
			lit = converter.createAnonAtom(getSMTFormula());
			negated.lit = lit.negate();
		}
		((NamedAtom) lit.getAtom()).occursIn(formNumber);
		if (!auxAxiomsAdded)
			addAuxAxioms(formNumber);
		return lit;
	}

	public Set<FlatFormula> getSubFormulas() {
		if (subforms == null) {
			subforms = new HashSet<FlatFormula>();
			subforms.addAll(converter.convertDisjunction(cond.negate(),thenForm.negate()).negate().getSubFormulas());
			subforms.addAll(converter.convertDisjunction(cond,elseForm.negate()).negate().getSubFormulas());
		}
		return subforms;
	}
	
	public String toString() {
		return "(IFTHENELSE " + cond + " " +thenForm + " " + elseForm + ")";
	}
}