package local.stalin.smt.smtlib;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import local.stalin.logic.Formula;
import local.stalin.logic.Theory;

public class Benchmark {
	private Theory theory;
	private List<Formula> formulaList; 
	private List<Formula> axiomList;
	
	public Benchmark(Theory theory) {
		this.theory = theory;
		formulaList = new LinkedList<Formula>();
		axiomList = null;
	}
	
	public void addFormula(Formula f) {
		formulaList.add(f);
	}
	
	public List<Formula> getFormulae() {
		return formulaList;
	}
	
	public Theory getTheory() {
		return theory;
	}
	
	public void note(String s) {
		if( "Interpolation Problem starts here".equals(s) ) {
			axiomList = formulaList;
			formulaList = new LinkedList<Formula>();
			Collection<Formula> axioms = theory.getAxioms();
			if (axioms.isEmpty()) {
				for( Formula f : axiomList )
					theory.createAxiom(f);
			} else {
				// Try a symmetric diff (both should be lists...)
				List<Formula> laxioms = (List<Formula>)axioms;
				if (laxioms.size() != axiomList.size()) {
					System.err.println("Different axiom lengths!!!");
					throw new AssertionError("Different axiom lengths!!!");
				}
				for (int i = 0; i < laxioms.size(); ++i) {
					if (laxioms.get(i) != axiomList.get(i)) {
						System.err.println(laxioms.get(i));
						System.err.println(axiomList.get(i));
						throw new AssertionError("Different axioms at possition " + i);
					}
				}
			}
		}
	}
	
	public List<Formula> getAxioms() {
		return axiomList;
	}
	
}
