package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class FormulasAndLevelAnnotations {
	private ArrayList<Term> edgeFormulas;
	private ArrayList<LevelAnnotations> levelAnnotations;
	
	public FormulasAndLevelAnnotations(List<FormulaAndLevelAnnotation> formulasAndLevelAnnotations) {
		this.edgeFormulas = new ArrayList<Term>();
		this.levelAnnotations = new ArrayList<LevelAnnotations>();
		for (FormulaAndLevelAnnotation formulaAndLvl : formulasAndLevelAnnotations) {
			this.edgeFormulas.add(formulaAndLvl.getFormula());
			this.levelAnnotations.add(formulaAndLvl.getLevelAnnotation());
		}
	}
	
	public FormulasAndLevelAnnotations(ArrayList<Term> edgeFormulas, ArrayList<LevelAnnotations> levelAnnotations) {
		assert(edgeFormulas.size() == levelAnnotations.size());
		this.edgeFormulas = edgeFormulas;
		this. levelAnnotations = levelAnnotations;
	}
	
	public ArrayList<Term> getEdgeFormulas() {
		return edgeFormulas;
	}
	
	public ArrayList<LevelAnnotations> getLevelAnnotations() {
		return levelAnnotations;
	}
	
	public int size() {
		assert(edgeFormulas.size() == levelAnnotations.size());
		return edgeFormulas.size();
	}
	
	public ArrayList<FormulaAndLevelAnnotation> getFormulasAndLevelAnnotations() {
		ArrayList<FormulaAndLevelAnnotation> result = new ArrayList<>();
		for (int i = 0; i < edgeFormulas.size(); i++) {
			result.add(new FormulaAndLevelAnnotation(edgeFormulas.get(i), levelAnnotations.get(i)));
		}
		return result;
	}
	
	public FormulaAndLevelAnnotation getFormulaAndLevel(int index) {
		return new FormulaAndLevelAnnotation(edgeFormulas.get(index), levelAnnotations.get(index));
	}
	
	@Override
	public String toString() {
		return this.getFormulasAndLevelAnnotations().toString();
	}
	
}
