package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.Settings;

public class FormulaAndLevelAnnotation {
	private Term edgeFormula;
	private LevelAnnotations levelAnnotation;
	
	public FormulaAndLevelAnnotation(Term formula, LevelAnnotations levelAnnotation) {
		this.edgeFormula = formula;
		this.levelAnnotation =levelAnnotation; 
	}
	
	public Term getFormula() {
		return edgeFormula;
	}
	
	public LevelAnnotations getLevelAnnotation() {
		return levelAnnotation;
	}
	
	public String toString() {
		String result = edgeFormula.toStringDirect();
		for (Integer level : levelAnnotation.getAvailableLevels()) {
			for (TermVariable var : levelAnnotation.getLevel(level).values()) {
				result = result.replaceAll(var.getName(), Settings.levelMarker + level + Settings.levelMarker + var.getName());
			}
		}
		return result;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((edgeFormula == null) ? 0 : edgeFormula.hashCode());
		result = prime * result
				+ ((levelAnnotation == null) ? 0 : levelAnnotation.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		FormulaAndLevelAnnotation other = (FormulaAndLevelAnnotation) obj;
		if (edgeFormula == null) {
			if (other.edgeFormula != null)
				return false;
		} else if (!edgeFormula.equals(other.edgeFormula))
			return false;
		if (levelAnnotation == null) {
			if (other.levelAnnotation != null)
				return false;
		} else if (!levelAnnotation.equals(other.levelAnnotation))
			return false;
		return true;
	}
}
