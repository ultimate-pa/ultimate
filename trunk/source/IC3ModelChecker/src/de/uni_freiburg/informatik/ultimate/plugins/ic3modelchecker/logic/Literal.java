package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/** immutable */
public class Literal {
	private boolean positive;
	private FormulaAndLevelAnnotation atomarFormulaAndLvl;
	
	public Literal(boolean positive, FormulaAndLevelAnnotation atomarFormulaAndLvl) {
		this.positive = positive;
		this.atomarFormulaAndLvl = atomarFormulaAndLvl;
	}
	
	public FormulaAndLevelAnnotation getAtomarFormulaAndLvl() {
		return this.atomarFormulaAndLvl;
	}
	/** Not to mismatch with getAtomarFormulaAndLvl which doesn't mind the pre-sign. */
	public FormulaAndLevelAnnotation getFormulaAndLvl(Script script) {
		return new FormulaAndLevelAnnotation(this.toTerm(script), atomarFormulaAndLvl.getLevelAnnotation());
	}
	
	public LevelAnnotations getLvl() {
		return atomarFormulaAndLvl.getLevelAnnotation();
	}
	
	public boolean isPositive() {
		return this.positive;
	}
	
	public Term toTerm(Script script) {
		if (this.positive)
			return this.atomarFormulaAndLvl.getFormula();
		else
			return script.term("not", this.atomarFormulaAndLvl.getFormula());
	}
	
	public String toString() {
		if (!positive) {
			return "(not "+atomarFormulaAndLvl.toString()+")";
		} else {
			return atomarFormulaAndLvl.toString();
		}
	}
	
	
	public static Literal extractLiteral(FormulaAndLevelAnnotation formulaAndLvl) {
		Term formula = formulaAndLvl.getFormula();
		LevelAnnotations levelAnnotation = formulaAndLvl.getLevelAnnotation();
		if (formula instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) formula;
			Term[] params = appTerm.getParameters();
			String functionName = appTerm.getFunction().getName();
			if (functionName.equals("not")) {
				if (params[0] instanceof ApplicationTerm) {
					String contentFunctionName = ((ApplicationTerm)params[0]).getFunction().getName();
					if (contentFunctionName.equals("and") || contentFunctionName.equals("or"))
						throw new RuntimeException("extractLiteral(): Strange function symbol detected!");
				}
				return new Literal(false, new FormulaAndLevelAnnotation(params[0], levelAnnotation));
			} else if (functionName.equals("and") || functionName.equals("or")) {
				throw new RuntimeException("extractLiteral(): Strange function symbol detected!");
			} else {
				return new Literal(true, formulaAndLvl);
			}
		} else {
			return new Literal(true, formulaAndLvl);
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime
				* result
				+ ((atomarFormulaAndLvl == null) ? 0 : atomarFormulaAndLvl
						.hashCode());
		result = prime * result + (positive ? 1231 : 1237);
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
		Literal other = (Literal) obj;
		if (atomarFormulaAndLvl == null) {
			if (other.atomarFormulaAndLvl != null)
				return false;
		} else if (!atomarFormulaAndLvl.equals(other.atomarFormulaAndLvl))
			return false;
		if (positive != other.positive)
			return false;
		return true;
	}
}
