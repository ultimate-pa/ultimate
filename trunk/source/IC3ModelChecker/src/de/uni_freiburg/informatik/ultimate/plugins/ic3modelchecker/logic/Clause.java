package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;

/** immutable */
public class Clause extends LiteralSet {
	private final static String operator = "or";
	
	public Clause() {
		super(operator);
	}
	
	public Clause(Set<Literal> literals) {
		super(operator, literals);
	}
	
	public Clause(Literal literal) {
		super(operator, literal);
	}
	
	public static String getUsedOperator() {
		return operator;
	}
	
	public Cube negateToCube() {
		return new Cube(negate());
	}
	
	public Clause toOut(Script script, LevelAnnotations preceedingEdgeLvl) {
		return new Clause(toOutSet(script, preceedingEdgeLvl));
	}
	
	public static FormulaAndLevelAnnotation buildConjunction(Script script, Set<Clause> clauseSet) {
		return buildCompound(script, clauseSet, "and");
	}
	
	public static Set<Clause> extractClauseSetFromCNF(FormulaAndLevelAnnotation formulaAndLvl) {
		Set<Set<Literal>> literalSets = extractSetOfLiteralSets(formulaAndLvl, operator, "and");
		HashSet<Clause> result = new HashSet<Clause>();
		for (Set<Literal> literalSet : literalSets) {
			result.add(new Clause(literalSet));
		}
		return result;
	}
	
	public static Clause extractClause(FormulaAndLevelAnnotation formulaAndLvl) {
		return new Clause(extractLiteralSet(formulaAndLvl, operator));
	}
}
