package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;

/** immutable */
public class Cube extends LiteralSet {
	private final static String operator = "and";
	
	public Cube() {
		super(operator);
	}
	
	public Cube(Set<Literal> literals) {
		super(operator, literals);
	}
	
	public Cube(Literal literal) {
		super(operator, literal);
	}
	
	public static String getUsedOperator() {
		return operator;
	}
	
	public Clause negateToClause() {
		return new Clause(negate());
	}
	
	public Cube toOut(Script script, LevelAnnotations preceedingEdgeLvl) {
		return new Cube(toOutSet(script, preceedingEdgeLvl));
	}
	
	public static FormulaAndLevelAnnotation buildDisjunction(Script script, Set<Cube> cubeSet) {
		return buildCompound(script, cubeSet, "or");
	}
	
	public static Set<Cube> extractCubeSetFromDNF(FormulaAndLevelAnnotation formulaAndLvl) {
		Set<Set<Literal>> literalSets = extractSetOfLiteralSets(formulaAndLvl, operator, "or");
		HashSet<Cube> result = new HashSet<Cube>();
		for (Set<Literal> literalSet : literalSets) {
			result.add(new Cube(literalSet));
		}
		return result;
	}
	
	public static Cube extractCube(FormulaAndLevelAnnotation formulaAndLvl) {
		return new Cube(extractLiteralSet(formulaAndLvl, operator));
	}
}
