package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.HelperMethods;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.SubstitutionManager;

/** immutable */
public abstract class LiteralSet {
	private Set<Literal> literals;
	private String usedOperator;
	
	protected LiteralSet(String operator) {
		checkOperator(operator);
		this.usedOperator = operator;
		this.literals = new HashSet<Literal>();
	}
	
	protected LiteralSet(String operator, Set<Literal> literals) {
		checkOperator(operator);
		this.usedOperator = operator;
		this.literals = literals;
	}
	
	protected LiteralSet(String operator, Literal literal) {
		checkOperator(operator);
		this.usedOperator = operator;
		this.literals = new HashSet<Literal>();
		this.literals.add(literal);
	}
	
	
	
	public Set<Literal> getLiterals() {
		return literals;
	}
	
	
	
	public int countLiterals() {
		return literals.size();
	}

	
	
	public boolean isEmpty() {
		return literals.isEmpty();
	}
	
	
	
	public Term toTerm(Script script) {
		return toFormulaAndLvl(script).getFormula();
	}
	
	
	
	protected static FormulaAndLevelAnnotation buildCompound(Script script, Set<? extends LiteralSet> set,
														String composingOuterOperator) {
		checkOperator(composingOuterOperator);
		if (set.isEmpty())
			return new FormulaAndLevelAnnotation(script.term(getNeutralElement(composingOuterOperator)),
												new LevelAnnotations(script));
		
		Iterator<? extends LiteralSet> iterator = set.iterator();
		if (set.size() == 1)
			return iterator.next().toFormulaAndLvl(script);
		ArrayList<Term> content = new ArrayList<Term>();
		List<LevelAnnotations> levelAnnotationList = new ArrayList<LevelAnnotations>();
		while (iterator.hasNext()) {
			FormulaAndLevelAnnotation formulaAndLvl = iterator.next().toFormulaAndLvl(script);
			content.add(formulaAndLvl.getFormula());
			levelAnnotationList.add(formulaAndLvl.getLevelAnnotation());			
		}
		Term[] content2 = content.toArray(new Term[content.size()]);
		Term resultFormula = script.term(composingOuterOperator, content2);
		LevelAnnotations mergedLevelAnnotations = LevelAnnotations.getMerged(levelAnnotationList, resultFormula);
		return new FormulaAndLevelAnnotation(resultFormula, mergedLevelAnnotations);
	}
	
	
	
	public FormulaAndLevelAnnotation toFormulaAndLvl(Script script) {
		if (this.isEmpty()) {
			return new FormulaAndLevelAnnotation(script.term(getNeutralElement()), new LevelAnnotations(script));
		}
		Iterator<Literal> iterator = literals.iterator();
		if (literals.size() == 1)
			return iterator.next().getFormulaAndLvl(script);
		ArrayList<Term> content = new ArrayList<Term>();
		ArrayList<LevelAnnotations> levelAnnotationList = new ArrayList<LevelAnnotations>();
		while (iterator.hasNext()) {
			Literal nextLiteral = iterator.next();
			content.add(nextLiteral.toTerm(script));
			levelAnnotationList.add(nextLiteral.getLvl());
		}
		Term[] content2 = content.toArray(new Term[content.size()]);
		Term concatenatedTerm = script.term(usedOperator, content2);
		LevelAnnotations mergedLevelAnnotations = LevelAnnotations.getMerged(levelAnnotationList, concatenatedTerm);
		return new FormulaAndLevelAnnotation(concatenatedTerm, mergedLevelAnnotations);
	}
	
	
	
	/** Does shifting / priming to all variables that are modified by preceedingEdgeLvl
	 * (= that are in preceedingEdgeLvl.outVars). */
	protected Set<Literal> toOutSet(Script script, LevelAnnotations preceedingEdgeLvl) {
		Set<Literal> outLiterals = new HashSet<Literal>();
		HashMap<BoogieVar, Integer> shiftLevelPerVariable = new HashMap<BoogieVar, Integer>();
		HelperMethods.determineShiftLevelsFromEdge(shiftLevelPerVariable, preceedingEdgeLvl, 1);
		for (Literal literal : literals) {
			FormulaAndLevelAnnotation literalTermAndLvl = literal.getAtomarFormulaAndLvl();
			FormulaAndLevelAnnotation newLiteralTermAndLvl = SubstitutionManager.substituteSpecificInToOut(script,
																			literalTermAndLvl, shiftLevelPerVariable, false);
			outLiterals.add(new Literal(literal.isPositive(), newLiteralTermAndLvl));
		}
		return outLiterals;
	}
	
	
	
	public String toString() {
		StringBuilder builder = new StringBuilder();
		Iterator<Literal> iterator = literals.iterator();
		builder.append("{");
		while (iterator.hasNext()) {
			builder.append(iterator.next().toString());
			if (iterator.hasNext())
				builder.append(", ");
		}
		builder.append("}");
		return builder.toString();
	}
	
	
	
	protected static String getOppositeOperator(String operator) {
		if (operator.equals("and"))
			return "or";
		else if (operator.equals("or"))
			return "and";
		else
			throw new RuntimeException("getOppositeOperator() only supports and / or !");
	}
	
	
	
	protected String getNeutralElement() {
		return getNeutralElement(usedOperator);
	}
	protected static String getNeutralElement(String operator) {
		if (operator.equals("and"))
			return "true";
		else if (operator.equals("or"))
			return "false";
		else
			throw new RuntimeException("Could not determine neutral element!");
	}
	
	
	protected String getOppositeNeutralElement() {
		return getOppositeNeutralElement(usedOperator);
	}
	protected static String getOppositeNeutralElement(String operator) {
		if (operator.equals("or"))
			return "true";
		else if (operator.equals("and"))
			return "false";
		else
			throw new RuntimeException("Could not determine opposite neutral element!");		
	}
	
	
	
	protected Set<Literal> negate() {
		Set<Literal> resultLiterals = new HashSet<Literal>();
		for (Literal literal : literals) {
			Literal negatedLiteral = new Literal(!literal.isPositive(), literal.getAtomarFormulaAndLvl());
			resultLiterals.add(negatedLiteral);
		}
		return resultLiterals;
	}
	
	
	
	private static void checkOperator(String operator) {
		if (!operator.equals("and") && !operator.equals("or"))
			throw new RuntimeException("Only and / or are supported!");
	}
	
	
	
	protected static Set<Literal> extractLiteralSet(FormulaAndLevelAnnotation formulaAndLvl, String operator) {
		checkOperator(operator);
		Set<Literal> literals = new HashSet<Literal>();
		Term formula = formulaAndLvl.getFormula();
		LevelAnnotations levelAnnotation = formulaAndLvl.getLevelAnnotation();
		if (formula instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) formula;
			Term[] params = appTerm.getParameters();
			String functionName = appTerm.getFunction().getName();
			if (functionName.equals(operator)) {
				for (Term param : params) {
					Literal literal = Literal.extractLiteral(new FormulaAndLevelAnnotation(param, levelAnnotation));
					literals.add(literal);
				}
				return literals;
			} else {
				Literal literal = Literal.extractLiteral(formulaAndLvl);
				literals.add(literal);
				return literals;
			}
		} else {
			Literal literal = Literal.extractLiteral(formulaAndLvl);
			literals.add(literal);
			return literals;
		}
	}
	
	
	
	public static Set<Set<Literal>> extractSetOfLiteralSets(FormulaAndLevelAnnotation formulaAndLvl,
															String innerOperator,
															String composingOuterOperator) {
		checkOperator(composingOuterOperator);
		Set<Set<Literal>> literalSets = new HashSet<Set<Literal>>();
		Term formula = formulaAndLvl.getFormula();
		LevelAnnotations lvlAnnotation = formulaAndLvl.getLevelAnnotation();
		if (formula instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) formula;
			Term[] params = appTerm.getParameters();
			String functionName = appTerm.getFunction().getName();
			if (functionName.equals(composingOuterOperator)) {
				for (Term param : params) {
					Set<Literal> literalSet = extractLiteralSet(new FormulaAndLevelAnnotation(param, lvlAnnotation),
																innerOperator);
					literalSets.add(literalSet);
				}
				return literalSets;
			} else {
				Set<Literal> literalSet = extractLiteralSet(formulaAndLvl, innerOperator);
				literalSets.add(literalSet);
				return literalSets;
			}
		} else {
			Set<Literal> literalSet = extractLiteralSet(formulaAndLvl, innerOperator);
			literalSets.add(literalSet);
			return literalSets;
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((literals == null) ? 0 : literals.hashCode());
		result = prime * result
				+ ((usedOperator == null) ? 0 : usedOperator.hashCode());
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
		LiteralSet other = (LiteralSet) obj;
		if (literals == null) {
			if (other.literals != null)
				return false;
		} else if (!literals.equals(other.literals))
			return false;
		if (usedOperator == null) {
			if (other.usedOperator != null)
				return false;
		} else if (!usedOperator.equals(other.usedOperator))
			return false;
		return true;
	}
}
