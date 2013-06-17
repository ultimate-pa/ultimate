package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.generalizers;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.TreeIC3;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Clause;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Cube;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulaAndLevelAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Literal;

/** Generalization g of ~cube such that implyingTerm -> g' is valid.<br/>
 * Here, we iterate backwards over the literals of ~cube and drop them if ~cube would still be implied.<br/>
 * NOTE: given cube object may not be modified! */
public class DropLiteralsGeneralizer implements Generalizer {

	@Override
	public Set<Clause> generalization(Script script, Cube cube, FormulaAndLevelAnnotation clauseSetAndLvl, FormulaAndLevelAnnotation edgeFormulaAndLvl) {
		Clause originalClause = cube.negateToClause();
		Set<Literal> literalSet = originalClause.getLiterals();
		
		Term implyingTerm = script.term("and", clauseSetAndLvl.getFormula(), edgeFormulaAndLvl.getFormula());
		TreeIC3.logger().debug("Generalization started with implying term");
		TreeIC3.logger().debug(implyingTerm);
		TreeIC3.logger().debug("and clause");
		TreeIC3.logger().debug(originalClause);
		
		Clause clause = originalClause;
		List<Literal> literalList = new ArrayList<Literal>(literalSet);
		boolean didReduce = false;
		
		for (int i = literalList.size()-1; i >= 0; i--) {
			// It is senseless to leave out literals if we only have one literal left!
			if (i == 0 && literalList.size() == 1)
				break;
			Literal tryRemove = literalList.remove(i);
			TreeIC3.logger().debug("Generalization: Trying to leave out "+tryRemove+" ...");
			Clause reducedClause = new Clause(new HashSet<Literal>(literalList));
			Clause reducedClausePrimed = reducedClause.toOut(script, edgeFormulaAndLvl.getLevelAnnotation());
			// TODO: This might be a major slowdown here: We always calculate toOut!
			Term toCheck = script.term("=>", implyingTerm, reducedClausePrimed.toTerm(script));
			LBool result = TreeIC3.checkSat(script, script.term("not", toCheck));
			if (result == LBool.UNSAT) {
				TreeIC3.logger().debug("... worked, because "+toCheck+" was still valid.");
				clause = reducedClause;
				didReduce = true;
			} else {
				TreeIC3.logger().debug("... failed, because "+toCheck+" doesn't hold anymore.");
				literalList.add(i, tryRemove);
			}
		}
		
		if (didReduce)
			TreeIC3.logger().debug("Generalization: Reduced from "+originalClause+" to "+clause+".");
		else
			TreeIC3.logger().debug("Generalization: Could not reduce.");
		HashSet<Clause> resultSet = new HashSet<Clause>();
		resultSet.add(clause);
		return resultSet;
	}
}
