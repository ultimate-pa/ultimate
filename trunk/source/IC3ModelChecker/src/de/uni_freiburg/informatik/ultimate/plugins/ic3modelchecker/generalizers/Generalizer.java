package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.generalizers;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Clause;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Cube;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulaAndLevelAnnotation;

/** Module that performs generalization of candidate cubes. */
public interface Generalizer {
	public Set<Clause> generalization(Script script, Cube cube, FormulaAndLevelAnnotation clauseSetAndLvl, FormulaAndLevelAnnotation edgeFormulaAndLvl);
}
