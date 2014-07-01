package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

/**
 * Represents predicate with multiple locations. 
 *
 */
public interface IMLPredicate extends IPredicate {
	
	public ProgramPoint[] getProgramPoints();

}
