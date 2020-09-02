package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Interface to construct interpolants for a given trace with precondition and postcondition.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public interface IInterpolantProvider<LETTER> {
	IPredicate[] getInterpolants(IPredicate precondition, List<LETTER> trace, IPredicate postcondition);
}
