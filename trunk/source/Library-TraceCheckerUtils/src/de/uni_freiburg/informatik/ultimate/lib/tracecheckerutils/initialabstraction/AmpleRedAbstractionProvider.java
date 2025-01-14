package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/*
 * Analogon to PartialOrderAbstractionProvider
 * no idea what this thing is supposed to do
 * transform an initial abstraction to ?
 *
 * @param <L>: type of transition
 *
 *
 */
public class AmpleRedAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, NestedWordAutomaton<L, IPredicate>> {

	@Override
	public NestedWordAutomaton<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return null;
	}

}
