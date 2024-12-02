package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

public interface IAssertOrder<L extends IAction> {
	List<Set<Integer>> partitionTrace(final NestedWord<L> trace, final List<Object> controlConfigurationSequence);
}
