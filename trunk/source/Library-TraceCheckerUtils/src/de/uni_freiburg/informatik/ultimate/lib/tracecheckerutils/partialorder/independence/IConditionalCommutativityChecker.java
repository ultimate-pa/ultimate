package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;

public interface IConditionalCommutativityChecker<L extends IIcfgTransition<?>> {

	Boolean checkConditionalCommutativity();
}
