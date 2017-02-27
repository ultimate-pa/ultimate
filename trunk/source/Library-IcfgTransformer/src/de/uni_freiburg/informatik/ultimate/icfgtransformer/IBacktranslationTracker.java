package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;

@FunctionalInterface
public interface IBacktranslationTracker {
	void rememberRelation(final IIcfgTransition<?> oldTransition, final IIcfgTransition<?> newTransition);
}