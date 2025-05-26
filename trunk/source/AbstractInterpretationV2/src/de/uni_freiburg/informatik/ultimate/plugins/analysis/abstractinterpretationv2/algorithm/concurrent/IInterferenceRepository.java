package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public interface IInterferenceRepository<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {

	void addInterference(Interference<STATE, ACTION, LOC> interference);

	Collection<Interference<STATE, ACTION, LOC>> getAllInterferences();

	Collection<Interference<STATE, ACTION, LOC>> getInterferencesForThread(final String threadName);

	SubsetResult isSubsetOf(IInterferenceRepository<STATE, ACTION, LOC> other);
}
