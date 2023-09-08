package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public interface IEnabledProcedures<L, P> {

	ImmutableSet<String> getEnabledProcedures(P state, L letter, Set<L> outgoing, Script script, IIcfg<?> icfg);
}
