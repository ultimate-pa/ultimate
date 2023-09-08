package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class EnabledProceduresAlwaysEnabled<L extends IIcfgTransition<?>, IPredicate> implements IEnabledProcedures<L, IPredicate> {

	@Override
	public ImmutableSet<String> getEnabledProcedures(IPredicate state, L letter, Set<L> outgoing, Script script) {
		Set<String> annotations = new HashSet<>();
		for (L edge : outgoing) {
			if (!(edge instanceof IIcfgJoinTransitionThreadOther)) {
				annotations.add(edge.getSucceedingProcedure());
			}	
		}
		if (letter instanceof IIcfgForkTransitionThreadOther) {
			annotations.remove(letter.getSucceedingProcedure());
		}

		annotations.remove(letter.getPrecedingProcedure());
		Set<String> preAnnotations = ((SleepPredicate<String>) state).getSleepSet();
		if (!preAnnotations.isEmpty()) {
			annotations.retainAll(preAnnotations);
		}
		return ImmutableSet.of(annotations);
	}

}
