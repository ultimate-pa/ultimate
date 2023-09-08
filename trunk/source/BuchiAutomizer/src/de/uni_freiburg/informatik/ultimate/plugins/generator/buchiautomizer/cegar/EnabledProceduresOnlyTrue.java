package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.HashSet;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class EnabledProceduresOnlyTrue<L extends IIcfgTransition<?>, IPredicate> implements IEnabledProcedures<L, IPredicate> {

	@Override
	public ImmutableSet<String> getEnabledProcedures(IPredicate state, L letter, Set<L> outgoing, Script script, IIcfg<?> icfg) {
		Set<String> annotations = new HashSet<>();
		for (L edge : outgoing) {
			UnmodifiableTransFormula transFormula = edge.getTransformula();
			Term formula = transFormula.getFormula();
			Set<TermVariable> existsVariables = new HashSet<>();
			for(Entry<IProgramVar, TermVariable> entry : transFormula.getOutVars().entrySet()) {
					existsVariables.add(entry.getValue());
			}
			if (!existsVariables.isEmpty()) {
				formula = script.quantifier(Script.EXISTS, existsVariables.toArray(new TermVariable[existsVariables.size()]), formula, null);
			}
			formula = SmtUtils.not(script, formula);
			if (SmtUtils.checkSatTerm(script, formula).equals(LBool.UNSAT)) {
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
