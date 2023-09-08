package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class EnabledProceduresWeakFairness<L extends IIcfgTransition<?>, IPredicate> implements IEnabledProcedures<L, IPredicate> {

	@Override
	public ImmutableSet<String> getEnabledProcedures(IPredicate state, L letter, Set<L> outgoing, Script script, IIcfg<?> icfg) {
		Set<String> annotations = new HashSet<>();
		//edge is enabled if (not (-> A B)), thus if (and A (not B))is unsatisfiable
		for (L edge : outgoing) {
			UnmodifiableTransFormula transFormula = edge.getTransformula();
			Term formula = transFormula.getFormula();
			
			//substitute the variables in B to match the names of A
			Map<Term, Term> substitutionMapping = new HashMap<>();
			for(Entry<IProgramVar, TermVariable> entry : transFormula.getInVars().entrySet()) {
				substitutionMapping.put(entry.getValue(), entry.getKey().getTermVariable());
			}
			formula = PureSubstitution.apply(script, substitutionMapping, formula);
			
			//add an existential quantifier before B, quantifying over all OutVars, then assert (not B)
			Set<TermVariable> existsVariables = new HashSet<>();
			for(Entry<IProgramVar, TermVariable> entry : transFormula.getOutVars().entrySet()) {
					existsVariables.add(entry.getValue());
			}
			if (!existsVariables.isEmpty()) {
				formula = script.quantifier(Script.EXISTS, existsVariables.toArray(new TermVariable[existsVariables.size()]), formula, null);
			}
			
			formula = SmtUtils.not(script, formula);
			
			//if A != true, then assert A
			Term stateFormula = ((SleepPredicate<String>) state).getFormula();
			if (!stateFormula.toString().equals("don't care")) {
				formula = SmtUtils.and(script, stateFormula, formula);
				//Script.assertTerm(stateFormula);
			}
				
			//if unsatisfiable (or fork/join), then the edge is considered as enabled
			if(//letter instanceof IIcfgForkTransitionThreadOther || letter instanceof IIcfgJoinTransitionThreadOther ||
					Util.checkSat(script, formula).equals(LBool.UNSAT)) {
				annotations.add(edge.getSucceedingProcedure());
			}
			//Script.resetAssertions();
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
