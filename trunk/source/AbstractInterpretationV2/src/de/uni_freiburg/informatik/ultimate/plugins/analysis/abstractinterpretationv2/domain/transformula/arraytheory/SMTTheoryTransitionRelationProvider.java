package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Dnf;

public class SMTTheoryTransitionRelationProvider {

	private ManagedScript mMgdScript;
	private IUltimateServiceProvider mServices;
	
	public SMTTheoryTransitionRelationProvider(IUltimateServiceProvider services, ManagedScript mgdScript) {
		mServices = services;
		mMgdScript = mgdScript;
	}

	public Set<TransFormula> getTransitionRelationDNF(IcfgEdge edge) {
		final UnmodifiableTransFormula tf = edge.getTransformula();
		final Term formulaInDNF = new Dnf(mMgdScript, mServices).transform(tf.getFormula());
		
		final Term[] disjuncts = SmtUtils.getDisjuncts(formulaInDNF);
		
		final Set<TransFormula> result = new HashSet<>();
		for (Term disjunct : disjuncts) {

			final Term[] conjuncts = SmtUtils.getConjuncts(disjunct);
			final List<Term> filteredConjuncts = Arrays.stream(conjuncts, 0, conjuncts.length)
					.filter(t -> isTheoryLiteral(t)).collect(Collectors.toList());
			final Term filteredDisjunct = SmtUtils.and(mMgdScript.getScript(), filteredConjuncts);

			result.add(buildNewDisjunctTf(filteredDisjunct, tf));
		}
		
		return result;
	}
	
	private boolean isTheoryLiteral(Term t) {
		assert "Bool".equals(t.getSort().getName());
		if (SmtUtils.isFunctionApplication(t, "distinct")
				|| SmtUtils.isFunctionApplication(t, "=")
				|| (SmtUtils.isFunctionApplication(t, "not") 
						&& SmtUtils.isFunctionApplication(((ApplicationTerm) t).getParameters()[0], "="))
				) {
			return true;
		}
		return false;
	}

	private TransFormula buildNewDisjunctTf(Term disjunct, TransFormula originalTf) {
		final Map<IProgramVar, TermVariable> inVars = originalTf.getInVars();
		final Map<IProgramVar, TermVariable> outVars = originalTf.getOutVars();
		final Set<IProgramConst> nonTheoryConsts = originalTf.getNonTheoryConsts();
		final Collection<TermVariable> branchEncoders = Collections.emptySet();
		final boolean emptyAuxVars = originalTf.getAuxVars().isEmpty();
		
		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(inVars, outVars, nonTheoryConsts.isEmpty(), 
				nonTheoryConsts, branchEncoders.isEmpty(), branchEncoders, emptyAuxVars);
		tfBuilder.setFormula(disjunct);
		tfBuilder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		
		final UnmodifiableTransFormula disjunctTf = tfBuilder.finishConstruction(mMgdScript);
		// assert disjunctTf is conjunctive  TODO
		return disjunctTf;
	}
}
