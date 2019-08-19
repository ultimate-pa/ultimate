/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.DnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class SMTTheoryTransitionRelationProvider {

	private ManagedScript mMgdScript;
	private IUltimateServiceProvider mServices;
	
	public SMTTheoryTransitionRelationProvider(IUltimateServiceProvider services, ManagedScript mgdScript) {
		mServices = services;
		mMgdScript = mgdScript;
	}

	public Set<TransFormula> getTransitionRelationDNF(IcfgEdge edge) {
		final UnmodifiableTransFormula tf = edge.getTransformula();
		
		if (tf.isInfeasible() == Infeasibility.INFEASIBLE) {
			mMgdScript.lock(this);
			final Term falseTerm = mMgdScript.term(this, "false");
			mMgdScript.unlock(this);
			return Collections.singleton(buildNewDisjunctTf(falseTerm, tf));
		}
		
		final Term formulaInDNF = new DnfTransformer(mMgdScript, mServices).transform(tf.getFormula());
		
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
