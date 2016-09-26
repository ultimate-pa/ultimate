/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class VPPostOperator implements IAbstractPostOperator<VPState, CodeBlock, IProgramVar> {

	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;

	// private Set<EqGraphNode> mEqGraphNodeSet;
	// private Map<Term, EqNode> mTermToEqNodeMap;
	// private Map<EqNode, EqGraphNode> mEqNodeToEqGraphNodeMap;

	public VPPostOperator(ManagedScript script, IUltimateServiceProvider services) {
		mScript = script;
		mServices = services;
	}

	@Override
	public List<VPState> apply(final VPState oldstate, final CodeBlock transition) {

		final UnmodifiableTransFormula tf = transition.getTransitionFormula();
		if (tf.getOutVars().isEmpty()) {
			return Collections.singletonList(oldstate);
		}

		VPState preparedState = prepareState(oldstate, transition.getTransitionFormula().getAssignedVars());
		Term nnfTerm = new Nnf(mScript, mServices, QuantifierHandling.CRASH)
				.transform(transition.getTransitionFormula().getFormula());
		System.out.println("Original term: " + transition.getTransitionFormula().getFormula());
		System.out.println("Nnf term:      " + nnfTerm);

		
		
		
		
		
		return Collections.singletonList(
				new VPState(oldstate.getEqGraphNodeSet(), 
						oldstate.getTermToBaseNodeMap(),
						oldstate.getTermToFnNodeMap(),
						oldstate.getEqNodeToEqGraphNodeMap(), 
						oldstate.getmEqualityMap(), 
						oldstate.getmDisEqualityMap()));
	}

	/**
	 * This is a pre-step before deriving a new @VPState with @CodeBlock
	 * (transition) in order to handle assignment and assume in the same way. In
	 * this method, the variables that are about to be assigned will be havoc
	 * first. Then the graph will be change and return a new @VPState with the
	 * new graph.
	 * 
	 * @param oldState
	 * @param assignmentVars
	 * @return
	 */
	private VPState prepareState(VPState oldState, Set<IProgramVar> assignmentVars) {

		VPState preparedState = oldState.copy();
		havoc(preparedState, assignmentVars);

		return oldState;
	}

	private void havoc(VPState state, Set<IProgramVar> assignmentVars) {

		Map<Term, EqBaseNode> termToBaseNodeMap = state.getTermToBaseNodeMap();
		Map<Term, Set<EqFunctionNode>> termToFnNodeMap = state.getTermToFnNodeMap();
		Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap = state.getEqNodeToEqGraphNodeMap();

		TermVariable tv;
		
		for (IProgramVar var : assignmentVars) {
			
			tv = var.getTermVariable();
			
			if (termToBaseNodeMap.containsKey(tv)) {
				if (eqNodeToEqGraphNodeMap.containsKey(termToBaseNodeMap.get(tv))) {
					eqNodeToEqGraphNodeMap.get(termToBaseNodeMap.get(tv)).setNodeToInitial();
				}
			}
			if (termToFnNodeMap.containsKey(tv)) {
				for (EqFunctionNode fnNode : termToFnNodeMap.get(tv)) {
					if (eqNodeToEqGraphNodeMap.containsKey(fnNode)) {
						eqNodeToEqGraphNodeMap.get(fnNode).setNodeToInitial();
					}
				}
			}
		}
	}

	@Override
	public List<VPState> apply(final VPState stateBeforeLeaving, final VPState stateAfterLeaving,
			final CodeBlock transition) {
		// TODO Auto-generated method stub
		return null;
	}

}
