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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
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
	
	private VPState preparedState;
	private final VPDomain mDomain;
	
	public VPPostOperator(final ManagedScript script, final IUltimateServiceProvider services, final VPDomain domain) {
		mScript = script;
		mServices = services;
		mDomain = domain;
	}

	@Override
	public List<VPState> apply(final VPState oldstate, final CodeBlock transition) {

		final UnmodifiableTransFormula tf = transition.getTransitionFormula();
		if (tf.getOutVars().isEmpty()) {
			return Collections.singletonList(oldstate);
		}
		
		if (oldstate instanceof VPStateBottom) {
			return Collections.singletonList(mDomain.getmBottomState());
		}
		
		preparedState = oldstate.prepareState(tf.getAssignedVars());
		final Term nnfTerm = new Nnf(mScript, mServices, QuantifierHandling.CRASH)
				.transform(transition.getTransitionFormula().getFormula());
		
		System.out.println("Original term: " + tf.getFormula());
		System.out.println("Nnf term:      " + nnfTerm);
		
		// Substitution
		final Map<Term, Term> substitionMap = new HashMap<Term, Term>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			substitionMap.put(entry.getValue(), entry.getKey().getTermVariable());
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			substitionMap.put(entry.getValue(), entry.getKey().getTermVariable());
		}
		
		final Term substitutedTerm = new Substitution(mScript, substitionMap).transform(nnfTerm);
		
		final VPState resultState = handleTransition(substitutedTerm);
		
		System.out.println(resultState.toLogString());
		
		if (resultState instanceof VPStateBottom) {
			return Collections.singletonList(mDomain.getmBottomState());
		}
		
		return Collections.singletonList(
				new VPState(resultState.getEqGraphNodeSet(), 
						resultState.getTermToBaseNodeMap(),
						resultState.getTermToFnNodeMap(),
						resultState.getEqNodeToEqGraphNodeMap(),  
						resultState.getDisEqualitySet(),
						mDomain));
	}
	
	private VPState handleTransition(final Term term) {
		
		VPState resultState = preparedState.copy();
		
		if (term instanceof ApplicationTerm) {
			
			ApplicationTerm appTerm = (ApplicationTerm)term;
			String applicationName = appTerm.getFunction().getName();
			
			if (applicationName == "and") {
				
				List<VPState> andList = new ArrayList<VPState>();
				for (final Term t : appTerm.getParameters()) {
					andList.add(handleTransition(t));
				}
				VPState state = andList.get(0);
				for (int i = 1; i < andList.size(); i++) {
					state = state.conjoin(andList.get(i));
				}
				return state;
				
			} else if (applicationName == "or") {
				
				List<VPState> orList = new ArrayList<VPState>();
				for (final Term t : appTerm.getParameters()) {
					orList.add(handleTransition(t));
				}
				VPState state = orList.get(0);
				for (int i = 1; i < orList.size(); i++) {
					state = state.disjoin(orList.get(i));	
				}
				return state;
				
			} else if (applicationName == "=") {
				
				EqNode node1 = null;
				EqNode node2 = null;
				
				if (isArray(appTerm.getParameters()[0], resultState)) {
					if (isArray(appTerm.getParameters()[1], resultState)) {
						
						resultState.arrayAssignment(appTerm.getParameters()[0], appTerm.getParameters()[1]);
						return resultState;
						
					} else {
						if (appTerm.getParameters()[1] instanceof ApplicationTerm) {
							ApplicationTerm param1 = (ApplicationTerm) appTerm.getParameters()[1];
							if (param1.getFunction().getName() == "store") {
								MultiDimensionalStore mulStore = new MultiDimensionalStore(param1);
								if (mulStore.getArray().equals(appTerm.getParameters()[0])) {
									node1 = getNodeFromTerm(param1, resultState);
									resultState.havoc(node1);
									resultState.getEqNodeToEqGraphNodeMap().get(node1).setNodeToInitial();
									node2 = getNodeFromTerm(param1.getParameters()[2], resultState);
								}
							}
						}
					}
				}
				
				if (node1 == null && node2 == null) {
					node1 = getNodeFromTerm(appTerm.getParameters()[0], resultState);
					node2 = getNodeFromTerm(appTerm.getParameters()[1], resultState);
				}
							
				if (node1 == null || node2 == null) {
					return resultState;
				}
				
				boolean isContradic = resultState.addEquality(node1, node2);
				
				if (isContradic) {
					return mDomain.getmBottomState();
				}
				
				return resultState;
				
				
			} else if (applicationName == "not") {
				
				ApplicationTerm equalTerm = (ApplicationTerm)appTerm.getParameters()[0];
				if (!(equalTerm.getFunction().getName() == "=")) {
					// TODO: check: is it correct here to return bottom?
					return mDomain.getmBottomState();
				} else {
					EqNode node1 = getNodeFromTerm(equalTerm.getParameters()[0], resultState);
					EqNode node2 = getNodeFromTerm(equalTerm.getParameters()[1], resultState);
					
					if (node1 == null || node2 == null) {
						return resultState;
					}
					
					boolean isContradic = resultState.addDisEquality(node1, node2);
					
					if (isContradic) {
						return mDomain.getmBottomState();
					}
					
					return resultState;
				}

			} else if (applicationName == "distinct") {
				
				EqNode node1 = getNodeFromTerm(appTerm.getParameters()[0], resultState);
				EqNode node2 = getNodeFromTerm(appTerm.getParameters()[1], resultState);
				
				if (node1 == null || node2 == null) {
					return mDomain.getmBottomState();
				}
				
				boolean isContradic = resultState.addDisEquality(node1, node2);
				
				if (isContradic) {
					return mDomain.getmBottomState();
				}
				
				return resultState;
			}
			
			
		} else if (term instanceof QuantifiedFormula) {
			return handleTransition(((QuantifiedFormula) term).getSubformula());
		} else if (term instanceof AnnotatedTerm) {
			return handleTransition(((AnnotatedTerm) term).getSubterm());
		}
		
		return resultState;
	}
	
	private EqNode getNodeFromTerm(final Term term, final VPState state) {
		
		final Map<Term, EqBaseNode> baseNodeMap = state.getTermToBaseNodeMap();
		final Map<Term, Set<EqFunctionNode>> fnNodeMap = state.getTermToFnNodeMap();
		
		if (term instanceof TermVariable || term instanceof ConstantTerm) {
			if (baseNodeMap.containsKey(term)) {
				return baseNodeMap.get(term);
			}
		} else {
			final Term array = ((ApplicationTerm)term).getParameters()[0];
			final Term index = ((ApplicationTerm)term).getParameters()[1];
			final EqNode indexNode = getNodeFromTerm(index, state);
			if (fnNodeMap.containsKey(array)) {
				for (final EqFunctionNode fnNode : fnNodeMap.get(array)) {
					if (fnNode.getArg().equals(indexNode)) {
						return fnNode;
					}
				}
			}
		}
		return null;
	}

	private boolean isArray(final Term term, final VPState state) {
		for (Term key : state.getTermToFnNodeMap().keySet()) {
			if (term.equals(key)) {
				return true;
			}
		}
		return false;
	}
	
	@Override
	public List<VPState> apply(final VPState stateBeforeLeaving, final VPState stateAfterLeaving,
			final CodeBlock transition) {
		// TODO Auto-generated method stub
		return null;
	}

}
