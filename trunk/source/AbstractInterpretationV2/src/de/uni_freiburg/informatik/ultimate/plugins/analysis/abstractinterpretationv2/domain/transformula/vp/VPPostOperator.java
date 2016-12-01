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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
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
			return Collections.singletonList(mDomain.getVpStateFactory().getBottomState());
		}
		
		final Term nnfTerm = new Nnf(mScript, mServices, QuantifierHandling.CRASH)
				.transform(tf.getFormula());
		
		mDomain.getLogger().debug("Original term: " + tf.getFormula());
		mDomain.getLogger().debug("Nnf term:      " + nnfTerm);
	
		final Term term = nnfTerm;
		
		VPState preparedState = mDomain.getVpStateFactory().havocVariables(tf.getAssignedVars(), oldstate);
		
		Map<TermVariable, IProgramVar> tvToPvMap = VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf);
		
		final List<VPState> resultStates = handleTransition(preparedState, term, tvToPvMap, false);
		
		mDomain.getLogger().debug("states after transition " + transition + ": " + resultStates);
		
		return resultStates;
	}
	
	private List<VPState> handleTransition(final VPState preState, final Term term, Map<TermVariable, IProgramVar> tvToPvMap, boolean negated) {
	
		if (term instanceof ApplicationTerm) {
			
			ApplicationTerm appTerm = (ApplicationTerm)term;
			String applicationName = appTerm.getFunction().getName();
			
			if (applicationName == "and") {
				assert !negated : "we transformed to nnf before, right?";
				
				List<List<VPState>> andList = new ArrayList<>();
				for (final Term t : appTerm.getParameters()) {
					andList.add(handleTransition(preState, t, tvToPvMap, false));
				}
				
				assert andList.size() > 1;
				
				List<VPState> result = new ArrayList<>();
				List<VPState> state = new ArrayList<>();
				state.addAll(andList.get(0));
				for (int i = 1; i < andList.size(); i++) {
					for (int j = 0; j < state.size(); j++) {
						for (int k = 0; k < andList.get(i).size(); k++) {
							result.add(mDomain.getVpStateFactory().conjoin(state.get(j), andList.get(i).get(k)));
						}
					}
					state.clear();
					state.addAll(result);
					if (!(i == andList.size() - 1)) {
						result.clear();
					}
				}
				return result;
			} else if (applicationName == "or") {
				assert !negated : "we transformed to nnf before, right?";
				
				List<VPState> orList = new ArrayList<>();
				for (final Term t : appTerm.getParameters()) {
					orList.addAll(handleTransition(preState, t, tvToPvMap, false));
				}
				return orList;
			} else if (applicationName == "=") {
				/*
				 * case "ArrayEquality"
				 */
				ArrayEquality aeq;
				try {
					 aeq = new ArrayEquality(appTerm);
				} catch (Exception ex) {
					aeq = null;
				}
				
				if (aeq != null) {
					// we have an array equality (i.e. something like (= a b) where a,b are arrays)
					Term array1Term = aeq.getLhs();
					Term array2Term = aeq.getRhs();
					IProgramVarOrConst array1 = mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(array1Term, tvToPvMap);
					IProgramVarOrConst array2 = mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(array2Term, tvToPvMap);
					VPState resultState = mDomain.getVpStateFactory().arrayEquality(array1, array2, preState);
					return Collections.singletonList(resultState);
				}
				
				/*
				 * case "ArrayUpdate"
				 */
				ArrayUpdate au;
				try {
					au = new ArrayUpdate(appTerm, negated, false);
				} catch (Exception ex) {
					au = null;
				} 
				
				if (au != null) {
					// we have an array update
					MultiDimensionalStore mdStore = au.getMultiDimensionalStore();
					TermVariable newArrayTv = au.getNewArray();
					Term oldArrayTerm = au.getOldArray();
					ArrayIndex arrayIndex = au.getIndex();
					Term value = au.getValue();
					
					IProgramVarOrConst newArrayId = mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(newArrayTv, tvToPvMap);
					IProgramVarOrConst oldArrayId = mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(newArrayTv, tvToPvMap);
					
					if (newArrayId.equals(oldArrayId)) {
						assert newArrayId == oldArrayId : "right?..";
						/*
						 * we essentially have something of the form 
						 * a[i_1, ..,i_n] := v;
						 * in terms of Boogie
						 *  --> we only havoc the EqNode belonging to a[i_1, ..,i_n] and add an equality to v
						 */
						
						EqNode arrayAtIndexNode = mDomain.getPreAnalysis().getEqNode(mdStore.getStoreTerm(), tvToPvMap);
						EqNode valueNode = mDomain.getPreAnalysis().getEqNode(value, tvToPvMap);

						VPState resultState = mDomain.getVpStateFactory().havoc(
								arrayAtIndexNode, preState);
						resultState = mDomain.getVpStateFactory().addEquality(
								arrayAtIndexNode, 
								valueNode, 
								resultState);
						return Collections.singletonList(resultState);
					} else {
						/*
						 * we have something of the form 
						 * b := a[(i_1, ..,i_n) := v]
						 * in terms of Boogie
						 * --> 
						 */
						assert false : "does this occur?";
						return null;
					}
				}
				
				/*
				 * case "two terms we track are equated"
				 */
				EqNode node1 = mDomain.getPreAnalysis().getEqNode(appTerm.getParameters()[0], tvToPvMap);
				EqNode node2 = mDomain.getPreAnalysis().getEqNode(appTerm.getParameters()[1], tvToPvMap);
							
				if (node1 != null && node2 != null) {
					VPState resultState = mDomain.getVpStateFactory().addEquality(
							node1, 
							node2, 
							preState);
					return Collections.singletonList(resultState);
				}
				
				/*
				 * case "otherwise"
				 */
				return Collections.singletonList(preState);
			} else if (applicationName == "not") {
				assert !negated : "we transformed to nnf before, right?";
				return handleTransition(preState, appTerm.getParameters()[0], tvToPvMap, true);
			} else if (applicationName == "distinct") {
				
				Term equality = mScript.getScript().term("=", appTerm.getParameters()[0], appTerm.getParameters()[1]);
				boolean newNegated = !negated;
				
				handleTransition(preState, equality, tvToPvMap, newNegated);
			}
			
			
		} else if (term instanceof QuantifiedFormula) {
//			return handleTransition(preState, ((QuantifiedFormula) term).getSubformula(), tvToPvMap);
			assert false : "we currently cannot deal with quantifiers";
			return null;
		} else if (term instanceof AnnotatedTerm) {
			return handleTransition(preState, ((AnnotatedTerm) term).getSubterm(), tvToPvMap, negated);
		}
		/*
		 * no part of the TransFormula influences the state --> return a copy
		 */

		VPState resultState = mDomain.getVpStateFactory().copy(preState);
		return Collections.singletonList(resultState);
	}
	
	
	@Override
	public List<VPState> apply(final VPState stateBeforeLeaving, final VPState stateAfterLeaving,
			final CodeBlock transition) {
		VPState conjoined = mDomain.getVpStateFactory().conjoin(stateBeforeLeaving, stateAfterLeaving);
		
		return apply(conjoined, transition);
	}

}
