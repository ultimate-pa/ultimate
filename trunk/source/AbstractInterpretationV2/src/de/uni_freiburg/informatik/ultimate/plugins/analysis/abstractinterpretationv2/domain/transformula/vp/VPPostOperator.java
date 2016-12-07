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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality.ArrayEqualityExtractor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf.QuantifierHandling;
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

		final Term nnfTerm = new Nnf(mScript, mServices, QuantifierHandling.CRASH).transform(tf.getFormula());

		mDomain.getLogger().debug("Original term: " + tf.getFormula());
		mDomain.getLogger().debug("Nnf term:      " + nnfTerm);
		
		final Term term = nnfTerm;

		final VPState havocedState = mDomain.getVpStateFactory().havocVariables(tf.getAssignedVars(), oldstate);

		final Map<TermVariable, IProgramVar> tvToPvMap = VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf);

		final List<VPState> resultStates = handleTransition(havocedState, oldstate, term, tvToPvMap, 
				tf.getAssignedVars(), tf.getInVars(), tf.getOutVars(), false);

		mDomain.getLogger().debug("states after transition " + transition + ": " + resultStates);

		return resultStates;
	}

	private List<VPState> handleTransition(
			final VPState preStateWithHavoccedAssignedVars, 
			VPState oldstate, 
			final Term term,
			final Map<TermVariable, IProgramVar> tvToPvMap, 
			Set<IProgramVar> assignedVars,
			Map<IProgramVar, TermVariable> inVars, 
			Map<IProgramVar, TermVariable> outVars, 
			final boolean negated) {
		
		if (term instanceof ApplicationTerm) {
			
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final String applicationName = appTerm.getFunction().getName();

			if (applicationName == "and") {
				assert !negated : "we transformed to nnf before, right?";

				final List<List<VPState>> andList = new ArrayList<>();
				for (final Term t : appTerm.getParameters()) {
					andList.add(handleTransition(preStateWithHavoccedAssignedVars, oldstate, t, tvToPvMap, assignedVars, inVars, outVars, false));
				}

				assert andList.size() > 1;

				final List<VPState> result = new ArrayList<>();
				final List<VPState> state = new ArrayList<>();
				state.addAll(andList.get(0));
				for (int i = 1; i < andList.size(); i++) {
					for (int j = 0; j < state.size(); j++) {
						for (int k = 0; k < andList.get(i).size(); k++) {
							result.addAll(mDomain.getVpStateFactory().conjoin(state.get(j), andList.get(i).get(k)));
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

				final List<VPState> orList = new ArrayList<>();
				for (final Term t : appTerm.getParameters()) {
					orList.addAll(handleTransition(preStateWithHavoccedAssignedVars, oldstate, t, tvToPvMap, assignedVars, inVars, outVars, false));
				}
				return orList;
			} else if (applicationName == "=") {
				/*
				 * case "ArrayEquality"
				 */
				final List<ArrayEquality> aeqs =
						new ArrayEqualityExtractor(new Term[] { appTerm }).getArrayEqualities();
				if (!aeqs.isEmpty()) {
					assert aeqs.size() == 1 : "?";
					// we have an array equality (i.e. something like (= a b) where a,b are arrays)
					return new ArrayList<>(handleArrayEqualityTransition(preStateWithHavoccedAssignedVars, oldstate, tvToPvMap, inVars, outVars, negated, aeqs.get(0)));
				}

				/*
				 * case "ArrayUpdate"
				 */
				final List<ArrayUpdate> aus = new ArrayUpdateExtractor(false, false, appTerm).getArrayUpdates();
				
				if (!aus.isEmpty()) {
					assert aus.size() == 1 : "?";
					// we have an array update
					return new ArrayList<>(handleArrayUpdateTransition(preStateWithHavoccedAssignedVars, oldstate, tvToPvMap, inVars, outVars, negated, aus.get(0)));
				}

				/*
				 * case "two terms we track are equated"
				 */
				
			
				EqNode node1 = mDomain.getPreAnalysis().getEqNode(appTerm.getParameters()[0], tvToPvMap);
				EqNode node2 = mDomain.getPreAnalysis().getEqNode(appTerm.getParameters()[1], tvToPvMap);
	
				// is one of the terms an assignedVar -and- does that var occur in the other term?
				// --> in that case, replace the occurence with something from the old state that is equal 
				//     or return the havocced state, if no such node exists
				
				// 
				
				/*
				 * TODO: right now, this can only infer a stronger post state if
				 *  say we have the assignment x := a[x];
				 *  - there is a node, say y, that is equivalent to x in oldstate  
				 *  - we track the substituted node, i.e., a[y], in the right version, it can be select or store.
				 *  we might increase the probability by detecting this in the preanalysis and creating nodes accordingly..
				 */
				Term param1 = appTerm.getParameters()[0];
				Term param2 = appTerm.getParameters()[1];
				
				IProgramVar p1Pv = tvToPvMap.get(param1);
				IProgramVar p2Pv = tvToPvMap.get(param2);
			
				if (assignedVars.contains(p1Pv) && inVars.containsKey(p1Pv)) {
					// param1 is assigned, and used on the other side of the equation
					// --> replace the occurrences on the other side by something equal in the oldstate if possible
					
					final EqNode otherOccurrenceEqNode = mDomain.getPreAnalysis().getEqNode(inVars.get(p1Pv), tvToPvMap);
					
					Set<EqNode> equivalentNodes = oldstate.getEquivalentEqNodes(otherOccurrenceEqNode);
					
					assert equivalentNodes.size() > 0;
					if (equivalentNodes.size() == 1) {
						assert equivalentNodes.iterator().next() == otherOccurrenceEqNode;
						return Collections.singletonList(preStateWithHavoccedAssignedVars);
					} 
					Iterator<EqNode> eqNodesIt = equivalentNodes.iterator();
					EqNode equivalentNode = null;

					node2 = null;
					while (node2 == null && eqNodesIt.hasNext()) {
						equivalentNode = eqNodesIt.next();
						if (equivalentNode == otherOccurrenceEqNode) {
							continue;
						}
						Term equivalentTerm = equivalentNode.getTerm(mScript.getScript());

						Map<Term, Term> subs = new HashMap<>();
						subs.put(inVars.get(p1Pv), equivalentTerm);
						Term otherParamEquivalentTermSubstituted = new Substitution(mScript, subs).transform(param2);

						// technical note: here that tvToPvMap does not need to be augmented, even though the equivalentTerm
						// may contain variables that the map does not know --> but these are already "normalized" 
						node2 = mDomain.getPreAnalysis().getEqNode(otherParamEquivalentTermSubstituted, tvToPvMap);
					}

					if (node2 == null) { // probably unnecessary, to make this a special case -- but might be better understandable..
						return Collections.singletonList(preStateWithHavoccedAssignedVars);
					}
				} else if (assignedVars.contains(p2Pv)) {
					assert assignedVars.contains(p1Pv);
					assert false : "TODO: implement"; // do we have assignments where the assigned var ends up on the right of the equality??
					node1 = null;
					return Collections.singletonList(preStateWithHavoccedAssignedVars);
				}

				if (node1 != null && node2 != null) {
					if (!negated) {
						final Set<VPState> resultStates =
								mDomain.getVpStateFactory().addEquality(node1, node2, preStateWithHavoccedAssignedVars);
						return new ArrayList<>(resultStates);
					} else {
						final Set<VPState> resultStates =
								mDomain.getVpStateFactory().addDisEquality(node1, node2, preStateWithHavoccedAssignedVars);
						return new ArrayList<>(resultStates);
					}
				}

				/*
				 * case "otherwise" --> we leave the state unchanged
				 */
				return Collections.singletonList(preStateWithHavoccedAssignedVars);
			} else if (applicationName == "not") {
				assert !negated : "we transformed to nnf before, right?";
				return handleTransition(preStateWithHavoccedAssignedVars, oldstate, appTerm.getParameters()[0], tvToPvMap, assignedVars, inVars, outVars, !negated);
			} else if (applicationName == "distinct") {
				
				mScript.lock(this);
				final Term equality =
						mScript.term(this, "=", appTerm.getParameters()[0], appTerm.getParameters()[1]);
				mScript.unlock(this);

				return handleTransition(preStateWithHavoccedAssignedVars, oldstate, equality, tvToPvMap, assignedVars, inVars, outVars, !negated);
			}
			
		} else if (term instanceof QuantifiedFormula) {
			// return handleTransition(preState, ((QuantifiedFormula) term).getSubformula(), tvToPvMap);
			assert false : "we currently cannot deal with quantifiers";
			return null;
		} else if (term instanceof AnnotatedTerm) {
			return handleTransition(preStateWithHavoccedAssignedVars, oldstate, ((AnnotatedTerm) term).getSubterm(), tvToPvMap, assignedVars, inVars, outVars, negated);
		}
		/*
		 * no part of the TransFormula influences the state --> return a copy
		 */

		VPState resultState = preStateWithHavoccedAssignedVars;//mDomain.getVpStateFactory().copy(preState).build();
		return Collections.singletonList(resultState);
	}
	
//	private boolean isInVarAndAssignedVar(Term term, Map<TermVariable, IProgramVar> tvToPvMap) {
//		
//		return false;
//	}
//
//	private boolean isInVarAndAssignedVar(Term term, 
//			Map<IProgramVar, TermVariable> inVars,
//			Map<IProgramVar, TermVariable> outVars) {
//		// TODO Auto-generated method stub
//		return false;
//	}

	private Set<VPState> handleArrayEqualityTransition(
			final VPState preState,
			final VPState oldstate, 
			final Map<TermVariable, IProgramVar> tvToPvMap, 
			final Map<IProgramVar, TermVariable> inVars, 
			final Map<IProgramVar, TermVariable> outVars, 
			final boolean negated, 
			final ArrayEquality aeq) {
		final Term array1Term = aeq.getLhs();
		final Term array2Term = aeq.getRhs();
		final IProgramVarOrConst array1 =
				mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(array1Term, tvToPvMap);
		final IProgramVarOrConst array2 =
				mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(array2Term, tvToPvMap);
		if (!negated) {
			final Set<VPState> resultStates = mDomain.getVpStateFactory().arrayEquality(array1, array2, preState);
			return resultStates;
		} else {
			/*
			 * something of the form a != b where a and b are arrays
			 *  --> we cannot derive anything from this because we only track a finite number
			 *     of positions in each (infinite) array
			 */
			return Collections.singleton(preState);
		}
	}
	
	private Set<VPState> handleArrayUpdateTransition(
			final VPState preState,
			final VPState oldstate, 
			final Map<TermVariable, IProgramVar> tvToPvMap, 
			final Map<IProgramVar, TermVariable> inVars, 
			final Map<IProgramVar, TermVariable> outVars, 
			final boolean negated, final ArrayUpdate au) {
		final MultiDimensionalStore mdStore = au.getMultiDimensionalStore();
		final TermVariable newArrayTv = au.getNewArray();
		final Term oldArrayTerm = au.getOldArray();
		final Term value = au.getValue();

		final IProgramVarOrConst newArrayId =
				mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(newArrayTv, tvToPvMap);
		final IProgramVarOrConst oldArrayId =
				mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(oldArrayTerm, tvToPvMap);

		if (newArrayId.equals(oldArrayId)) {
			assert newArrayId == oldArrayId : "right?..";
			/*
			 * we essentially have something of the form a[i_1, ..,i_n] := v; in terms of Boogie --> we only havoc the
			 * EqNode belonging to a[i_1, ..,i_n] and add an equality to v
			 */

			// TODO: strictly speaking we have to check here, that newArrayId is an outVar, oldArrayId an inVar

			final EqNode arrayAtIndexNode = mDomain.getPreAnalysis().getEqNode(mdStore.getStoreTerm(), tvToPvMap);
			final EqNode valueNode = mDomain.getPreAnalysis().getEqNode(value, tvToPvMap);

			if (!negated) {
				final VPState resultState = mDomain.getVpStateFactory().havoc(arrayAtIndexNode, preState);
				final Set<VPState> resultStates = new HashSet<>();
				resultStates.addAll(mDomain.getVpStateFactory().addEquality(arrayAtIndexNode, valueNode, resultState));
				return resultStates;
			} else {
				assert false : "TODO";// TODO
				return null;
			}
		} else {
			/*
			 * we have something of the form b := a[(i_1, ..,i_n) := v] in terms of Boogie -->
			 */
		
			if (!negated) {
//				TODO: treat essentially like an ArrayEquality (except for that one point)
				assert false : "does this occur?";
			
			/*
			 * for all points p except (i_1, .., i_n), we add 
			 *   b[p] = a[p] to the state
			 * and we add b[i_1, ..., i_n] = v
			 */
			
				return null;
			} else {
				/*
				 * see the "negated" case in handleArrayEquality for an explanation
				 */
				return Collections.singleton(preState);
			}
		}
	}
	
	@Override
	public List<VPState> apply(final VPState stateBeforeLeaving, final VPState stateAfterLeaving,
			final CodeBlock transition) {
		// List<VPState> conjoined = mDomain.getVpStateFactory().conjoin(stateBeforeLeaving, stateAfterLeaving);

		// TODO
		
		// return apply(conjoined, transition);
		return null;
	}
	
}
