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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractPostOperator;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality.ArrayEqualityExtractor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class VPPostOperator implements IAbstractPostOperator<VPState, CodeBlock, IProgramVar> {

	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;

	private final VPDomain mDomain;
	private final VPStateFactory mStateFactory;
	private final VPDomainPreanalysis mPreAnalysis;
	private final VPTransFormulaStateBuilderPreparer mTfPreparer;
	private final VpTfStateFactory mTfStateFactory;

	public VPPostOperator(final ManagedScript script, final IUltimateServiceProvider services, final VPDomain domain) {
		mScript = script;
		mServices = services;
		mDomain = domain;
		mStateFactory = mDomain.getVpStateFactory();
		mPreAnalysis = mDomain.getPreAnalysis();
		mTfPreparer = mDomain.getTfPreparer();
		mTfStateFactory = mDomain.getTfStateFactory();
	}

	@Override
	public List<VPState> apply(final VPState oldState, final CodeBlock transition) {

		final UnmodifiableTransFormula tf = transition.getTransitionFormula();
		if (tf.getOutVars().isEmpty()) {
			return Collections.singletonList(oldState);
		}

		if (oldState.isBottom()) {
			return Collections.singletonList(oldState);
		}

		VPTfState tfPreState = mTfStateFactory.createTfState(oldState, tf);


		final Term nnfTerm = new Nnf(mScript, mServices, QuantifierHandling.CRASH).transform(tf.getFormula());
		mDomain.getLogger().debug("Original term: " + tf.getFormula());
		mDomain.getLogger().debug("Nnf term:      " + nnfTerm);


		final Map<TermVariable, IProgramVar> tvToPvMap = VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf);

		final Set<VPTfState> resultTfStates = handleTransition(tfPreState, nnfTerm, tf, false);

		mDomain.getLogger().debug("states after transition " + transition + ": " + resultTfStates);

		Set<VPState> resultStates = mStateFactory.convertToStates(resultTfStates, tf);

		assert VPDomainHelpers.containsNoNullElement(resultStates);
		assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
		assert resultStates.size() < 50 : "TODO: merge internally";
		return new ArrayList<>(resultStates);
	}

	private Set<VPTfState> handleTransition(
			final VPTfState tfPreState, 
			final Term term, 
			final TransFormula tf,
			boolean negated) {

		if (term instanceof ApplicationTerm) {

			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final String applicationName = appTerm.getFunction().getName();

			if (applicationName == "and") {
				assert !negated : "we transformed to nnf before, right?";

			final List<Set<VPTfState>> andList = new ArrayList<>();
			for (final Term conjunct : appTerm.getParameters()) {
				andList.add(handleTransition(tfPreState, conjunct, tf, false));
			}

			Set<VPTfState> resultStates =
					mTfStateFactory.conjoinAll(andList);
			assert !resultStates.isEmpty();
//			assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
			return resultStates;
			} else if (applicationName == "or") {
				assert !negated : "we transformed to nnf before, right?";

				final Set<VPTfState> orList = new HashSet<VPTfState>();
				for (final Term t : appTerm.getParameters()) {
					orList.addAll(handleTransition(tfPreState, term, tf, false));
				}
				assert !orList.isEmpty();
//				assert VPDomainHelpers.allStatesHaveSameVariables(orList);
				return orList;
			} else if (applicationName == "=") {
				/*
				 * case "ArrayEquality"
				 */
				{
					final List<ArrayEquality> aeqs =
							new ArrayEqualityExtractor(new Term[] { appTerm }).getArrayEqualities();
					if (!aeqs.isEmpty()) {
						assert aeqs.size() == 1 : "?";
						if (!mDomain.getPreAnalysis().isArrayTracked(
								aeqs.get(0).getLhs(), tf.getInVars(), tf.getOutVars())
								|| !mDomain.getPreAnalysis().isArrayTracked(
										aeqs.get(0).getRhs(), tf.getInVars(), tf.getOutVars())) {
							return Collections.singleton(tfPreState);
						}

						// we have an array equality (i.e. something like (= a b) where a,b are arrays)
						Set<VPTfState> result = handleArrayEqualityTransition(
										tfPreState,
										tf,
										aeqs.get(0),
										negated);
						assert !result.isEmpty();
//						assert VPDomainHelpers.allStatesHaveSameVariables(result);
						return result;
					}
				}

				/*
				 * case "ArrayUpdate"
				 */
				{
					final List<ArrayUpdate> aus = new ArrayUpdateExtractor(false, false, appTerm).getArrayUpdates();
					if (!aus.isEmpty()) {
						assert aus.size() == 1 : "?";
						if (!mDomain.getPreAnalysis().isArrayTracked(
								aus.get(0).getNewArray(), tf.getInVars(), tf.getOutVars())
								|| !mDomain.getPreAnalysis().isArrayTracked(
										aus.get(0).getOldArray(), tf.getInVars(), tf.getOutVars())){
							return Collections.singleton(tfPreState);
						}

						// we have an array update
						Set<VPTfState> result = handleArrayUpdateTransition(
										tfPreState, 
										tf,
										aus.get(0),
										negated);
						assert !result.isEmpty();
//						assert VPDomainHelpers.allStatesHaveSameVariables(result);
						return result;
					}
				}

				/*
				 * case "two terms we track are equated"
				 */
				Set<VPTfState> resultStates = handleBasicEquality(
						tfPreState, tf, appTerm, negated);
//				assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
				return resultStates;
			} else if (applicationName == "not") {
				assert !negated : "we transformed to nnf before, right?";
			Set<VPTfState> result = handleTransition(
					tfPreState, appTerm.getParameters()[0], tf, !negated);
			assert !result.isEmpty();
//			assert VPDomainHelpers.allStatesHaveSameVariables(result);
			return result;
			} else if (applicationName == "distinct") {

				mScript.lock(this);
				final Term equality =
						mScript.term(this, "=", appTerm.getParameters()[0], appTerm.getParameters()[1]);
				mScript.unlock(this);

				Set<VPTfState> result = handleTransition(tfPreState, equality, tf, !negated);
				assert !result.isEmpty();
//				assert VPDomainHelpers.allStatesHaveSameVariables(result);
				return result;
			} else if (applicationName == "true") {
				if (!negated) {
					return Collections.singleton(tfPreState);
				} else {
					VPTfState result = mTfStateFactory.getBottomState(tfPreState.getVariables());
					return Collections.singleton(result);
				}
			} else if (applicationName == "false") {
				if (!negated) {
					VPTfState result = mTfStateFactory.getBottomState(tfPreState.getVariables());
					return Collections.singleton(result);
				} else {
					return Collections.singleton(tfPreState);
				}
			} else {
				/*
				 * we don't handle this function 
				 * --> what does this mean?
				 * guesses:
				 *  - always safe: return top state
				 *  - finer: if no outVars occur, then the prestate can be returned safely, right?
				 */
//				VPState result = mStateFactory.havocVariables(assignedVars, prestate);
				assert false : "TODO: implement";
				return Collections.singleton(mTfStateFactory.createEmptyStateBuilder(tf).build());
			}

		} else if (term instanceof QuantifiedFormula) {
			// return handleTransition(preState, ((QuantifiedFormula) term).getSubformula(), tvToPvMap);
			assert false : "we currently cannot deal with quantifiers";
		return null;
		} else if (term instanceof AnnotatedTerm) {
			Set<VPTfState> result = handleTransition(
					tfPreState, 
					((AnnotatedTerm) term).getSubterm(), 
					tf, 
					negated);
			assert !result.isEmpty();
			return result;
		}

		assert false : "missed a case?";
		return Collections.singleton(tfPreState);
	}

	private Set<VPTfState> handleBasicEquality(VPTfState tfPreState, TransFormula tf, ApplicationTerm appTerm,
			boolean negated) {
		Term param1 = appTerm.getParameters()[0];
		Term param2 = appTerm.getParameters()[1];

		if (tfPreState.tracksTerm(param1) 
				&& tfPreState.tracksTerm(param2)) {
			if (!negated) {
				Set<VPTfState> result = mTfStateFactory.addEquality(param1, param2, tfPreState);
				return result;
			} else {
				Set<VPTfState> result = mTfStateFactory.addDisequality(param1, param2, tfPreState);
				return result;
			}
		} else {
			// we don't track at least one of the params 
			return Collections.singleton(tfPreState);
		}
	}

		private Set<VPTfState> handleArrayUpdateTransition(VPTfState tfPreState, TransFormula tf, ArrayUpdate arrayUpdate,
			boolean negated) {
			
			
//			/*
//			 * special case: the newArray is the outVar, the oldArray the inVar of the same IProgramVar
//			 *  i.e., we have something like a[i] := x;
//			 * (question: can we generalize this some more?, what if one of them is an auxVar?)
//			 * (another case might be: newArray == oldArray on TermVariable level, then this could be replaced
//			 *  by a equality with select.. --> maybe does not happen.., but may be covered anyway)
//			 */
//			if (VPDomainHelpers.getProgramVar(arrayUpdate.getNewArray(), tf) 
//					== VPDomainHelpers.getProgramVar(arrayUpdate.getOldArray(), tf)) {
//				if (!negated) {
//					// technical note: by our convention the EqNode of a store is that of the corresponding select
//					Set<VPTfState> result = mTfStateFactory.addEquality(arrayUpdate.getNewArray(), 
//							arrayUpdate.getMultiDimensionalStore().getStoreTerm(),  
//							tfPreState);
//					return result;
//				} else {
//					
//				}
//			}
			
			
			
			if (!negated) {
				Set<VPTfState> result = mTfStateFactory.handleArrayEqualityWithException(
						arrayUpdate.getNewArray(), 
						arrayUpdate.getOldArray(),
						arrayUpdate.getMultiDimensionalStore().getStoreTerm(),
						arrayUpdate.getMultiDimensionalStore().getValue(), 
						tfPreState);
						return result;
			} else {
				// we have a disequality between arrays
				// --> "it could be anywhere"..
				return Collections.singleton(tfPreState);
			}
	}

		private Set<VPTfState> handleArrayEqualityTransition(VPTfState tfPreState, TransFormula tf, ArrayEquality arrayEquality,
			boolean negated) {
			
			if (!negated) {
				Set<VPTfState> result = mTfStateFactory.handleArrayEquality(
						arrayEquality.getLhs(),
						arrayEquality.getRhs(),
						tfPreState);
				return result;
			} else {
				// we have a disequality between arrays
				// --> "it could be anywhere"..
				return Collections.singleton(tfPreState);
			}
		}

//		private Set<EqNode> collectDisEqualitiesForNodeInState(EqNode nodeForOtherSide, VPState prestate) {
//			return prestate.getUnequalNodes(nodeForOtherSide);
//		}
//
//		private Set<EqNode> collectEqualitiesForNodeInState(EqNode nodeForOtherSide, VPState prestate) {
//			Set<EqNode> result = new HashSet<>();
//			EqGraphNode graphNode = prestate.getEqNodeToEqGraphNodeMap().get(nodeForOtherSide);
//			result.add(graphNode.getRepresentative().eqNode);
//			for (EqGraphNode rr : graphNode.getReverseRepresentative()) {
//				result.add(rr.eqNode);
//			}
//			return result;
//		}

		@Override
		public List<VPState> apply(final VPState stateBeforeLeaving, final VPState stateAfterLeaving,
				final CodeBlock transition) {

			if (transition instanceof Call) {
				List<VPState> result = applyContextSwitch(stateBeforeLeaving, stateAfterLeaving, ((Call) transition).getLocalVarsAssignment());
				assert VPDomainHelpers.containsNoNullElement(result);
				assert VPDomainHelpers.allStatesHaveSameVariables(result);
				return result;
			} else if (transition instanceof Return) {
				List<VPState> result = applyContextSwitch(stateBeforeLeaving, stateAfterLeaving, ((Return) transition).getAssignmentOfReturn());
				assert VPDomainHelpers.containsNoNullElement(result);
				assert VPDomainHelpers.allStatesHaveSameVariables(result);
				return result;
			} else if (transition instanceof Summary) {
				List<VPState> result = applyContextSwitch(stateBeforeLeaving, stateAfterLeaving, ((Summary) transition).getTransformula());
				assert VPDomainHelpers.containsNoNullElement(result);
				assert VPDomainHelpers.allStatesHaveSameVariables(result);
				return result;
			} else {
				assert false : "unexpected..";
			}

			assert false : "forgot a case?";
			return null;
		}

		private List<VPState> applyContextSwitch(VPState stateBeforeLeaving, VPState stateAfterLeaving, TransFormula variableAssignment) {
			/*
			 * Plan:
			 *   say x1.. xn are the parameters in the call  (sth like call x:= foo(x1, ... xn) )
			 *  - from stateBeforeLeaving extract all relations (equality/disequality) of x1 .. xn to global variables
			 *  (- background: stateAfterLeaving already has the relations that the globals have between each other patched into)
			 *  - the resulting state(s) is obtained by adding all the extracted (dis)equalities to stateAfterLeaving according
			 *    to the matching of parameters 
			 */

			if (stateAfterLeaving.isBottom()) {
				return Collections.singletonList(stateAfterLeaving);
			}

			//		Set<VPState> resultStates = new HashSet<>();
			VPState copy = mDomain.getVpStateFactory().copy(stateAfterLeaving).build();
			//        resultStates.add(copy);

			VPState resultState = copy;

			Set<ApplicationTerm> equations = 
					new ApplicationTermFinder("=", true)
					.findMatchingSubterms(
							variableAssignment.getFormula());
			for (ApplicationTerm eq : equations) {
				assert eq.getParameters().length == 2;
				/*
				 * Convention:
				 * say we have a call
				 *  call x := f(x1, .., xn)
				 * and a procedure declaration
				 *  procedure f(p1 ... pn)
				 * Then x1...xn are called "call parameters"
				 *  and p1...pn are called "function parameters".
				 */
				Term callParam = eq.getParameters()[0];
				Term funcParam = eq.getParameters()[1];

				Set<Pair<EqNode, EqNode>> equalitiesWithGlobals = 
						extractEqualitiesWithGlobals(callParam, funcParam, stateBeforeLeaving, variableAssignment, mDomain);
				for (Pair<EqNode, EqNode> pair : equalitiesWithGlobals) {
					//				resultStates.addAll(
					//						mDomain.getVpStateFactory().addEquality(
					//								pair.getFirst(), pair.getSecond(), resultStates));

					// TODO: fallback, think through
					Set<VPState> newStates = VPFactoryHelpers.addEquality(
							new VPNodeIdentifier(pair.getFirst()), 
							new VPNodeIdentifier(pair.getSecond()), 
							resultState, 
							mDomain.getVpStateFactory());
					resultState = VPFactoryHelpers.disjoinAll(newStates, mDomain.getVpStateFactory());
				}
				Set<Pair<EqNode, EqNode>> disequalitiesWithGlobals = 
						extractDisequalitiesWithGlobals(callParam, funcParam, stateBeforeLeaving, variableAssignment, mDomain);
				for (Pair<EqNode, EqNode> pair : disequalitiesWithGlobals) {
					//				resultStates.addAll(
					//						mDomain.getVpStateFactory().addDisEquality(
					//								pair.getFirst(), pair.getSecond(), resultStates));
					// TODO: fallback, think through
					Set<VPState> newStates = VPFactoryHelpers.addDisEquality(
							new VPNodeIdentifier(pair.getFirst()), 
							new VPNodeIdentifier(pair.getSecond()), 
							resultState, 
							mDomain.getVpStateFactory());
					resultState = VPFactoryHelpers.disjoinAll(newStates, mDomain.getVpStateFactory());
				}

			}

			//		assert VPDomainHelpers.containsNoNullElement(resultStates);
			//		return new ArrayList<>(resultStates);
			return Collections.singletonList(resultState);
		}

		private Set<Pair<EqNode, EqNode>> extractDisequalitiesWithGlobals(
				Term callParam, 
				Term funcParam, 
				VPState stateBeforeLeaving, 
				TransFormula varAssignment,
				VPDomain domain) {

			return extractDisequalitiesWithProperty(
					callParam, funcParam, stateBeforeLeaving, varAssignment, domain, 
					node -> node.isGlobal());
		}


		public static Set<Pair<EqNode, EqNode>> extractDisequalitiesWithProperty(
				Term callParam, 
				Term funcParam, 
				VPState stateBeforeLeaving, 
				TransFormula varAssignment,
				VPDomain domain,
				Predicate<EqNode> property) {
			Map<TermVariable, IProgramVar> tvToPvMap = 
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(varAssignment);

			EqNode callParamNode = domain.getPreAnalysis().getEqNode(callParam, tvToPvMap);
			EqNode funcParamNode = domain.getPreAnalysis().getEqNode(funcParam, tvToPvMap);

			//TODO: do this more efficiently if necessary..
			Set<EqNode> unequalGlobals = 
					stateBeforeLeaving.getUnequalNodes(callParamNode).stream()
					.filter(property)
					.collect(Collectors.toSet());


			Set<Pair<EqNode, EqNode>> result = new HashSet<>();
			for (EqNode unequalGlobal : unequalGlobals) {
				result.add(new Pair<>(funcParamNode, unequalGlobal));
			}

			return result;
		}


		private Set<Pair<EqNode, EqNode>> extractEqualitiesWithGlobals(
				Term callParam, 
				Term funcParam, 
				VPState stateBeforeLeaving, 
				TransFormula varAssignment,
				VPDomain domain) {
			return extractEqualitiesWithProperty(
					callParam, funcParam, stateBeforeLeaving, varAssignment, domain, 
					node -> node.isGlobal());
		}

		/**
		 * 
		 * @param callParam the Term in the stateBeforeLeaving, i.e., we are looking for globals that this term is equal with
		 * @param funcParam the Term in the stateAfterLeaving, i.e., our resulting pair will equate this term with some global variables
		 * @param stateBeforeLeaving
		 * @param call 
		 * @return
		 */
		public static Set<Pair<EqNode, EqNode>> extractEqualitiesWithProperty(
				Term callParam, 
				Term funcParam, 
				VPState stateBeforeLeaving, 
				TransFormula varAssignment,
				VPDomain domain,
				Predicate<EqNode> property) {
			Map<TermVariable, IProgramVar> tvToPvMap = 
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(varAssignment);

			EqNode callParamNode = domain.getPreAnalysis().getEqNode(callParam, tvToPvMap);
			EqNode funcParamNode = domain.getPreAnalysis().getEqNode(funcParam, tvToPvMap);

			//TODO: do this more efficiently if necessary..
			Set<EqNode> equivalentGlobals = 
					stateBeforeLeaving.getEquivalentEqNodes(callParamNode).stream()
					.filter(property)
					.collect(Collectors.toSet());

			Set<Pair<EqNode, EqNode>> result = new HashSet<>();
			for (EqNode equivalentGlobal : equivalentGlobals) {
				result.add(new Pair<>(funcParamNode, equivalentGlobal));
			}

			return result;
		}

	}
