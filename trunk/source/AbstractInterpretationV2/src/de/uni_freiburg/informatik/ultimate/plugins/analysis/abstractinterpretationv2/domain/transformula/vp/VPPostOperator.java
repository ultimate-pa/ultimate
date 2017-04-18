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
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPStateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VpTfStateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class VPPostOperator<ACTION extends IIcfgTransition<IcfgLocation>>
		implements IAbstractPostOperator<VPState<ACTION>, ACTION, IProgramVarOrConst> {
	
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	
	private final VPDomain<ACTION> mDomain;
	private final VPStateFactory<ACTION> mStateFactory;
	private final VPDomainPreanalysis mPreAnalysis;
	private final VPTransFormulaStateBuilderPreparer mTfPreparer;
	private final VpTfStateFactory mTfStateFactory;
	
	public VPPostOperator(final ManagedScript script, final IUltimateServiceProvider services,
			final VPDomain<ACTION> domain) {
		mScript = script;
		mServices = services;
		mDomain = domain;
		mStateFactory = mDomain.getVpStateFactory();
		mPreAnalysis = mDomain.getPreAnalysis();
		mTfPreparer = mDomain.getTfPreparer();
		mTfStateFactory = mDomain.getTfStateFactory();
	}
	
	/**
	 * This specific implementation of apply(..) proceeds as follows
	 * <list>
	 *  <li> create a tfState that corresponds to the given transFormula and propagate all we know about its inVars from
	 *     the oldState into it
	 *  <li> apply the TransFormula to the tfState, i.e., put it into a state where we have all the knowledge about the 
	 *       outVars that we can compute from the inVar-information from the step before and the transFormula
	 *  <li> convert the resulting tfState(s) back to "normal" states, by taking all the information about the outVars,
	 *     and overwriting the information the oldState has about them -- but leaving the information about other 
	 *     variables in the oldState intact, as the TransFormula did not touch those
	 * </list>
	 */
	@Override
	public List<VPState<ACTION>> apply(final VPState<ACTION> oldState, final ACTION transition) {

		if (mPreAnalysis.isDebugMode()) {
			mPreAnalysis.getLogger().debug("VPPostOperator: apply(..) (internal transition) (begin)");
			mPreAnalysis.getBenchmark().unpause(VPSFO.applyClock);
		}
		
		final UnmodifiableTransFormula tf = IcfgUtils.getTransformula(transition);
		if (tf.getOutVars().isEmpty()) {
			if (mPreAnalysis.isDebugMode()) {
				mPreAnalysis.getBenchmark().pause(VPSFO.applyClock);
			}
			return Collections.singletonList(oldState);
		}
		
		if (oldState.isBottom()) {
			if (mPreAnalysis.isDebugMode()) {
				mPreAnalysis.getBenchmark().pause(VPSFO.applyClock);
			}
			return Collections.singletonList(oldState);
		}
		
//		final VPTfState tfPreState = mTfStateFactory.createTfState(oldState, tf);
		
		final VPTfState tfState = mTfStateFactory.createTfState(oldState, tf);
		
//		final Term nnfTerm = new Nnf(mScript, mServices, QuantifierHandling.CRASH).transform(tf.getFormula());

//		if (mPreAnalysis.isDebugMode()) {
//			mDomain.getLogger().debug("Original term: " + tf.getFormula());
//			mDomain.getLogger().debug("Nnf term:      " + nnfTerm);
//		}
		
//		final Set<VPTfState> resultTfStates = handleTransition(tfPreState, nnfTerm, tf, false);
		
		tfState.computeOutStates(mTfStateFactory);
		
//		if (mPreAnalysis.isDebugMode()) {
//			mDomain.getLogger().debug("states after transition " + transition + ": " + resultTfStates);
//		}
		
//		final Set<VPState<ACTION>> resultStates = mStateFactory.convertToStates(resultTfStates, tf.getAssignedVars(), 
//				oldState);
		final Set<VPState<ACTION>> resultStates = tfState.patchOut(mStateFactory.getTopState(oldState.getVariables()));

		if (mPreAnalysis.isDebugMode()) {
			mPreAnalysis.getLogger().debug("VPPostOperator: apply(..) (internal transition) (end)");
			mPreAnalysis.getBenchmark().pause(VPSFO.overallFromPreAnalysis);
			mPreAnalysis.getBenchmark().printResult(mPreAnalysis.getLogger());
			mPreAnalysis.getBenchmark().unpause(VPSFO.overallFromPreAnalysis);
		
			mPreAnalysis.getBenchmark().pause(VPSFO.applyClock);
		}
		assert VPDomainHelpers.containsNoNullElement(resultStates);
		assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
		assert resultStates.size() < 50 : "TODO: merge internally";
		return new ArrayList<>(resultStates);
	}
	
	@Override
	public List<VPState<ACTION>> apply(final VPState<ACTION> stateBeforeLeaving,
			final VPState<ACTION> stateAfterLeaving, final ACTION transition) {

		if (transition instanceof Call
				|| transition instanceof Return) {
			final VPTfState tfState = mTfStateFactory.createTfState(stateBeforeLeaving, transition.getTransformula());
			tfState.computeOutStates(mTfStateFactory);
			final Set<VPState<ACTION>> result = tfState.patchOut(stateAfterLeaving);

			assert VPDomainHelpers.containsNoNullElement(result);
			assert VPDomainHelpers.allStatesHaveSameVariables(result);
			return new ArrayList<>(result);
		} else if (transition instanceof Summary) {
			throw new AssertionError("TODO: implement"); //TODO
		} else {
			throw new AssertionError("unexpected: apply with two preStates on an edges that is not Call, Return, "
					+ "Summary");
		}
		
//		if (transition instanceof Call) {
//			final List<VPState<ACTION>> result = applyContextSwitch(stateBeforeLeaving, stateAfterLeaving,
//					((Call) transition).getLocalVarsAssignment());
//			assert VPDomainHelpers.containsNoNullElement(result);
//			assert VPDomainHelpers.allStatesHaveSameVariables(result);
//			return result;
//		} else if (transition instanceof Return) {
//			final List<VPState<ACTION>> result = applyContextSwitch(stateBeforeLeaving, stateAfterLeaving,
//					((Return) transition).getAssignmentOfReturn());
//			assert VPDomainHelpers.containsNoNullElement(result);
//			assert VPDomainHelpers.allStatesHaveSameVariables(result);
//			return result;
//		} else if (transition instanceof Summary) {
//			final List<VPState<ACTION>> result =
//					applyContextSwitch(stateBeforeLeaving, stateAfterLeaving, ((Summary) transition).getTransformula());
//			assert VPDomainHelpers.containsNoNullElement(result);
//			assert VPDomainHelpers.allStatesHaveSameVariables(result);
//			return result;
//		} else {
//			assert false : "unexpected..";
//		}
	}

//	/**
//	 * Patches the side conditions of the given XwithSideConditions into the given state, returns the resulting state.
//	 * 
//	 * @param tfPreState
//	 * @param lhsNodeWSc
//	 * @param rhsNodeWSc
//	 * @return
//	 */
//	private Set<VPTfState> addSideConditionsToState(final VPTfState tfPreState,
//			final INodeOrArrayWithSideCondition lhsNodeWSc, final INodeOrArrayWithSideCondition rhsNodeWSc) {
//		final VPTfStateBuilder preStateCopy = mTfStateFactory.copy(tfPreState);
//		// add side conditions
//		for (final VPDomainSymmetricPair<VPTfNodeIdentifier> de : lhsNodeWSc.getDisEqualities()) {
//			preStateCopy.addDisEquality(de);
//		}
//		for (final VPDomainSymmetricPair<VPTfNodeIdentifier> de : rhsNodeWSc.getDisEqualities()) {
//			preStateCopy.addDisEquality(de);
//		}
//
//		Set<VPTfState> resultStatesForCurrentNodePair = new HashSet<>();
//		resultStatesForCurrentNodePair.add(preStateCopy.build());
//		for (final VPDomainSymmetricPair<VPTfNodeIdentifier> eq : lhsNodeWSc.getEqualities()) {
//			resultStatesForCurrentNodePair = VPFactoryHelpers.addEquality(eq.getFirst(), eq.getSecond(),
//					resultStatesForCurrentNodePair, mTfStateFactory);
//		}
//		for (final VPDomainSymmetricPair<VPTfNodeIdentifier> eq : rhsNodeWSc.getEqualities()) {
//			resultStatesForCurrentNodePair = VPFactoryHelpers.addEquality(eq.getFirst(), eq.getSecond(),
//					resultStatesForCurrentNodePair, mTfStateFactory);
//		}
//		// TODO: filter bottom states?
//		return resultStatesForCurrentNodePair;
//	}
	
//	private List<VPState<ACTION>> applyContextSwitch(final VPState<ACTION> stateBeforeLeaving,
//			final VPState<ACTION> stateAfterLeaving, final TransFormula variableAssignment) {
//		/*
//		 * Plan: say x1.. xn are the parameters in the call (sth like call x:= foo(x1, ... xn) ) - from
//		 * stateBeforeLeaving extract all relations (equality/disequality) of x1 .. xn to global variables (-
//		 * background: stateAfterLeaving already has the relations that the globals have between each other patched
//		 * into) - the resulting state(s) is obtained by adding all the extracted (dis)equalities to stateAfterLeaving
//		 * according to the matching of parameters
//		 */
//		
//		if (stateAfterLeaving.isBottom()) {
//			return Collections.singletonList(stateAfterLeaving);
//		}
//		
//		final VPState<ACTION> copy = mDomain.getVpStateFactory().copy(stateAfterLeaving).build();
//		
//		VPState<ACTION> resultState = copy;
//		
//		final Set<ApplicationTerm> equations =
//				new ApplicationTermFinder("=", true).findMatchingSubterms(variableAssignment.getFormula());
//		for (final ApplicationTerm eq : equations) {
//			assert eq.getParameters().length == 2;
//			/*
//			 * Convention: say we have a call call x := f(x1, .., xn) and a procedure declaration procedure f(p1 ... pn)
//			 * Then x1...xn are called "call parameters" and p1...pn are called "function parameters".
//			 */
//			final Term callParam = eq.getParameters()[0];
//			final Term funcParam = eq.getParameters()[1];
//			
//			final Set<Pair<EqNode, EqNode>> equalitiesWithGlobals =
//					extractEqualitiesWithGlobals(callParam, funcParam, stateBeforeLeaving, variableAssignment, mDomain);
//			for (final Pair<EqNode, EqNode> pair : equalitiesWithGlobals) {
//				// TODO: fallback, think through
//				final Set<VPState<ACTION>> newStates = VPFactoryHelpers.addEquality(pair.getFirst(), pair.getSecond(),
//						resultState, mDomain.getVpStateFactory());
//				resultState = VPFactoryHelpers.disjoinAll(newStates, mDomain.getVpStateFactory());
//			}
//			final Set<Pair<EqNode, EqNode>> disequalitiesWithGlobals = extractDisequalitiesWithGlobals(callParam,
//					funcParam, stateBeforeLeaving, variableAssignment, mDomain);
//			for (final Pair<EqNode, EqNode> pair : disequalitiesWithGlobals) {
//				final Set<VPState<ACTION>> newStates = VPFactoryHelpers.addDisEquality(pair.getFirst(),
//						pair.getSecond(), resultState, mDomain.getVpStateFactory());
//				resultState = VPFactoryHelpers.disjoinAll(newStates, mDomain.getVpStateFactory());
//			}
//			
//		}
//		
//		return Collections.singletonList(resultState);
//	}
//	
//	private Set<Pair<EqNode, EqNode>> extractDisequalitiesWithGlobals(final Term callParam, final Term funcParam,
//			final VPState<ACTION> stateBeforeLeaving, final TransFormula varAssignment, final VPDomain<ACTION> domain) {
//		return extractDisequalitiesWithProperty(callParam, funcParam, stateBeforeLeaving, varAssignment, domain,
//				node -> node.isGlobal());
//	}
//	
//	public Set<Pair<EqNode, EqNode>> extractDisequalitiesWithProperty(final Term callParam, final Term funcParam,
//			final VPState<ACTION> stateBeforeLeaving, final TransFormula varAssignment, final VPDomain<ACTION> domain,
//			final Predicate<EqNode> property) {
//		final Map<TermVariable, IProgramVar> tvToPvMap =
//				VPDomainHelpers.computeProgramVarMappingFromTransFormula(varAssignment);
//		
//		final EqNode callParamNode = domain.getPreAnalysis().getEqNode(callParam, tvToPvMap);
//		final EqNode funcParamNode = domain.getPreAnalysis().getEqNode(funcParam, tvToPvMap);
//		
//		// TODO: do this more efficiently if necessary..
//		final Set<EqNode> unequalGlobals =
//				stateBeforeLeaving.getUnequalNodes(callParamNode).stream().filter(property).collect(Collectors.toSet());
//		
//		final Set<Pair<EqNode, EqNode>> result = new HashSet<>();
//		for (final EqNode unequalGlobal : unequalGlobals) {
//			result.add(new Pair<>(funcParamNode, unequalGlobal));
//		}
//		
//		return result;
//	}
//	
//	private Set<Pair<EqNode, EqNode>> extractEqualitiesWithGlobals(final Term callParam, final Term funcParam,
//			final VPState<ACTION> stateBeforeLeaving, final TransFormula varAssignment, final VPDomain<ACTION> domain) {
//		return extractEqualitiesWithProperty(callParam, funcParam, stateBeforeLeaving, varAssignment, domain,
//				EqNode::isGlobal);
//	}
//	
//	/**
//	 *
//	 * @param callParam
//	 *            the Term in the stateBeforeLeaving, i.e., we are looking for globals that this term is equal with
//	 * @param funcParam
//	 *            the Term in the stateAfterLeaving, i.e., our resulting pair will equate this term with some global
//	 *            variables
//	 * @param stateBeforeLeaving
//	 * @param call
//	 * @return
//	 */
//	public Set<Pair<EqNode, EqNode>> extractEqualitiesWithProperty(final Term callParam, final Term funcParam,
//			final VPState<ACTION> stateBeforeLeaving, final TransFormula varAssignment, final VPDomain<ACTION> domain,
//			final Predicate<EqNode> property) {
//		final Map<TermVariable, IProgramVar> tvToPvMap =
//				VPDomainHelpers.computeProgramVarMappingFromTransFormula(varAssignment);
//		
//		final EqNode callParamNode = domain.getPreAnalysis().getEqNode(callParam, tvToPvMap);
//		final EqNode funcParamNode = domain.getPreAnalysis().getEqNode(funcParam, tvToPvMap);
//		
//		// TODO: do this more efficiently if necessary..
//		final Set<EqNode> equivalentGlobals = stateBeforeLeaving.getEquivalentEqNodes(callParamNode).stream()
//				.filter(property).collect(Collectors.toSet());
//		
//		final Set<Pair<EqNode, EqNode>> result = new HashSet<>();
//		for (final EqNode equivalentGlobal : equivalentGlobals) {
//			result.add(new Pair<>(funcParamNode, equivalentGlobal));
//		}
//		
//		return result;
//	}

//	private Set<VPTfState> handleTransition(final VPTfState tfPreState, final Term term, final TransFormula tf,
//			final boolean negated) {
//		
//		if (term instanceof ApplicationTerm) {
//			
//			final ApplicationTerm appTerm = (ApplicationTerm) term;
//			final String functionName = appTerm.getFunction().getName();
//			
//			if ("and".equals(functionName)) {
//				assert !negated : "we transformed to nnf before, right?";
//				
//				final List<Set<VPTfState>> andList = new ArrayList<>();
//				for (final Term conjunct : appTerm.getParameters()) {
//					andList.add(handleTransition(tfPreState, conjunct, tf, false));
//				}
//				
//				final Set<VPTfState> resultStates = mTfStateFactory.conjoinAll(andList);
//				assert !resultStates.isEmpty();
//				// assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
//				return resultStates;
//			} else if ("or".equals(functionName)) {
//				assert !negated : "we transformed to nnf before, right?";
//				
//				final Set<VPTfState> orList = new HashSet<>();
//				for (final Term t : appTerm.getParameters()) {
//					orList.addAll(handleTransition(tfPreState, t, tf, false));
//				}
//				assert !orList.isEmpty();
//				// assert VPDomainHelpers.allStatesHaveSameVariables(orList);
//				return orList;
//			} else if ("=".equals(functionName)) {
//				final Set<VPTfState> result = handleEqualitySubterm(tfPreState, tf, negated, appTerm.getParameters()[0],
//						appTerm.getParameters()[1]);
//				assert !result.isEmpty();
//				return result;
//			} else if ("not".equals(functionName)) {
//				assert !negated : "we transformed to nnf before, right?";
//				final Set<VPTfState> result = handleTransition(tfPreState, appTerm.getParameters()[0], tf, !negated);
//				assert !result.isEmpty();
//				// assert VPDomainHelpers.allStatesHaveSameVariables(result);
//				return result;
//			} else if ("distinct".equals(functionName)) {
//				
//				mScript.lock(this);
//				final Term equality = mScript.term(this, "=", appTerm.getParameters()[0], appTerm.getParameters()[1]);
//				mScript.unlock(this);
//				
//				final Set<VPTfState> result = handleTransition(tfPreState, equality, tf, !negated);
//				assert !result.isEmpty();
//				// assert VPDomainHelpers.allStatesHaveSameVariables(result);
//				return result;
//			} else if ("true".equals(functionName)) {
//				if (!negated) {
//					return Collections.singleton(tfPreState);
//				}
//				final VPTfState result = mTfStateFactory.getBottomState(tfPreState.getVariables());
//				return Collections.singleton(result);
//			} else if ("false".equals(functionName)) {
//				if (!negated) {
//					final VPTfState result = mTfStateFactory.getBottomState(tfPreState.getVariables());
//					return Collections.singleton(result);
//				}
//				return Collections.singleton(tfPreState);
//			} else {
//				/*
//				 * we don't handle this function --> what does this mean? guesses: - always safe: return top state -
//				 * finer: if no outVars occur, then the prestate can be returned safely, right?
//				 */
//				return Collections.singleton(tfPreState);
//			}
//			
//		} else if (term instanceof QuantifiedFormula) {
//			throw new UnsupportedOperationException("we cannot deal with quantifiers right now");
//		} else if (term instanceof AnnotatedTerm) {
//			final Set<VPTfState> result =
//					handleTransition(tfPreState, ((AnnotatedTerm) term).getSubterm(), tf, negated);
//			assert !result.isEmpty();
//			return result;
//		}
//		
//		assert false : "missed a case?";
//		return Collections.singleton(tfPreState);
//	}
//
//	/**
//	 *
//	 * @param tfPreState
//	 * @param tf
//	 * @param negated
//	 * @param appTerm
//	 *            the subterm of the current transformula that this method should apply to the preState
//	 * @return
//	 */
//	private Set<VPTfState> handleEqualitySubterm(final VPTfState tfPreState, final TransFormula tf,
//			final boolean negated, final Term lhs, final Term rhs) {
//		if (lhs.getSort().isArraySort()) {
//			if (negated) {
//				// we have a disequality between arrays
//				// we cannot conclude anything from this as we never track all array indices
//				return Collections.singleton(tfPreState);
//			}
//			// two arrays are equated
//	
//			final VPTfStateBuilder tfStateBuilder = mTfPreparer.getVPTfStateBuilder(tf);
//			
//			final IArrayWrapper lhsWrapper = tfStateBuilder.getArrayWrapper(lhs);
//			final IArrayWrapper rhsWrapper = tfStateBuilder.getArrayWrapper(rhs);
//	
//			final Set<VPTfState> resultStates = new HashSet<>();
//			for (final ArrayWithSideCondition lhsArrayWSc : lhsWrapper.getArrayWithSideConditions(tfPreState, null)) {
//				for (final ArrayWithSideCondition rhsArrayWSc : rhsWrapper.getArrayWithSideConditions(tfPreState,
//						null)) {
//					
//					Set<VPTfState> resultStatesForCurrentNodePair =
//							addSideConditionsToState(tfPreState, lhsArrayWSc, rhsArrayWSc);
//	
//					// add equalities for all the indices we track for both arrays
//					for (final Entry<List<VPTfNodeIdentifier>, VPTfNodeIdentifier> en : lhsArrayWSc.getIndexToValue()
//							.entrySet()) {
//						if (!rhsArrayWSc.getIndexToValue().containsKey(en.getKey())) {
//							// the other array does not have a value for the current index
//							// --> do nothing
//							continue;
//						}
//	
//						final VPTfNodeIdentifier lhS = en.getValue();
//						final VPTfNodeIdentifier rhS = rhsArrayWSc.getIndexToValue().get(en.getKey());
//						
//						resultStatesForCurrentNodePair =
//								VPFactoryHelpers.addEquality(lhS, rhS, resultStatesForCurrentNodePair, mTfStateFactory);
//					}
//					
//					resultStates.addAll(resultStatesForCurrentNodePair);
//				}
//			}
//	
//			assert !resultStates.isEmpty();
//			return resultStates;
//		} else {
//			// two "normal" terms are equated
//	
//			// only used for array wrapping --> vanilla builder should suffice
//			final VPTfStateBuilder tfStateBuilder = mTfPreparer.getVPTfStateBuilder(tf); 
//	
//			final IElementWrapper lhsWrapper = tfStateBuilder.getElementWrapper(lhs);
//			final IElementWrapper rhsWrapper = tfStateBuilder.getElementWrapper(rhs);
//	
//			if (lhsWrapper == null || rhsWrapper == null) {
//				return Collections.singleton(tfPreState);
//			}
//	
//			final Set<VPTfState> resultStates = new HashSet<>();
//			//
//			for (final NodeIdWithSideCondition lhsNodeWSc : lhsWrapper.getNodeIdWithSideConditions(tfPreState)) {
//				for (final NodeIdWithSideCondition rhsNodeWSc : rhsWrapper.getNodeIdWithSideConditions(tfPreState)) {
//					Set<VPTfState> resultStatesForCurrentNodePair =
//							addSideConditionsToState(tfPreState, lhsNodeWSc, rhsNodeWSc);
//					if (lhsNodeWSc instanceof UndeterminedNodeWithSideCondition
//							|| rhsNodeWSc instanceof UndeterminedNodeWithSideCondition) {
//						// we don't have both nodes --> we cannot add a (dis)equality, but we can still add the
//						// sideconditions
//						resultStates.addAll(resultStatesForCurrentNodePair);
//						continue;
//					}
//					
//					// add (dis)equality
//					if (!negated) {
//						resultStatesForCurrentNodePair = VPFactoryHelpers.addEquality(lhsNodeWSc.getNodeId(),
//								rhsNodeWSc.getNodeId(), resultStatesForCurrentNodePair, mTfStateFactory);
//					} else {
//						resultStatesForCurrentNodePair = VPFactoryHelpers.addDisEquality(lhsNodeWSc.getNodeId(),
//								rhsNodeWSc.getNodeId(), resultStatesForCurrentNodePair, mTfStateFactory);
//						
//					}
//					resultStates.addAll(resultStatesForCurrentNodePair);
//				}
//			}
//	
//			assert !resultStates.isEmpty();
//			return resultStates;
//		}
//	}
	
}
