/*
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.ArrayWithSideCondition;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IArrayWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IElementWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.INodeOrArrayWithSideCondition;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.NodeIdWithSideCondition;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.UndeterminedNodeWithSideCondition;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfArrayIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class VPTfState extends IVPStateOrTfState<VPTfNodeIdentifier, VPTfArrayIdentifier> {
	
	private final VPTfStateBuilder mBuilder;
	private final TransFormula mTransFormula;
	private final HashRelation<VPTfArrayIdentifier, VPTfNodeIdentifier> mArrayIdToFunctionNodes;
	private final Map<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> mNodeIdToEqGraphNode;
	private final Set<VPTfNodeIdentifier> mAllNodeIds;
	private final VpTfStateFactory mTfStateFactory;
	private final ManagedScript mScript;

	private final Set<IProgramVarOrConst> mInVars;
	private final Set<IProgramVarOrConst> mOutVars;
	
	public VPTfState(final TransFormula tf, final VPTfStateBuilder builder,
			final Map<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> nodeIdToEqGraphNode,
			final Set<VPTfNodeIdentifier> allNodeIds,
			final HashRelation<VPTfArrayIdentifier, VPTfNodeIdentifier> arrayIdToFunctionNodes,
			final Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> disEqs, final boolean isTop,
			final Set<IProgramVarOrConst> inVars, 
			final Set<IProgramVarOrConst> outVars, 
			VpTfStateFactory tfStateFactory) {
		super(disEqs, isTop);
		mTransFormula = tf;
		mBuilder = builder;
		mAllNodeIds = allNodeIds;
		mNodeIdToEqGraphNode = Collections.unmodifiableMap(nodeIdToEqGraphNode);
		mArrayIdToFunctionNodes = new HashRelation<>(arrayIdToFunctionNodes); // TODO is copy needed here?
		mTfStateFactory = tfStateFactory;
		
		mInVars = inVars;
		mOutVars = outVars;
		
		assert false : "TODO: obtain script somehow";
		mScript = null;
		

		assert isTopConsistent();
	}
	
	@Override
	public boolean isBottom() {
		return false;
	}
	
	@Override
	public EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>
			getEqGraphNode(final VPTfNodeIdentifier nodeIdentifier) {
		return mNodeIdToEqGraphNode.get(nodeIdentifier);
	}
	
	@Override
	public Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> getAllEqGraphNodes() {
		return new HashSet<>(mNodeIdToEqGraphNode.values());
	}
	
	@Override
	public VPTfNodeIdentifier find(final VPTfNodeIdentifier id) {
		return mNodeIdToEqGraphNode.get(id).find().mNodeIdentifier;
	}
	
	public Set<VPTfNodeIdentifier> getFunctionNodesForArray(final VPTfArrayIdentifier array) {
		return mArrayIdToFunctionNodes.getImage(array);
	}
	
	public TransFormula getTransFormula() {
		return mTransFormula;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("VPTfState\n");
		sb.append("InVars: " + getInVariables().toString() + "\n");
		sb.append("OutVars: " + getOutVariables().toString() + "\n");
		// sb.append("eqGraphNodes: " + getAllEqGraphNodes().toString() +"\n");
		sb.append("Graph:\n");
		for (final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> egn : getAllEqGraphNodes()) {
			if (egn.getRepresentative() != egn) {
				sb.append(egn.toString() + "\n");
			}
		}
		sb.append("DisEqualities:" + getDisEqualities() + "\n");
		return sb.toString();
	}
	
	public Set<IProgramVarOrConst> getInVariables() {
		return mInVars;
	}

	public Set<IProgramVarOrConst> getOutVariables() {
		return mOutVars;
	}

	public VPTfArrayIdentifier getArrayIdentifier(final Term newArray) {
		assert mBuilder.getTransFormula() == mTransFormula;
		return mBuilder.getOrConstructArrayIdentifier(newArray);
	}

	public void computeOutStates() {
		// TODO Auto-generated method stub
		
	}

	public <ACTION extends IIcfgTransition<IcfgLocation>> Set<VPState<ACTION>> patchOut(VPState<ACTION> topState) {
		// TODO Auto-generated method stub
		return null;
	}

	private Set<VPTfState> handleTransition(final Term term, final TransFormula tf,
			final boolean negated) {
		
		if (term instanceof ApplicationTerm) {
			
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final String functionName = appTerm.getFunction().getName();
			
			if ("and".equals(functionName)) {
				assert !negated : "we transformed to nnf before, right?";
				
				final List<Set<VPTfState>> andList = new ArrayList<>();
				for (final Term conjunct : appTerm.getParameters()) {
					andList.add(handleTransition(conjunct, tf, false));
				}
				
				final Set<VPTfState> resultStates = mTfStateFactory.conjoinAll(andList);
				assert !resultStates.isEmpty();
				// assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
				return resultStates;
			} else if ("or".equals(functionName)) {
				assert !negated : "we transformed to nnf before, right?";
				
				final Set<VPTfState> orList = new HashSet<>();
				for (final Term t : appTerm.getParameters()) {
					orList.addAll(handleTransition(t, tf, false));
				}
				assert !orList.isEmpty();
				// assert VPDomainHelpers.allStatesHaveSameVariables(orList);
				return orList;
			} else if ("=".equals(functionName)) {
				final Set<VPTfState> result = handleEqualitySubterm(tf, negated, appTerm.getParameters()[0],
						appTerm.getParameters()[1]);
				assert !result.isEmpty();
				return result;
			} else if ("not".equals(functionName)) {
				assert !negated : "we transformed to nnf before, right?";
				final Set<VPTfState> result = handleTransition(appTerm.getParameters()[0], tf, !negated);
				assert !result.isEmpty();
				// assert VPDomainHelpers.allStatesHaveSameVariables(result);
				return result;
			} else if ("distinct".equals(functionName)) {
				
				mScript.lock(this);
				final Term equality = mScript.term(this, "=", appTerm.getParameters()[0], appTerm.getParameters()[1]);
				mScript.unlock(this);
				
				final Set<VPTfState> result = handleTransition(equality, tf, !negated);
				assert !result.isEmpty();
				// assert VPDomainHelpers.allStatesHaveSameVariables(result);
				return result;
			} else if ("true".equals(functionName)) {
				if (!negated) {
					return Collections.singleton(this);
				}
				final VPTfState result = mTfStateFactory.getBottomState(this.getOutVariables());
				return Collections.singleton(result);
			} else if ("false".equals(functionName)) {
				if (!negated) {
					final VPTfState result = mTfStateFactory.getBottomState(this.getOutVariables());
					return Collections.singleton(result);
				}
				return Collections.singleton(this);
			} else {
				/*
				 * we don't handle this function --> what does this mean? guesses: - always safe: return top state -
				 * finer: if no outVars occur, then the prestate can be returned safely, right?
				 */
				return Collections.singleton(this);
			}
			
		} else if (term instanceof QuantifiedFormula) {
			throw new UnsupportedOperationException("we cannot deal with quantifiers right now");
		} else if (term instanceof AnnotatedTerm) {
			final Set<VPTfState> result =
					handleTransition(((AnnotatedTerm) term).getSubterm(), tf, negated);
			assert !result.isEmpty();
			return result;
		}
		
		assert false : "missed a case?";
		return Collections.singleton(this);
	}
	
	/**
	 *
	 * @param tfPreState
	 * @param tf
	 * @param negated
	 * @param appTerm
	 *            the subterm of the current transformula that this method should apply to the preState
	 * @return
	 */
	private Set<VPTfState> handleEqualitySubterm(final TransFormula tf,
			final boolean negated, final Term lhs, final Term rhs) {
		if (lhs.getSort().isArraySort()) {
			if (negated) {
				// we have a disequality between arrays
				// we cannot conclude anything from this as we never track all array indices
				return Collections.singleton(this);
			}
			// two arrays are equated

			final IArrayWrapper lhsWrapper = mBuilder.getArrayWrapper(lhs);
			final IArrayWrapper rhsWrapper = mBuilder.getArrayWrapper(rhs);

			final Set<VPTfState> resultStates = new HashSet<>();
			for (final ArrayWithSideCondition lhsArrayWSc : lhsWrapper.getArrayWithSideConditions(this, null)) {
				for (final ArrayWithSideCondition rhsArrayWSc : rhsWrapper.getArrayWithSideConditions(this, null)) {
					
					Set<VPTfState> resultStatesForCurrentNodePair =
							addSideConditionsToState(this, lhsArrayWSc, rhsArrayWSc);

					// add equalities for all the indices we track for both arrays
					for (final Entry<List<VPTfNodeIdentifier>, VPTfNodeIdentifier> en : lhsArrayWSc.getIndexToValue()
							.entrySet()) {
						if (!rhsArrayWSc.getIndexToValue().containsKey(en.getKey())) {
							// the other array does not have a value for the current index
							// --> do nothing
							continue;
						}

						final VPTfNodeIdentifier lhS = en.getValue();
						final VPTfNodeIdentifier rhS = rhsArrayWSc.getIndexToValue().get(en.getKey());
						
						resultStatesForCurrentNodePair =
								VPFactoryHelpers.addEquality(lhS, rhS, resultStatesForCurrentNodePair, mTfStateFactory);
					}
					
					resultStates.addAll(resultStatesForCurrentNodePair);
				}
			}

			assert !resultStates.isEmpty();
			return resultStates;
		} else {
			// two "normal" terms are equated

			final IElementWrapper lhsWrapper = mBuilder.getElementWrapper(lhs);
			final IElementWrapper rhsWrapper = mBuilder.getElementWrapper(rhs);

			if (lhsWrapper == null || rhsWrapper == null) {
				return Collections.singleton(this);
			}

			final Set<VPTfState> resultStates = new HashSet<>();
			//
			for (final NodeIdWithSideCondition lhsNodeWSc : lhsWrapper.getNodeIdWithSideConditions(this)) {
				for (final NodeIdWithSideCondition rhsNodeWSc : rhsWrapper.getNodeIdWithSideConditions(this)) {
					Set<VPTfState> resultStatesForCurrentNodePair =
							addSideConditionsToState(this, lhsNodeWSc, rhsNodeWSc);
					if (lhsNodeWSc instanceof UndeterminedNodeWithSideCondition
							|| rhsNodeWSc instanceof UndeterminedNodeWithSideCondition) {
						// we don't have both nodes --> we cannot add a (dis)equality, but we can still add the
						// sideconditions
						resultStates.addAll(resultStatesForCurrentNodePair);
						continue;
					}
					
					// add (dis)equality
					if (!negated) {
						resultStatesForCurrentNodePair = VPFactoryHelpers.addEquality(lhsNodeWSc.getNodeId(),
								rhsNodeWSc.getNodeId(), resultStatesForCurrentNodePair, mTfStateFactory);
					} else {
						resultStatesForCurrentNodePair = VPFactoryHelpers.addDisEquality(lhsNodeWSc.getNodeId(),
								rhsNodeWSc.getNodeId(), resultStatesForCurrentNodePair, mTfStateFactory);
						
					}
					resultStates.addAll(resultStatesForCurrentNodePair);
				}
			}

			assert !resultStates.isEmpty();
			return resultStates;
		}
	}
	
		/**
	 * Patches the side conditions of the given XwithSideConditions into the given state, returns the resulting state.
	 * 
	 * @param tfPreState
	 * @param lhsNodeWSc
	 * @param rhsNodeWSc
	 * @return
	 */
	private Set<VPTfState> addSideConditionsToState(final VPTfState tfPreState,
			final INodeOrArrayWithSideCondition lhsNodeWSc, final INodeOrArrayWithSideCondition rhsNodeWSc) {
		final VPTfStateBuilder preStateCopy = mTfStateFactory.copy(tfPreState);
		// add side conditions
		for (final VPDomainSymmetricPair<VPTfNodeIdentifier> de : lhsNodeWSc.getDisEqualities()) {
			preStateCopy.addDisEquality(de);
		}
		for (final VPDomainSymmetricPair<VPTfNodeIdentifier> de : rhsNodeWSc.getDisEqualities()) {
			preStateCopy.addDisEquality(de);
		}

		Set<VPTfState> resultStatesForCurrentNodePair = new HashSet<>();
		resultStatesForCurrentNodePair.add(preStateCopy.build());
		for (final VPDomainSymmetricPair<VPTfNodeIdentifier> eq : lhsNodeWSc.getEqualities()) {
			resultStatesForCurrentNodePair = VPFactoryHelpers.addEquality(eq.getFirst(), eq.getSecond(),
					resultStatesForCurrentNodePair, mTfStateFactory);
		}
		for (final VPDomainSymmetricPair<VPTfNodeIdentifier> eq : rhsNodeWSc.getEqualities()) {
			resultStatesForCurrentNodePair = VPFactoryHelpers.addEquality(eq.getFirst(), eq.getSecond(),
					resultStatesForCurrentNodePair, mTfStateFactory);
		}
		// TODO: filter bottom states?
		return resultStatesForCurrentNodePair;
	}
}
