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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPTransFormulaStateBuilderPreparer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.ArrayInOutStatus;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunctionNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IArrayWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IElementWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.SelectTermWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.StoreTermWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.TfNodeInOutStatus;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPAuxVarNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfArrayIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfExtraArrayIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VpTfExtraNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class VPTfStateBuilder extends IVPStateOrTfStateBuilder<VPTfState, VPTfNodeIdentifier, VPTfArrayIdentifier> {

	private Set<VPTfNodeIdentifier> mAllNodeIds = new HashSet<>();
	private Map<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> mNodeIdToEqGraphNode =
			new HashMap<>();
	private NestedMap3<EqNode, Map<IProgramVar, TermVariable>, Map<IProgramVar, TermVariable>, VPTfNodeIdentifier> mNonAuxVarNodeIds =
			new NestedMap3<>();
	private Map<TermVariable, VPAuxVarNodeIdentifier> mAuxVarNodeIds = new HashMap<>();

	private HashRelation<VPTfArrayIdentifier, VPTfNodeIdentifier> mArrayIdToFunctionNodes = new HashRelation<>();

	private final TransFormula mTransFormula;

	VPTransFormulaStateBuilderPreparer mTfStatePreparer;

	NestedMap3<IProgramVarOrConst, Pair<IProgramVar, TermVariable>, Pair<IProgramVar, TermVariable>, VPTfArrayIdentifier> mPvocToInVarToOutVarToArrayIdentifier =
			new NestedMap3<>();

	private final VPDomainPreanalysis mPreAnalysis;
	private final Map<Term, IArrayWrapper> mTermToArrayWrapper = new HashMap<>();
	private final Map<Term, IElementWrapper> mTermToElementWrapper = new HashMap<>();

	private final WrapperFactory mWrapperFactory = new WrapperFactory();

	private final Map<EqNode, VPTfNodeIdentifier> mEqNodeToInOrThroughTfNodeId = new HashMap<>();
	private final Map<EqNode, VPTfNodeIdentifier> mEqNodeToOutOrThroughTfNodeId = new HashMap<>();

	private final Map<IProgramVar, VPTfArrayIdentifier> mProgramVarToInOrThroughArrayId = new HashMap<>();
	private final Map<IProgramVar, VPTfArrayIdentifier> mProgramVarToOutOrThroughArrayId = new HashMap<>();

	/**
	 * Create the template VPTfStateBuilder for a given TransFormula. These templates are created for all TransFormulas
	 * in the program before the fixpoint computation starts. During analysis copies of the templates are maded and
	 * manipulated.
	 *
	 * @param preAnalysis
	 * @param tfStatePreparer
	 * @param tf
	 * @param allConstantEqNodes
	 */
	public VPTfStateBuilder(final VPDomainPreanalysis preAnalysis,
			final VPTransFormulaStateBuilderPreparer tfStatePreparer, final TransFormula tf,
			final Set<EqNode> allConstantEqNodes) {
		mTfStatePreparer = tfStatePreparer;
		mPreAnalysis = preAnalysis;
		mTransFormula = tf;
		createEqGraphNodes(preAnalysis, allConstantEqNodes);

		for (final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> tfegn : getAllEqGraphNodes()) {
			tfegn.setupNode();
		}

		/*
		 * Generate disequality set for constants TODO: do this more efficiently
		 */
		final Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> disEqualitySet = new HashSet<>();
		for (final VPTfNodeIdentifier node1 : mAllNodeIds) {
			for (final VPTfNodeIdentifier node2 : mAllNodeIds) {
				if (!node1.isLiteral() || !node2.isLiteral()) {
					continue;
				}
				if (!node1.equals(node2)) {
					disEqualitySet.add(new VPDomainSymmetricPair<>(node1, node2));
				}
			}
		}
		addDisEqualites(disEqualitySet);

		assert isTopConsistent();
	}

	/**
	 * Copy constructor.
	 *
	 * @param builder
	 */
	public VPTfStateBuilder(final VPTfStateBuilder builder) {
		super(builder);
		assert builder.isTopConsistent();
		mPvocToInVarToOutVarToArrayIdentifier = builder.mPvocToInVarToOutVarToArrayIdentifier;
		mPreAnalysis = builder.mPreAnalysis;
		mTfStatePreparer = builder.mTfStatePreparer;
		mTransFormula = builder.mTransFormula;
		
		// the arrayIdentifiers are shared between all "sibling" builders (i.e. builders for the same TransFormula)
		mPvocToInVarToOutVarToArrayIdentifier = builder.mPvocToInVarToOutVarToArrayIdentifier;
		// the nodeIdentifiers are shared between all "sibling" builders (i.e. builders for the same TransFormula)
		mAllNodeIds = builder.mAllNodeIds;
		mNonAuxVarNodeIds = builder.mNonAuxVarNodeIds.copy();
		mAuxVarNodeIds = new HashMap<>(builder.mAuxVarNodeIds);
		mArrayIdToFunctionNodes = builder.mArrayIdToFunctionNodes.copy();

		// nodes need to be deepcopied..
		mNodeIdToEqGraphNode = new HashMap<>();
		for (final Entry<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> en : 
				builder.mNodeIdToEqGraphNode.entrySet()) {
			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> egnInOldState = en.getValue();
			final VPTfNodeIdentifier nodeId = en.getKey();
			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newGraphNode = new EqGraphNode<>(nodeId);
			assert newGraphNode != null;
			mNodeIdToEqGraphNode.put(nodeId, newGraphNode);
			assert !builder.mIsTop || newGraphNode.getRepresentative() == newGraphNode;
		}

		for (final Entry<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> en : 
				builder.mNodeIdToEqGraphNode.entrySet()) {
			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> egnInOldState = en.getValue();
			final VPTfNodeIdentifier nodeId = en.getKey();
			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newGraphNode = getEqGraphNode(nodeId);
			EqGraphNode.copyFields(egnInOldState, newGraphNode, this);

			newGraphNode.setupNode();
		}

		assert isTopConsistent();
	}

	private void createEqGraphNodes(final VPDomainPreanalysis preAnalysis, final Set<EqNode> allConstantEqNodes) {
		/*
		 * The EqGraphNodes we need for the given TransFormula can come from the following sources: (Paradigm: whenever
		 * the TransFormula can introduce a (dis-)equality about something, we need EqGraphNodes to track that.) 1.
		 * equalities in the TransFormula a) between elements b) between arrays (normal or store terms) --> we obtain
		 * the EqGraphNodes during construction of the Element/ArrayWrappers 2. variables in the TransFormula (outside
		 * of array accesses) that we have an EqNode for --> we can see them in the invars and outvars of the
		 * TransFormula 3. constants in the TransFormula that we have an EqNode for --> we can just take the constant
		 * EqNodes from the preanalysis 4. the auxVars of the TransFormula // * 5. Array equalities in the TransFormula
		 * // * --> for both arrays we need all the EqFunctionNodes that have the array as function // * --> this also
		 * includes ArrayUpdates, which are array equalities with store terms
		 *
		 */

		/*
		 * Step 1a. construct element wrappers, for non-array equations (in this order because the array equations
		 * should only create EqGraphNodes that are not created anyway..)
		 */
		final Set<ApplicationTerm> xQualities =
				new ApplicationTermFinder(new HashSet<>(Arrays.asList(new String[] { "=", "distinct" })), false)
						.findMatchingSubterms(mTransFormula.getFormula());
		for (final ApplicationTerm xQuality : xQualities) {
			final Term lhs = xQuality.getParameters()[0];
			final Term rhs = xQuality.getParameters()[1];

			if (!lhs.getSort().isArraySort()) {
				getOrConstructElementWrapper(lhs);
				getOrConstructElementWrapper(rhs);
			} else {
				getOrConstructArrayWrapper(lhs);
				getOrConstructArrayWrapper(rhs);
			}
		}

		/*
		 * Step 1b. construct element wrappers, for array equations
		 */
		for (final ApplicationTerm xQuality : xQualities) {
			final Term lhs = xQuality.getParameters()[0];
			final Term rhs = xQuality.getParameters()[1];

			/*
			 * construct the additional "through nodes" for array indices that are not in the formula
			 */
			if (lhs.getSort().isArraySort()) {
				final IArrayWrapper lhsWrapper = getOrConstructArrayWrapper(lhs);
				constructEqGraphNodesForEquatedArrayWrapper(lhsWrapper);
				final IArrayWrapper rhsWrapper = getOrConstructArrayWrapper(rhs);
				constructEqGraphNodesForEquatedArrayWrapper(rhsWrapper);
			}
		}

		/*
		 * 2. variables in the TransFormula (outside of array accesses)
		 */
		for (final Entry<TermVariable, IProgramVar> en : VPDomainHelpers
				.computeProgramVarMappingFromTransFormula(mTransFormula).entrySet()) {
			final EqNode varEqNode = preAnalysis.getEqNode(en.getValue().getTerm(), Collections.emptyMap());

			if (varEqNode == null) {
				// we don't track that variable
				continue;
			}

			getOrConstructElementWrapper(en.getKey());
		}

		/*
		 * 3. constants in the TransFormula
		 */
		for (final EqNode constantEqNode : allConstantEqNodes) {
			assert constantEqNode.isConstant();

			/* 
			 *  technical note: the constant select/store terms that occur in mTransFormula have been treated by
			 *  step 1. already. -- therefore it should be ok to use EqNode.getTerm for the term argument of the
			 *  getOrConstruct method; because say we have a constant store in this formula, it has
			 * already been put into the map.
			 */
			getOrConstructElementWrapper(constantEqNode.getTerm());
		}

		/*
		 * 4. the auxVars of the TransFormula
		 */
		for (final TermVariable auxVar : mTransFormula.getAuxVars()) {
			getOrConstructElementWrapper(auxVar);
		}
	}

	/**
	 * Plan: - as input we get an IArrayWrapper, right now we just take its base array (e.g. for (store a i x) we take
	 * a) --> this might be optimized further perhaps - we look up which indices we track for that array (from
	 * preAnalysis), i.e., which indices of that array our states talk about - for each of these EqFunctionNodes we
	 * build an EqGraphNode, which has an in/out/through status compatible with the array - there may be some
	 * EqGraphNodes constructed in an earlier step (for a Term that occurs in the TransFormula) that we can use for
	 * this, however we usually will have to introduce special EqGraphNodes for this. - if the array is "in" in the
	 * given TransFormula, its corresponding EqGraphNode including all its descendants needs to be inOrThrough
	 * analogously if the array is "out" if the array is "through", then we need both versions for each functionNode:
	 * inOrThrough and outOrThrough .. the array could also be an auxVar --> TODO
	 *
	 *
	 *
	 * TODO: a further optimization could be to only take indices into account that are tracked for both arrays.
	 *
	 * @param arrayWrapper
	 */
	private void constructEqGraphNodesForEquatedArrayWrapper(final IArrayWrapper arrayWrapper) {
		final VPTfArrayIdentifier arrayId = arrayWrapper.getBaseArray();

		final IProgramVarOrConst arrayPvoc = arrayId.getProgramVarOrConst();
		final Set<EqFunctionNode> functionNodesForArray = mPreAnalysis.getFunctionNodesForArray(arrayPvoc);

		// // TODO (efficiency): these first steps could all be computed once, outside of this method..

		for (final EqFunctionNode functionNode : functionNodesForArray) {
			/*
			 * (this is a reason why the EqGraphNodes for array equalities should be constructed after those for
			 * "normal" terms)
			 */

			if (arrayId.isInOrThrough()) {
				// ensure that we have an inOrThrough node for functionNode

				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newNode =
						getOrConstructInOrOutOrThroughEqGraphNode(functionNode, true);
				assert newNode.nodeIdentifier.getEqNode() == functionNode;
				assert newNode.nodeIdentifier.isInOrThrough();
			}

			if (arrayId.isOutOrThrough()) {
				// ensure that we have an outOrThrough node for functionNode

				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newNode =
						getOrConstructInOrOutOrThroughEqGraphNode(functionNode, false);
				assert newNode.nodeIdentifier.getEqNode() == functionNode;
				assert newNode.nodeIdentifier.isOutOrThrough();
			}

			final ArrayInOutStatus targetInOutStatus = arrayId.getInOutStatus();
			if (targetInOutStatus == ArrayInOutStatus.AUX) {
				assert false : "TODO: treat this case";
			}
		}
	}

	private EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getOrConstructInOrOutOrThroughEqGraphNode(
			final EqNode eqNode, final boolean inOrThroughOrOutOrThroughChooseIn) {

		final VPTfNodeIdentifier resultNodeId = inOrThroughOrOutOrThroughChooseIn
				? mEqNodeToInOrThroughTfNodeId.get(eqNode) : mEqNodeToOutOrThroughTfNodeId.get(eqNode);

		if (resultNodeId != null) {
			// we already have an EqGraphNode for EqFunctionNode
			assert inOrThroughOrOutOrThroughChooseIn ? resultNodeId.isInOrThrough() : resultNodeId.isOutOrThrough();
			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> result = mNodeIdToEqGraphNode.get(resultNodeId);
			assert result != null;
			return result;
		}

		if (eqNode instanceof EqFunctionNode) {
			final EqFunctionNode functionNode = (EqFunctionNode) eqNode;

			final VPTfArrayIdentifier arrayId =
					getOrConstructArrayIdentifier(functionNode.getFunction(), inOrThroughOrOutOrThroughChooseIn);

			/*
			 * the new EqGraphNode must be a function node with - function "arrayId" - arguments with inOutStatus In or
			 * Through (those need to be getOrConstructed recursively, as any descendant may already be present or
			 * not..)
			 */

			// obtain index vector for the new EqGraphNode
			final List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> indexVector = new ArrayList<>();
			final Map<IProgramVar, TermVariable> newInVars = new HashMap<>();
			final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>();
			for (final EqNode arg : functionNode.getArgs()) {
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> indexVectorElement =
						getOrConstructInOrOutOrThroughEqGraphNode(arg, inOrThroughOrOutOrThroughChooseIn);
				newInVars.putAll(indexVectorElement.nodeIdentifier.getInVars());
				newOutVars.putAll(indexVectorElement.nodeIdentifier.getOutVars());
				indexVector.add(indexVectorElement);
			}

			// obtain new EqGraphNode
			newInVars.putAll(arrayId.getInVars());
			newOutVars.putAll(arrayId.getOutVars());
			final VPTfNodeIdentifier newNodeId = getNodeIdentifier(functionNode, newInVars, newOutVars);

			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newFunctionEqGraphNode =
					new EqGraphNode<>(newNodeId);
			// getOrConstructEqGraphNode(newNodeId);

			// update ccchild/parent fields
			newFunctionEqGraphNode.addToCcchild(arrayId, indexVector);

			for (final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> itn : indexVector) {
				itn.addToCcpar(newFunctionEqGraphNode);
			}

			// update store maps
			mNodeIdToEqGraphNode.put(newNodeId, newFunctionEqGraphNode);
			mArrayIdToFunctionNodes.addPair(arrayId, newNodeId);

			assert newFunctionEqGraphNode != null;
			return newFunctionEqGraphNode;
		}
		VPTfNodeIdentifier newNodeId;
		if (eqNode.isConstant()) {
			newNodeId = getNodeIdentifier(eqNode, Collections.emptyMap(), Collections.emptyMap());
			assert newNodeId != null;
		} else {
			boolean hasIn = false;
			boolean hasOut = false;

			for (final IProgramVar eqNodeVar : eqNode.getVariables()) {
				if (mTransFormula.getInVars().containsKey(eqNodeVar)) {
					hasIn = true;
				}
				if (mTransFormula.getOutVars().containsKey(eqNodeVar)) {
					hasOut = true;
				}
			}

			if (inOrThroughOrOutOrThroughChooseIn) {
				// we need to create an inOrThrough node
				if (!hasOut) {
					// we create a through id
					newNodeId = new VpTfExtraNodeIdentifier(eqNode, TfNodeInOutStatus.THROUGH);
					mEqNodeToInOrThroughTfNodeId.put(eqNode, newNodeId);
					mEqNodeToOutOrThroughTfNodeId.put(eqNode, newNodeId);
				} else {
					// we create an in id
					newNodeId = new VpTfExtraNodeIdentifier(eqNode, TfNodeInOutStatus.IN);
					mEqNodeToInOrThroughTfNodeId.put(eqNode, newNodeId);
				}
			} else {
				// we need to create an outOrThrough node
				if (!hasIn) {
					// we create a through id
					newNodeId = new VpTfExtraNodeIdentifier(eqNode, TfNodeInOutStatus.THROUGH);
					mEqNodeToInOrThroughTfNodeId.put(eqNode, newNodeId);
					mEqNodeToOutOrThroughTfNodeId.put(eqNode, newNodeId);
				} else {
					// we create an out id
					newNodeId = new VpTfExtraNodeIdentifier(eqNode, TfNodeInOutStatus.OUT);
					mEqNodeToOutOrThroughTfNodeId.put(eqNode, newNodeId);
				}
			}
		}
		final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newEqGraphNode = new EqGraphNode<>(newNodeId);
		mNodeIdToEqGraphNode.put(newNodeId, newEqGraphNode);

		assert newEqGraphNode != null;
		return newEqGraphNode;
	}

	private IElementWrapper getOrConstructElementWrapper(final Term term) {
		IElementWrapper result = mTermToElementWrapper.get(term);
		if (result == null) {
			result = mWrapperFactory.wrapElement(term);
			mTermToElementWrapper.put(term, result);
		}
		return result;
	}

	private IArrayWrapper getOrConstructArrayWrapper(final Term term) {
		IArrayWrapper result = mTermToArrayWrapper.get(term);
		if (result == null) {
			result = mWrapperFactory.wrapArray(term);
			mTermToArrayWrapper.put(term, result);
		}
		return result;
	}


	private EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getOrConstructAuxEqGraphNode(final TermVariable tv) {
		// we have an AuxVar
		final VPAuxVarNodeIdentifier nodeId = getAuxVarNodeIdentifier(tv);
		EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> result = mNodeIdToEqGraphNode.get(nodeId);
		if (result == null) {
			result = new EqGraphNode<>(nodeId);
			mNodeIdToEqGraphNode.put(nodeId, result);
		}
		return result;
	}

	/**
	 * construct a "normal" (i.e. non-AuxVar-) EqGraphNode
	 *
	 * @param eqNode
	 * @param inVars
	 * @param outVars
	 * @return
	 */
	private EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getOrConstructEqGraphNode(final EqNode eqNode,
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {

		final VPTfNodeIdentifier nodeIdentifier = getNodeIdentifier(eqNode, inVars, outVars);

		EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> result = mNodeIdToEqGraphNode.get(nodeIdentifier);
		if (result != null) {
			return result;
		}

		/*
		 * the corresponding EqGraphNode has not yet been created
		 */
		result = getOrConstructEqGraphNode(nodeIdentifier);

		return result;
	}

	private EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>
			getOrConstructEqGraphNode(final VPTfNodeIdentifier nodeIdentifier) {

		EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> result = mNodeIdToEqGraphNode.get(nodeIdentifier);
		if (result != null) {
			return result;
		}

		result = new EqGraphNode<>(nodeIdentifier);

		mNodeIdToEqGraphNode.put(nodeIdentifier, result);

		if (nodeIdentifier.isFunction()) {
			final EqFunctionNode eqFunctionNode = (EqFunctionNode) nodeIdentifier.getEqNode();

			final List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> argNodes = new ArrayList<>();

			for (int i = 0; i < ((EqFunctionNode) nodeIdentifier.getEqNode()).getArgs().size(); i++) {
				final EqNode indexEqnode = eqFunctionNode.getArgs().get(i);
				final Map<IProgramVar, TermVariable> argInVars =
						VPDomainHelpers.projectOut(nodeIdentifier.getInVars(), eqFunctionNode.getFunction());
				final Map<IProgramVar, TermVariable> argOutVars =
						VPDomainHelpers.projectOut(nodeIdentifier.getOutVars(), eqFunctionNode.getFunction());
				final VPTfNodeIdentifier argNodeId = getNodeIdentifier(indexEqnode, argInVars, argOutVars);
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> argNode =
						getOrConstructEqGraphNode(argNodeId);

				// later EqGraphNode.setupNode() will make initCCPar out of this
				argNode.addToCcpar(result);
				argNodes.add(argNode);
			}
			// later EqGraphNode.setupNode() will make initCcchild out of this:
			final VPTfArrayIdentifier arrayId = nodeIdentifier.getFunction();
			result.addToCcchild(arrayId, argNodes);

			mArrayIdToFunctionNodes.addPair(arrayId, nodeIdentifier);
		}

		return result;
	}

	@Override
	public VPTfState build() {
		assert mTransFormula != null;
		assert mNodeIdToEqGraphNode != null;
		assert mArrayIdToFunctionNodes != null;
		assert mDisEqualitySet != null;
		assert mVars != null;
		assert isTopConsistent();
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);

		return new VPTfState(mTransFormula, this, mNodeIdToEqGraphNode,
				mAllNodeIds, mArrayIdToFunctionNodes, mDisEqualitySet, mIsTop, mVars);
	}

	@Override
	public EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getEqGraphNode(final VPTfNodeIdentifier i) {
		return mNodeIdToEqGraphNode.get(i);
	}

	public VPTfNodeIdentifier getNodeIdentifier(final EqNode eqNode, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		VPTfNodeIdentifier result = mNonAuxVarNodeIds.get(eqNode, inVars, outVars);

		if (result == null) {
			result = new VPTfNodeIdentifier(eqNode, inVars, outVars, this);
			mNonAuxVarNodeIds.put(eqNode, inVars, outVars, result);
			mAllNodeIds.add(result);
			if (result.isInOrThrough()) {
				mEqNodeToInOrThroughTfNodeId.put(eqNode, result);
			}
			if (result.isOutOrThrough()) {
				mEqNodeToOutOrThroughTfNodeId.put(eqNode, result);
			}
		}
		return result;
	}

	public VPAuxVarNodeIdentifier getAuxVarNodeIdentifier(final TermVariable tv) {
		VPAuxVarNodeIdentifier result = mAuxVarNodeIds.get(tv);
		if (result == null) {
			result = new VPAuxVarNodeIdentifier(tv);
			mAuxVarNodeIds.put(tv, result);
			mAllNodeIds.add(result);
		}
		return result;
	}

	@Override
	Collection<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> getAllEqGraphNodes() {
		return mNodeIdToEqGraphNode.values();
	}

	private VPTfArrayIdentifier getOrConstructArrayIdentifier(final IProgramVarOrConst array,
			final boolean inOrThroughOrOutOrThroughChooseIn) {

		if (array instanceof IProgramVar) {
			final VPTfArrayIdentifier earlyResult = inOrThroughOrOutOrThroughChooseIn
					? mProgramVarToInOrThroughArrayId.get(array) : mProgramVarToOutOrThroughArrayId.get(array);
			if (earlyResult != null) {
				assert inOrThroughOrOutOrThroughChooseIn ? earlyResult.isInOrThrough() : earlyResult.isOutOrThrough();
				assert earlyResult.getProgramVarOrConst() == array;
				return earlyResult;
			}

			// tvIn != null means that array is an inVar in mTransFormula, analogously for tvOut
			final TermVariable tvIn = mTransFormula.getInVars().get(array);
			final TermVariable tvOut = mTransFormula.getOutVars().get(array);

			if (tvIn != null && inOrThroughOrOutOrThroughChooseIn) {
				/*
				 * the TransFormula has an inVar for array and we want inOrThrough --> retrieve the corresponding
				 * arrayId
				 */
				final VPTfArrayIdentifier result = getOrConstructArrayIdentifier(tvIn);
				assert inOrThroughOrOutOrThroughChooseIn ? result.isInOrThrough() : result.isOutOrThrough();
				assert result.getProgramVarOrConst() == array;
				return result;
			} else if (tvOut != null && !inOrThroughOrOutOrThroughChooseIn) {
				/*
				 * the TransFormula has an outVar for array and we want outOrThrough --> retrieve the corresponding
				 * arrayId
				 */
				final VPTfArrayIdentifier result = getOrConstructArrayIdentifier(tvOut);
				assert inOrThroughOrOutOrThroughChooseIn ? result.isInOrThrough() : result.isOutOrThrough();
				assert result.getProgramVarOrConst() == array;
				return result;
			} else {
				/*
				 * there is no TermVariable in the TransFormula with the inOrThrough-status we are looking for --> we
				 * need an ArrayId especially for this purpose --> whether the new ArrayId we create is in/out or
				 * through depends on inVars/outVars, too: if we need an inOrThrough id, and there is an
				 * out-TermVariable for the array, we create an in-Id, otherwise we create a through-Id (and vice versa
				 * for outOrThrough)
				 */
				if (inOrThroughOrOutOrThroughChooseIn) {
					if (tvOut == null) {
						// we create a through id
						final VPTfArrayIdentifier newId = new VPTfExtraArrayIdentifier(array, ArrayInOutStatus.THROUGH);
						mProgramVarToInOrThroughArrayId.put((IProgramVar) array, newId);
						mProgramVarToOutOrThroughArrayId.put((IProgramVar) array, newId);

						assert inOrThroughOrOutOrThroughChooseIn ? newId.isInOrThrough() : newId.isOutOrThrough();
						assert newId.getProgramVarOrConst() == array;
						return newId;
					}
					// we create an in id
					final VPTfArrayIdentifier newId = new VPTfExtraArrayIdentifier(array, ArrayInOutStatus.IN);
					mProgramVarToOutOrThroughArrayId.put((IProgramVar) array, newId);
					assert inOrThroughOrOutOrThroughChooseIn ? newId.isInOrThrough() : newId.isOutOrThrough();
					assert newId.getProgramVarOrConst() == array;
					return newId;
				}
				if (tvIn == null) {
					// we create a through id
					final VPTfArrayIdentifier newId = new VPTfExtraArrayIdentifier(array, ArrayInOutStatus.THROUGH);
					mProgramVarToInOrThroughArrayId.put((IProgramVar) array, newId);
					mProgramVarToOutOrThroughArrayId.put((IProgramVar) array, newId);
					assert inOrThroughOrOutOrThroughChooseIn ? newId.isInOrThrough() : newId.isOutOrThrough();
					assert newId.getProgramVarOrConst() == array;
					return newId;
				}
				// we create an out id
				final VPTfArrayIdentifier newId = new VPTfExtraArrayIdentifier(array, ArrayInOutStatus.OUT);
				mProgramVarToInOrThroughArrayId.put((IProgramVar) array, newId);
				assert inOrThroughOrOutOrThroughChooseIn ? newId.isInOrThrough() : newId.isOutOrThrough();
				assert newId.getProgramVarOrConst() == array;
				return newId;
			}
		}
		final VPTfArrayIdentifier result =
				getOrConstructArrayIdentifier(array, Collections.emptyMap(), Collections.emptyMap());
		assert inOrThroughOrOutOrThroughChooseIn ? result.isInOrThrough() : result.isOutOrThrough();
		assert result.getProgramVarOrConst() == array;
		return result;
	}

	public VPTfArrayIdentifier getOrConstructArrayIdentifier(final Term term) {
		return getOrConstructArrayIdentifier(
				mPreAnalysis.getIProgramVarOrConstOrLiteral(term,
						VPDomainHelpers.computeProgramVarMappingFromTransFormula(mTransFormula)),
				VPDomainHelpers.projectToTerm(mTransFormula.getInVars(), term),
				VPDomainHelpers.projectToTerm(mTransFormula.getOutVars(), term));
	}

	/**
	 *
	 * @param function
	 * @param inVars
	 * @param outVars
	 * @return
	 *
	 */
	public VPTfArrayIdentifier getOrConstructArrayIdentifier(final IProgramVarOrConst function,
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		Pair<IProgramVar, TermVariable> inVar = null;
		Pair<IProgramVar, TermVariable> outVar = null;

		final TermVariable iTv = inVars.get(function);
		if (iTv != null) {
			inVar = new Pair<>((IProgramVar) function, iTv);
		}
		final TermVariable oTv = outVars.get(function);
		if (oTv != null) {
			outVar = new Pair<>((IProgramVar) function, oTv);
		}
		VPTfArrayIdentifier result = mPvocToInVarToOutVarToArrayIdentifier.get(function, inVar, outVar);

		if (result == null) {
			result = new VPTfArrayIdentifier(function, inVar, outVar);
			mPvocToInVarToOutVarToArrayIdentifier.put(function, inVar, outVar, result);
		}
		return result;
	}

	public VPDomainPreanalysis getPreAnalysis() {
		return mPreAnalysis;
	}

	public TransFormula getTransFormula() {
		return mTransFormula;
	}

	public Set<VPTfNodeIdentifier> getFunctionNodesForArray(final VPTfArrayIdentifier array) {
		return mArrayIdToFunctionNodes.getImage(array);
	}

	/**
	 *
	 * @param term
	 * @return null means the array is not tracked
	 */
	public IArrayWrapper getArrayWrapper(final Term term) {
		final IArrayWrapper result = mTermToArrayWrapper.get(term);
		// assert result != null;
		return result;
	}

	/**
	 *
	 * @param term
	 * @return null means the array is not tracked
	 */
	public IElementWrapper getElementWrapper(final Term term) {
		final IElementWrapper result = mTermToElementWrapper.get(term);
		// assert result != null;
		return result;
	}

	class WrapperFactory {
		/**
		 *
		 *
		 * @param term
		 * @return
		 */
		IElementWrapper wrapElement(final Term term) {
			assert !term.getSort().isArraySort();

			final EqNode eqNode = getPreAnalysis().getEqNode(term,
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(getTransFormula()));
			if (eqNode == null) {
				return null;
			}
			final VPTfNodeIdentifier nodeId =
					getOrConstructEqGraphNode(eqNode,
							VPDomainHelpers.projectToTermAndVars(getTransFormula().getInVars(), term,
									eqNode.getVariables()),
							VPDomainHelpers.projectToTermAndVars(getTransFormula().getOutVars(), term,
									eqNode.getVariables())).nodeIdentifier;

			if (term instanceof TermVariable || term instanceof ConstantTerm
					|| ((term instanceof ApplicationTerm) && ((ApplicationTerm) term).getParameters().length == 0)) {
				return nodeId;
			} else if (term instanceof ApplicationTerm
					&& "select".equals(((ApplicationTerm) term).getFunction().getName())) {

				final MultiDimensionalSelect mds = new MultiDimensionalSelect(term);

				final IArrayWrapper array = wrapArray(mds.getArray());

				final List<IElementWrapper> indices = new ArrayList<>();
				for (final Term index : mds.getIndex()) {
					final IElementWrapper el = wrapElement(index);
					assert el != null : "did preanalysis forget this?";
					indices.add(el);
				}
				return new SelectTermWrapper(array, indices);
			} else {
				assert false : "missed case?";
			}

			return null;
		}

		IArrayWrapper wrapArray(final Term term) {
			if (term instanceof TermVariable
					|| term instanceof ConstantTerm
					|| (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length == 0)) {

				// we have a constant
				final VPTfArrayIdentifier arrayId = getOrConstructArrayIdentifier(term);
				return arrayId;
			} else if (term instanceof ApplicationTerm
					&& "store".equals(((ApplicationTerm) term).getFunction().getName())) {

				final EqNode eqNode = getPreAnalysis().getEqNode(term,
						VPDomainHelpers.computeProgramVarMappingFromTransFormula(getTransFormula()));
				if (eqNode == null) {
					return null;
				}
				getOrConstructEqGraphNode(eqNode,
						VPDomainHelpers.projectToTermAndVars(getTransFormula().getInVars(), term,
								eqNode.getVariables()),
						VPDomainHelpers.projectToTermAndVars(getTransFormula().getOutVars(), term,
								eqNode.getVariables()));

				final MultiDimensionalStore mds = new MultiDimensionalStore(term);

				final IArrayWrapper array = wrapArray(mds.getArray());

				final List<IElementWrapper> indices = new ArrayList<>();
				for (final Term index : mds.getIndex()) {
					indices.add(wrapElement(index));
				}

				final IElementWrapper value = wrapElement(mds.getValue());

				return new StoreTermWrapper(array, indices, value);
			} else {
				assert false : "missed case?";
			}

			return null;
		}

	}
}