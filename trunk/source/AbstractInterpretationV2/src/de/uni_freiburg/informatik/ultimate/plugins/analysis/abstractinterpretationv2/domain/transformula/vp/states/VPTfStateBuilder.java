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

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPTransFormulaStateBuilderPreparer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IArrayWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IElementWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfArrayIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class VPTfStateBuilder extends IVPStateOrTfStateBuilder<VPTfState, VPTfNodeIdentifier, VPTfArrayIdentifier> {
	
	
	private final Set<IProgramVarOrConst> mInVars;
	private final Set<IProgramVarOrConst> mOutVars;

	private final Set<VPTfNodeIdentifier> mAllNodeIds;

	private final Map<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> mNodeIdToEqGraphNode;

//	private final NestedMap3<EqNode, 
//		Map<IProgramVar, TermVariable>, 
//		Map<IProgramVar, TermVariable>, VPTfNodeIdentifier> mNonAuxVarNodeIds;
//	private final Map<TermVariable, VPAuxVarNodeIdentifier> mAuxVarNodeIds;

	private final HashRelation<VPTfArrayIdentifier, VPTfNodeIdentifier> mArrayIdToFunctionNodes = new HashRelation<>();

	private final TransFormula mTransFormula;

	VPTransFormulaStateBuilderPreparer mTfStatePreparer;

	NestedMap3<IProgramVarOrConst, 
		Pair<IProgramVar, TermVariable>, 
		Pair<IProgramVar, TermVariable>, VPTfArrayIdentifier> mPvocToInVarToOutVarToArrayIdentifier =
			new NestedMap3<>();

	private final VPDomainPreanalysis mPreAnalysis;

	private final Map<Term, IArrayWrapper> mTermToArrayWrapper = new HashMap<>();
	private final Map<Term, IElementWrapper> mTermToElementWrapper = new HashMap<>();

//	private final WrapperFactory mWrapperFactory = new WrapperFactory();

//	private final Map<EqNode, VPTfNodeIdentifier> mEqNodeToInOrThroughTfNodeId = new HashMap<>();
//	private final Map<EqNode, VPTfNodeIdentifier> mEqNodeToOutOrThroughTfNodeId = new HashMap<>();

//	private final VpTfStateFactory mTfStateFactory;

//	/**
//	 * Create the template VPTfStateBuilder for a given TransFormula. These templates are created for all TransFormulas
//	 * in the program before the fixpoint computation starts. During analysis copies of the templates are maded and
//	 * manipulated.
//	 *
//	 * @param preAnalysis
//	 * @param tfStatePreparer
//	 * @param tf
//	 * @param allConstantEqNodes
//	 * @param tfStateFactory 
//	 */
//	public VPTfStateBuilder(final VPDomainPreanalysis preAnalysis,
//			final VPTransFormulaStateBuilderPreparer tfStatePreparer, final TransFormula tf,
//			final Set<EqNode> allConstantEqNodes, VpTfStateFactory tfStateFactory) {
//		mTfStatePreparer = tfStatePreparer;
//		mPreAnalysis = preAnalysis;
//		mTransFormula = tf;
//		mTfStateFactory = tfStateFactory;
//		createEqGraphNodes(preAnalysis, allConstantEqNodes);
//
//		for (final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> tfegn : getAllEqGraphNodes()) {
//			tfegn.setupNode();
//		}
//
//		/*
//		 * Generate disequality set for constants TODO: do this more efficiently
//		 */
//		final Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> disEqualitySet = new HashSet<>();
//		for (final VPTfNodeIdentifier node1 : mAllNodeIds) {
//			for (final VPTfNodeIdentifier node2 : mAllNodeIds) {
//				if (!node1.isLiteral() || !node2.isLiteral()) {
//					continue;
//				}
//				if (!node1.equals(node2)) {
//					disEqualitySet.add(new VPDomainSymmetricPair<>(node1, node2));
//				}
//			}
//		}
//		addDisEqualites(disEqualitySet);
//
//		assert isTopConsistent();
//	}
	
	
	public VPTfStateBuilder(VPDomainPreanalysis preAnalysis, VPTransFormulaStateBuilderPreparer tfStatePreparer, 
			TransFormula transFormula, //VpTfStateFactory tfStateFactory, 
			Set<IProgramVarOrConst> inVars, Set<IProgramVarOrConst> outVars, 
			Set<VPTfNodeIdentifier> allNodeIds, 
			Map<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> nodeIdToEqGraphNode, 
			Set<VPDomainSymmetricPair<VPTfNodeIdentifier>>  initialDisequalities) {
		super(initialDisequalities);
		mPreAnalysis = preAnalysis;
		mTfStatePreparer = tfStatePreparer;
		mTransFormula = transFormula;
//		mTfStateFactory = tfStateFactory;
		mInVars = Collections.unmodifiableSet(inVars);
		mOutVars = Collections.unmodifiableSet(outVars);
		mAllNodeIds = Collections.unmodifiableSet(allNodeIds);
		mNodeIdToEqGraphNode = Collections.unmodifiableMap(nodeIdToEqGraphNode);
	}

	/**
	 * Copy constructor.
	 *
	 * @param builder
	 */
	public VPTfStateBuilder(final VPTfStateBuilder builder) {
		super(builder);
		assert builder.isTopConsistent();
//		mPvocToInVarToOutVarToArrayIdentifier = builder.mPvocToInVarToOutVarToArrayIdentifier;
		mPreAnalysis = builder.mPreAnalysis;
		mTfStatePreparer = builder.mTfStatePreparer;
		mTransFormula = builder.mTransFormula;
//		mTfStateFactory = builder.mTfStateFactory;
		mInVars = builder.mInVars;
		mOutVars = builder.mOutVars;
//		
//		// the arrayIdentifiers are shared between all "sibling" builders (i.e. builders for the same TransFormula)
//		mPvocToInVarToOutVarToArrayIdentifier = builder.mPvocToInVarToOutVarToArrayIdentifier;
//		// the nodeIdentifiers are shared between all "sibling" builders (i.e. builders for the same TransFormula)
		mAllNodeIds = builder.mAllNodeIds;
//		mNonAuxVarNodeIds = builder.mNonAuxVarNodeIds.copy();
//		mAuxVarNodeIds = new HashMap<>(builder.mAuxVarNodeIds);
//		mArrayIdToFunctionNodes = new HashRelation(builder.mArrayIdToFunctionNodes);

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


	@Override
	public VPTfState build() {
		assert mTransFormula != null;
		assert mNodeIdToEqGraphNode != null;
		assert mArrayIdToFunctionNodes != null;
		assert mDisEqualitySet != null;
		assert mInVars != null;
		assert mOutVars != null;
		assert isTopConsistent();
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);

		return new VPTfState(mTransFormula, this, mNodeIdToEqGraphNode, mAllNodeIds, mArrayIdToFunctionNodes, 
				mDisEqualitySet, mIsTop, mInVars, mOutVars);
	}

	@Override
	public EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getEqGraphNode(final VPTfNodeIdentifier i) {
		return mNodeIdToEqGraphNode.get(i);
	}

//	private VPTfNodeIdentifier getNodeIdentifier(final EqNode eqNode, final Map<IProgramVar, TermVariable> inVars,
//			final Map<IProgramVar, TermVariable> outVars) {
//		VPTfNodeIdentifier result = mNonAuxVarNodeIds.get(eqNode, inVars, outVars);
//
//		if (result == null) {
//			result = new VPTfNodeIdentifier(eqNode, inVars, outVars, this);
//			mNonAuxVarNodeIds.put(eqNode, inVars, outVars, result);
//			mAllNodeIds.add(result);
//			if (result.isInOrThrough()) {
//				mEqNodeToInOrThroughTfNodeId.put(eqNode, result);
//			}
//			if (result.isOutOrThrough()) {
//				mEqNodeToOutOrThroughTfNodeId.put(eqNode, result);
//			}
//		}
//		return result;
//	}

//	private VPAuxVarNodeIdentifier getAuxVarNodeIdentifier(final TermVariable tv) {
//		VPAuxVarNodeIdentifier result = mAuxVarNodeIds.get(tv);
//		if (result == null) {
//			result = new VPAuxVarNodeIdentifier(tv);
//			mAuxVarNodeIds.put(tv, result);
//			mAllNodeIds.add(result);
//		}
//		return result;
//	}

	@Override
	Collection<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> getAllEqGraphNodes() {
		return mNodeIdToEqGraphNode.values();
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

//	public VPDomainPreanalysis getPreAnalysis() {
//		return mPreAnalysis;
//	}

	public TransFormula getTransFormula() {
		return mTransFormula;
	}

//	public Set<VPTfNodeIdentifier> getFunctionNodesForArray(final VPTfArrayIdentifier array) {
//		return mArrayIdToFunctionNodes.getImage(array);
//	}

	/**
	 *
	 * @param term
	 * @return null means the array is not tracked
	 */
	IArrayWrapper getArrayWrapper(final Term term) {
		return mTermToArrayWrapper.get(term);
	}

	/**
	 *
	 * @param term
	 * @return null means the array is not tracked
	 */
	IElementWrapper getElementWrapper(final Term term) {
		return  mTermToElementWrapper.get(term);
	}
	
	Set<IProgramVarOrConst> getInVariables() {
		return mInVars;
	}

	Set<IProgramVarOrConst> getOutVariables() {
		return mOutVars;
	}


//	class WrapperFactory {
//		/**
//		 *
//		 *
//		 * @param term
//		 * @return
//		 */
//		IElementWrapper wrapElement(final Term term) {
//			assert !term.getSort().isArraySort();
//
//			final EqNode eqNode = getPreAnalysis().getEqNode(term,
//					VPDomainHelpers.computeProgramVarMappingFromTransFormula(getTransFormula()));
//			if (eqNode == null) {
//				return null;
//			}
//			final VPTfNodeIdentifier nodeId =
//					getOrConstructEqGraphNode(eqNode,
//							VPDomainHelpers.projectToTermAndVars(getTransFormula().getInVars(), term,
//									eqNode.getVariables()),
//							VPDomainHelpers.projectToTermAndVars(getTransFormula().getOutVars(), term,
//									eqNode.getVariables())).mNodeIdentifier;
//
//			if (term instanceof TermVariable || term instanceof ConstantTerm
//					|| ((term instanceof ApplicationTerm) && ((ApplicationTerm) term).getParameters().length == 0)) {
//				return nodeId;
//			} else if (term instanceof ApplicationTerm
//					&& "select".equals(((ApplicationTerm) term).getFunction().getName())) {
//
//				final MultiDimensionalSelect mds = new MultiDimensionalSelect(term);
//
//				final IArrayWrapper array = wrapArray(mds.getArray());
//
//				final List<IElementWrapper> indices = new ArrayList<>();
//				for (final Term index : mds.getIndex()) {
//					final IElementWrapper el = wrapElement(index);
//					assert el != null : "did preanalysis forget this?";
//					indices.add(el);
//				}
//				return new SelectTermWrapper(array, indices);
//			} else {
//				assert false : "missed case?";
//			}
//
//			return null;
//		}
//
//		IArrayWrapper wrapArray(final Term term) {
//			if (term instanceof TermVariable
//					|| term instanceof ConstantTerm
//					|| (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length == 0)) {
//
//				// we have a constant
//				final VPTfArrayIdentifier arrayId = getOrConstructArrayIdentifier(term);
//				return arrayId;
//			} else if (term instanceof ApplicationTerm
//					&& "store".equals(((ApplicationTerm) term).getFunction().getName())) {
//
//				final EqNode eqNode = getPreAnalysis().getEqNode(term,
//						VPDomainHelpers.computeProgramVarMappingFromTransFormula(getTransFormula()));
//				if (eqNode == null) {
//					return null;
//				}
//				getOrConstructEqGraphNode(eqNode,
//						VPDomainHelpers.projectToTermAndVars(getTransFormula().getInVars(), term,
//								eqNode.getVariables()),
//						VPDomainHelpers.projectToTermAndVars(getTransFormula().getOutVars(), term,
//								eqNode.getVariables()));
//
//				final MultiDimensionalStore mds = new MultiDimensionalStore(term);
//
//				final IArrayWrapper array = wrapArray(mds.getArray());
//
//				final List<IElementWrapper> indices = new ArrayList<>();
//				for (final Term index : mds.getIndex()) {
//					indices.add(wrapElement(index));
//				}
//
//				final IElementWrapper value = wrapElement(mds.getValue());
//
//				return new StoreTermWrapper(array, indices, value);
//			} else {
//				assert false : "missed case?";
//			}
//
//			return null;
//		}
//
//	}

//	public <ACTION extends IIcfgTransition<IcfgLocation>> void patchIn(VPState<ACTION> oldState) {
//		// TODO Auto-generated method stub
//		assert false;
//		
//	}
}