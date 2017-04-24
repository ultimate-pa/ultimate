package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ContainsSubterm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.ArrayInOutStatus;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunctionNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IArrayWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IElementWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.SelectTermWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.StoreTermWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPAuxVarNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfArrayIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfStateBuilder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Sets up a VpTfStateBuilder without any (dis)equality information ("vanilla"). Creates all the necessary 
 * EqGraphNodes according to the given transition.
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class CreateVanillaTfStateBuilder {

	private VPTransFormulaStateBuilderPreparer mTfStatePreparer;
	private VPDomainPreanalysis mPreAnalysis;
	private TransFormula mTransFormula;
	
	private Set<VPTfNodeIdentifier> mAllNodeIds = new HashSet<>();
	private Map<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> mNodeIdToEqGraphNode =
			new HashMap<>();
	private Map<TermVariable, VPAuxVarNodeIdentifier> mAuxVarNodeIds = new HashMap<>();
	private HashRelation<VPTfArrayIdentifier, VPTfNodeIdentifier> mArrayIdToFunctionNodes = new HashRelation<>();
	
	
	private NestedMap3<EqNode, Map<IProgramVar, TermVariable>, Map<IProgramVar, TermVariable>, VPTfNodeIdentifier> 
		mNonAuxVarNodeIds = new NestedMap3<>();
	
//	private final Map<EqNode, VPTfNodeIdentifier> mEqNodeToInOrThroughTfNodeId = new HashMap<>();
//	private final Map<EqNode, VPTfNodeIdentifier> mEqNodeToOutOrThroughTfNodeId = new HashMap<>();

//	private final Map<IProgramVar, VPTfArrayIdentifier> mProgramVarToInOrThroughArrayId = new HashMap<>();
//	private final Map<IProgramVar, VPTfArrayIdentifier> mProgramVarToOutOrThroughArrayId = new HashMap<>();

	private final NestedMap3<IProgramVarOrConst, 
		Pair<IProgramVar, TermVariable>, 
		Pair<IProgramVar, TermVariable>, VPTfArrayIdentifier> mPvocToInVarToOutVarToArrayIdentifier =
			new NestedMap3<>();

	private final Map<Term, IArrayWrapper> mTermToArrayWrapper = new HashMap<>();
	private final Map<Term, IElementWrapper> mTermToElementWrapper = new HashMap<>();

	private final WrapperFactory mWrapperFactory = new WrapperFactory();
	private final Set<IProgramVarOrConst> mInVars;
	private final Set<IProgramVarOrConst> mOutVars;
	private final IAction mAction;
//	private Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> mOutNodes = new HashSet<>();



	/**
	 * Create the template VPTfStateBuilder for a given TransFormula. These templates are created for all TransFormulas
	 * in the program before the fixpoint computation starts. During analysis copies of the templates are made and
	 * manipulated.
	 *
	 * @param preAnalysis
	 * @param tfStatePreparer
	 * @param tf
	 * @param allConstantEqNodes
	 * @param tfStateFactory 
	 * @param inVars
	 * @param outVars
	 */
	public CreateVanillaTfStateBuilder(final VPDomainPreanalysis preAnalysis,
			final VPTransFormulaStateBuilderPreparer tfStatePreparer, final IAction action,//final TransFormula tf,
			final Set<EqNode> allConstantEqNodes, final Set<IProgramVarOrConst> inVars, 
			final Set<IProgramVarOrConst> outVars) {
		mTfStatePreparer = tfStatePreparer;
		mPreAnalysis = preAnalysis;
		mAction = action;
		mTransFormula = action.getTransformula();
		mInVars = inVars;
		mOutVars = outVars;
//		mTfStateFactory = tfStateFactory;

		createEqGraphNodes(preAnalysis, allConstantEqNodes);
//		createEqGraphNodes(preAnalysis);

		for (final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> tfegn : mNodeIdToEqGraphNode.values()) {
			tfegn.setupNode();
		}

	}
	
	
	/**
	 * Creates all the EqGraphNodes that are needed for instances of this TfStateBuilder.
	 * 
	 * (new) plan for this method:
	 * <ul>
	 *  <li> every EqNode that is visible in the current scope gets at least one node
	 *      (special case context switch: ..?)
	 *  <li> if an EqNode does not have a corresponding term in an equation in the TransFormula then we create a 
	 *       through-node for it.
	 *  <li> if an EqNode does have a corresponding term in the TransFormula,
	 *   <ul>
	 *    <li> create the according EqGraphNode
	 *    <li> if the term is involved in an array assignment, also create potentially missing in/out nodes 
	 *         (difficult case: composite node with mixed in/out status. The topmost symbol, i.e. the array, is 
	 *          important. The rest keeps its in/out status. E.g if in a[i], a is in, i is out, and we encounter the 
	 *          equality "a = a'" where a' is a's out-version, then we create a'[i] with i unchanged..
	 *          reason: for an array equality we need to equate the same index-values)
	 *   </ul>
	 *  <li> create a node for each auxVar in the TransFormula
	 * </ul> 
	 * 
	 * Algorithmically, we start by creating the nodes with terms in the TransFormula, then we create those for array
	 * equations. Afterwards we fill up with through-nodes. Last we create nodes for auxVars (it does not matter when we
	 *  do that).
	 * 
	 * Steps 1-3 are concerned with terms in the TransFormula.
	 * 
	 * @param preAnalysis
	 * @param allConstantEqNodes
	 */
	private void createEqGraphNodes(final VPDomainPreanalysis preAnalysis, final Set<EqNode> allConstantEqNodes) {
		
		/*
		 * collect (dis)equality subterms
		 */
		final Set<ApplicationTerm> xQualities =
				new ApplicationTermFinder(new HashSet<>(Arrays.asList(new String[] { "=", "distinct" })), false)
						.findMatchingSubterms(mTransFormula.getFormula());

		/*
		 * Step 1a. construct element wrappers, for non-array equations 
		 * (do this first because the array equations should only create EqGraphNodes that are not created anyway..)
		 */
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
		 * new: Handling array equalities separately is not necessary, because we will create EqGraphNodes for every 
		 *  EqNode that is in scope anyway such that both in and out are covered (either through an in- and an out-node
		 *  or through a through-node)
		 */
		
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
		 * 2. variables in the TransFormula that we have an EqNode for (outside of array accesses)
		 */
		for (final Entry<TermVariable, IProgramVar> en : VPDomainHelpers
				.computeProgramVarMappingFromTransFormula(mTransFormula).entrySet()) {

			// note: we can use .getEqNode(..) with an empty map here, because we are using the normalized 
			// TermVariable/ApplicationTerm from the ProgramVarOrConst
			if (preAnalysis.getEqNode(en.getValue().getTerm(), Collections.emptyMap()) == null) {
				// we don't track that variable
				continue;
			}
			getOrConstructElementWrapper(en.getKey());
		}
		
		/*
		 * 3. the auxVars of the TransFormula
		 */
		for (final TermVariable auxVar : mTransFormula.getAuxVars()) {
			getOrConstructElementWrapper(auxVar);
		}
		
		/*
		 * 4. Now we have finished with the terms in the TransFormula and fill up with EqGraphNodes for everything that
		 * is tracked, and in scope.
		 * (TODO: context switches)
		 */
		if (mAction instanceof IInternalAction) {
			final String proc = mAction.getPrecedingProcedure();
			
			for (EqNode eqNode : mPreAnalysis.getEqNodesForScope(proc)) {
				/*
				 * the boolean argument should not matter here.. right?..., i.e. if the node is freshly constructed, it
				 * is THROUGH no matter what the flag is set to 
				 */
//				getOrConstructMissingEqGraphNodes(eqNode);
			}
		}
	}
	
	/**
	 * Plan: 
	 * <ul>
	 *  <li> as input we get an IArrayWrapper, right now we just take its base array (e.g. for (store a i x) we take a) 
	 *    --> this might be optimized further perhaps 
	 *  <li> we look up which indices we track for that array (from
	 * preAnalysis), i.e., which indices of that array our states talk about 
	 *  <li> for each of these EqFunctionNodes we
	 * build an EqGraphNode, which has an in/out/through status compatible with the array 
	 *  <li> there may be some EqGraphNodes constructed in an earlier step (for a Term that occurs in the TransFormula) 
	 *    that we can use for this, however we usually will have to introduce special EqGraphNodes for this. 
	 *  <li> if the array is "in" in the given TransFormula, its corresponding EqGraphNode including all its descendants 
	 *    needs to be inOrThrough analogously if the array is "out" if the array is "through", then we need both 
	 *    versions for each functionNode:
	 * 	    inOrThrough and outOrThrough 
	 *  <li> .. the array could also be an auxVar --> TODO --> there might be other strategies to choose the nodes..
	 * </ul>
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
				assert newNode.mNodeIdentifier.getEqNode() == functionNode;
				assert newNode.mNodeIdentifier.isInOrThrough();
			}

			if (arrayId.isOutOrThrough()) {
				// ensure that we have an outOrThrough node for functionNode

				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newNode =
						getOrConstructInOrOutOrThroughEqGraphNode(functionNode, false);
				assert newNode.mNodeIdentifier.getEqNode() == functionNode;
				assert newNode.mNodeIdentifier.isOutOrThrough();
			}

			final ArrayInOutStatus targetInOutStatus = arrayId.getInOutStatus();
			if (targetInOutStatus == ArrayInOutStatus.AUX) {
				assert false : "TODO: treat this case";
			}
		}
	}

	/**
	 * Method for creating the nodes that are only introduced for an array equality. Their creation has to dynamically
	 * adapt to which in/out/through version of a node is already present and complement that. 
	 * (i.e. if no version of the node is present, then create through, otherwise create in or out according to the 
	 *  given parameter)
	 * 
	 * @param eqNode
	 * @param inOrThroughOrOutOrThroughChooseIn
	 * @return
	 */
	private EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getOrConstructInOrOutOrThroughEqGraphNode(
			final EqNode eqNode, final boolean inOrThroughOrOutOrThroughChooseIn) {

		return null;
//		final VPTfNodeIdentifier resultNodeId = inOrThroughOrOutOrThroughChooseIn
//				? mEqNodeToInOrThroughTfNodeId.get(eqNode) : mEqNodeToOutOrThroughTfNodeId.get(eqNode);
//
//		if (resultNodeId != null) {
//			// we already have an EqGraphNode for EqFunctionNode
//			assert inOrThroughOrOutOrThroughChooseIn ? resultNodeId.isInOrThrough() : resultNodeId.isOutOrThrough();
//			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> result = mNodeIdToEqGraphNode.get(resultNodeId);
//			assert result != null;
//			return result;
//		}
//		
//		if (eqNode.isConstant()) {
//			VPTfNodeIdentifier newNodeId = getNodeIdentifier(eqNode, Collections.emptyMap(), Collections.emptyMap());
//			assert newNodeId != null;
//			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newEqGraphNode = new EqGraphNode<>(newNodeId);
//
//			/*
//			 * register fresh node
//			 */
//			mNodeIdToEqGraphNode.put(newNodeId, newEqGraphNode);
//			return newEqGraphNode;
//		}
//
//		if (eqNode instanceof EqFunctionNode) {
//			final EqFunctionNode functionNode = (EqFunctionNode) eqNode;
//
//			final VPTfArrayIdentifier arrayId =
//					getOrConstructArrayIdentifier(functionNode.getFunction(), inOrThroughOrOutOrThroughChooseIn);
//
//			/*
//			 * the new EqGraphNode must be a function node with - function "arrayId" - arguments with inOutStatus In or
//			 * Through (those need to be getOrConstructed recursively, as any descendant may already be present or
//			 * not..)
//			 */
//
//			// obtain index vector for the new EqGraphNode
//			final List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> indexVector = new ArrayList<>();
//			final Map<IProgramVar, TermVariable> newInVars = new HashMap<>();
//			final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>();
//			for (final EqNode arg : functionNode.getArgs()) {
//				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> indexVectorElement =
//						getOrConstructInOrOutOrThroughEqGraphNode(arg, inOrThroughOrOutOrThroughChooseIn);
//				newInVars.putAll(indexVectorElement.mNodeIdentifier.getInVars());
//				newOutVars.putAll(indexVectorElement.mNodeIdentifier.getOutVars());
//				indexVector.add(indexVectorElement);
//			}
//
//			// obtain new EqGraphNode
//			newInVars.putAll(arrayId.getInVars());
//			newOutVars.putAll(arrayId.getOutVars());
//			final VPTfNodeIdentifier newNodeId = getNodeIdentifier(functionNode, newInVars, newOutVars);
//
//			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newFunctionEqGraphNode =
//					new EqGraphNode<>(newNodeId);
//			// getOrConstructEqGraphNode(newNodeId);
//
//			// update ccchild/parent fields
//			newFunctionEqGraphNode.addToCcchild(arrayId, indexVector);
//
//			for (final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> itn : indexVector) {
//				itn.addToCcpar(newFunctionEqGraphNode);
//			}
//
//			/*
//			 * register fresh node
//			 */
//			mNodeIdToEqGraphNode.put(newNodeId, newFunctionEqGraphNode);
//			mArrayIdToFunctionNodes.addPair(arrayId, newNodeId);
////			if (newNodeId.isOutOrThrough()) {
////				mOutNodes.add(newFunctionEqGraphNode);
////			}
//
//			assert newFunctionEqGraphNode != null;
//			return newFunctionEqGraphNode;
//		}
//		
//		// we are looking for a non-function node
//		
//		VPTfNodeIdentifier newNodeId;
//
//		boolean hasIn = false;
//		boolean hasOut = false;
//
//		for (final IProgramVar eqNodeVar : eqNode.getVariables()) {
//			if (mTransFormula.getInVars().containsKey(eqNodeVar)) {
//				hasIn = true;
//			}
//			if (mTransFormula.getOutVars().containsKey(eqNodeVar)) {
//				hasOut = true;
//			}
//		}
//
//		if (inOrThroughOrOutOrThroughChooseIn) {
//			// we need to create an inOrThrough node
//			if (!hasOut) {
//				// we create a through id
//				newNodeId = new VpTfExtraNodeIdentifier(eqNode, TfNodeInOutStatus.THROUGH);
//				mEqNodeToInOrThroughTfNodeId.put(eqNode, newNodeId);
//				mEqNodeToOutOrThroughTfNodeId.put(eqNode, newNodeId);
//			} else {
//				// we create an in id
//				newNodeId = new VpTfExtraNodeIdentifier(eqNode, TfNodeInOutStatus.IN);
//				mEqNodeToInOrThroughTfNodeId.put(eqNode, newNodeId);
//			}
//		} else {
//			// we need to create an outOrThrough node
//			if (!hasIn) {
//				// we create a through id
//				newNodeId = new VpTfExtraNodeIdentifier(eqNode, TfNodeInOutStatus.THROUGH);
//				mEqNodeToInOrThroughTfNodeId.put(eqNode, newNodeId);
//				mEqNodeToOutOrThroughTfNodeId.put(eqNode, newNodeId);
//			} else {
//				// we create an out id
//				newNodeId = new VpTfExtraNodeIdentifier(eqNode, TfNodeInOutStatus.OUT);
//				mEqNodeToOutOrThroughTfNodeId.put(eqNode, newNodeId);
//			}
//		}
//		final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newEqGraphNode = new EqGraphNode<>(newNodeId);
//
//		/*
//		 * register fresh node
//		 */
//		mNodeIdToEqGraphNode.put(newNodeId, newEqGraphNode);
//
//		assert newEqGraphNode != null;
//		return newEqGraphNode;
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
	 * Construct a "normal" (i.e. non-AuxVar-) EqGraphNode.
	 * 
	 * An EqGraphNode is given by an EqNode and an inVar/outVar signature (see also: VPTfNodeIdentifier).
	 * 
	 * If the EqNode is a EqFunctionNode, this method also creates EqGraphNodes for all sub-nodes with the corresponding
	 * projected signature.
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

		/*
		 * set ccchild/ccpar fields
		 */
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

		/*
		 * register new node
		 */
		mNodeIdToEqGraphNode.put(nodeIdentifier, result);
//		if (nodeIdentifier.isOutOrThrough()) {
//			mOutNodes.add(result);
//		}

		return result;
	}
	
	private VPTfNodeIdentifier getNodeIdentifier(final EqNode eqNode, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		VPTfNodeIdentifier result = mNonAuxVarNodeIds.get(eqNode, inVars, outVars);

		if (result == null) {
			result = new VPTfNodeIdentifier(eqNode, inVars, outVars, this);
			mNonAuxVarNodeIds.put(eqNode, inVars, outVars, result);
			mAllNodeIds.add(result);
//			if (result.isInOrThrough()) {
//				mEqNodeToInOrThroughTfNodeId.put(eqNode, result);
//			}
//			if (result.isOutOrThrough()) {
//				mEqNodeToOutOrThroughTfNodeId.put(eqNode, result);
//			}
		}
		return result;
	}

	private VPAuxVarNodeIdentifier getAuxVarNodeIdentifier(final TermVariable tv) {
		VPAuxVarNodeIdentifier result = mAuxVarNodeIds.get(tv);
		if (result == null) {
			result = new VPAuxVarNodeIdentifier(tv);
			mAuxVarNodeIds.put(tv, result);
			mAllNodeIds.add(result);
		}
		return result;
	}
	
	
	/**
	 * Looks up which array identifiers we already have constructed for the given array (given as pvoc).
	 *  <li> If we have a through, does nothing, 
	 *  <li> if we have in and out, does nothing,
	 *  <li> if we have only in/out, construct the other
	 *  <li> if we have neither, constructs a through array id
	 * 
	 * @param array
	 * @return
	 */
	private void constructMissingArrayIdentifier(final IProgramVarOrConst array) {
		boolean foundOut = false;
		boolean foundIn = false;
		for (Triple<Pair<IProgramVar, TermVariable>, Pair<IProgramVar, TermVariable>, VPTfArrayIdentifier> en : 
			mPvocToInVarToOutVarToArrayIdentifier.get(array).entrySet()) {
			assert en.getThird() != null;
			if (en.getFirst() != null && en.getSecond() != null) {
				// found a through array id --> do nothing, done
				return;
			} else if (en.getFirst() == null && en.getSecond() != null) {
				// found an out array id
				foundOut = true;
			} else if (en.getFirst() != null && en.getSecond() == null) {
				// found an in array id
				foundIn = true;
			} else {
				assert en.getFirst() == null && en.getSecond() == null;
				assert false : "we have stored an array id that is neither in nor out nor through??";
			}	
		}
		
	
		final Pair<IProgramVar, TermVariable> ivOvPair = new Pair<>((IProgramVar) array, null);
		
		// have not found a through node, checking if in/out is missing
		if (foundOut && foundIn) {
			return;
		} else if (!foundOut) {
			getOrConstructArrayIdentifier(array, null, ivOvPair);
		} else if (!foundIn) {
			getOrConstructArrayIdentifier(array, ivOvPair, null);
	 	} else {
	 		assert !foundOut && !foundIn;
			getOrConstructArrayIdentifier(array, ivOvPair, ivOvPair);
	 	}
		
//		Map<IProgramVar, TermVariable> inVars = null;
//		Map<IProgramVar, TermVariable> outVars = null;
//		return getOrConstructArrayIdentifier(array, inVars, outVars);
	}

	
	/**
	 * Looks up which array identifiers we already have constructed for the given array (given as pvoc).
	 * Then
	 *  <li> if inOrThroughOrOutOrThroughChooseIn: if we have a through array id, return it, if we have an in arrayid, 
	 *    return it, if we only have an out array id, return a fresh in array id, if we have no array id, return a fresh
	 *     through array id
	 *  <li> if !inOrThroughOrOutOrThroughChooseIn: analogous
	 * 
	 * @param array
	 * @param inOrThroughOrOutOrThroughChooseIn
	 * @return
	 */
	private VPTfArrayIdentifier getOrConstructArrayIdentifier(final IProgramVarOrConst array,
			final boolean inOrThroughOrOutOrThroughChooseIn) {
		
		Pair<IProgramVar, TermVariable> inVars = null;
		Pair<IProgramVar, TermVariable> outVars = null;
		
		for (Triple<Pair<IProgramVar, TermVariable>, Pair<IProgramVar, TermVariable>, VPTfArrayIdentifier> en : 
			mPvocToInVarToOutVarToArrayIdentifier.get(array).entrySet()) {
			assert en.getThird() != null;
			if (en.getFirst() != null && en.getSecond() != null) {
				// found a through array id
				return en.getThird();
			} else if (en.getFirst() == null && en.getSecond() != null) {
				// found an out array id
				if (inOrThroughOrOutOrThroughChooseIn) {
					inVars = new Pair<>((IProgramVar) array, null);
				} else {
					return en.getThird();
				}
			} else if (en.getFirst() != null && en.getSecond() == null) {
				// found an in array id
				if (inOrThroughOrOutOrThroughChooseIn) {
					return en.getThird();
				} else {
					outVars = new Pair<>((IProgramVar) array, null);
				}
			} else {
				assert en.getFirst() == null && en.getSecond() == null;
				assert false : "we have stored an array id that is neither in nor out nor through??";
			}
			
		}
		
		return getOrConstructArrayIdentifier(array, inVars, outVars);

//		if (array instanceof IProgramVar) {
//			final VPTfArrayIdentifier earlyResult = inOrThroughOrOutOrThroughChooseIn
//					? mProgramVarToInOrThroughArrayId.get(array) : mProgramVarToOutOrThroughArrayId.get(array);
//			if (earlyResult != null) {
//				assert inOrThroughOrOutOrThroughChooseIn ? earlyResult.isInOrThrough() : earlyResult.isOutOrThrough();
//				assert earlyResult.getProgramVarOrConst() == array;
//				return earlyResult;
//			}
//
//			// tvIn != null means that array is an inVar in mTransFormula, analogously for tvOut
//			final TermVariable tvIn = mTransFormula.getInVars().get(array);
//			final TermVariable tvOut = mTransFormula.getOutVars().get(array);
//
//			if (tvIn != null && inOrThroughOrOutOrThroughChooseIn) {
//				/*
//				 * the TransFormula has an inVar for array and we want inOrThrough --> retrieve the corresponding
//				 * arrayId
//				 */
//				final VPTfArrayIdentifier result = getOrConstructArrayIdentifier(tvIn);
//				assert inOrThroughOrOutOrThroughChooseIn ? result.isInOrThrough() : result.isOutOrThrough();
//				assert result.getProgramVarOrConst() == array;
//				return result;
//			} else if (tvOut != null && !inOrThroughOrOutOrThroughChooseIn) {
//				/*
//				 * the TransFormula has an outVar for array and we want outOrThrough --> retrieve the corresponding
//				 * arrayId
//				 */
//				final VPTfArrayIdentifier result = getOrConstructArrayIdentifier(tvOut);
//				assert inOrThroughOrOutOrThroughChooseIn ? result.isInOrThrough() : result.isOutOrThrough();
//				assert result.getProgramVarOrConst() == array;
//				return result;
//			} else {
//				/*
//				 * there is no TermVariable in the TransFormula with the inOrThrough-status we are looking for --> we
//				 * need an ArrayId especially for this purpose --> whether the new ArrayId we create is in/out or
//				 * through depends on inVars/outVars, too: if we need an inOrThrough id, and there is an
//				 * out-TermVariable for the array, we create an in-Id, otherwise we create a through-Id (and vice versa
//				 * for outOrThrough)
//				 */
//				if (inOrThroughOrOutOrThroughChooseIn) {
//					if (tvOut == null) {
//						// we create a through id
//						final VPTfArrayIdentifier newId = new VPTfExtraArrayIdentifier(array, ArrayInOutStatus.THROUGH);
//						mProgramVarToInOrThroughArrayId.put((IProgramVar) array, newId);
//						mProgramVarToOutOrThroughArrayId.put((IProgramVar) array, newId);
//
//						assert inOrThroughOrOutOrThroughChooseIn ? newId.isInOrThrough() : newId.isOutOrThrough();
//						assert newId.getProgramVarOrConst() == array;
//						return newId;
//					}
//					// we create an in id
//					final VPTfArrayIdentifier newId = new VPTfExtraArrayIdentifier(array, ArrayInOutStatus.IN);
//					mProgramVarToOutOrThroughArrayId.put((IProgramVar) array, newId);
//					assert inOrThroughOrOutOrThroughChooseIn ? newId.isInOrThrough() : newId.isOutOrThrough();
//					assert newId.getProgramVarOrConst() == array;
//					return newId;
//				}
//				if (tvIn == null) {
//					// we create a through id
//					final VPTfArrayIdentifier newId = new VPTfExtraArrayIdentifier(array, ArrayInOutStatus.THROUGH);
//					mProgramVarToInOrThroughArrayId.put((IProgramVar) array, newId);
//					mProgramVarToOutOrThroughArrayId.put((IProgramVar) array, newId);
//					assert inOrThroughOrOutOrThroughChooseIn ? newId.isInOrThrough() : newId.isOutOrThrough();
//					assert newId.getProgramVarOrConst() == array;
//					return newId;
//				}
//				// we create an out id
//				final VPTfArrayIdentifier newId = new VPTfExtraArrayIdentifier(array, ArrayInOutStatus.OUT);
//				mProgramVarToInOrThroughArrayId.put((IProgramVar) array, newId);
//				assert inOrThroughOrOutOrThroughChooseIn ? newId.isInOrThrough() : newId.isOutOrThrough();
//				assert newId.getProgramVarOrConst() == array;
//				return newId;
//			}
//		}
//		// array is not a variable
//		final VPTfArrayIdentifier result =
//				getOrConstructArrayIdentifier(array, Collections.emptyMap(), Collections.emptyMap());
//		assert inOrThroughOrOutOrThroughChooseIn ? result.isInOrThrough() : result.isOutOrThrough();
//		assert result.getProgramVarOrConst() == array;
//		return result;
	}

	/**
	 * Obtains the VPTfArrayIdentifier for the given term.
	 * The term is a subterm of the transition formula of the current TfStateBuilder.
	 * 
	 * Details:
	 *  We are looking for an array id based on a Term in the transition formula, thus we don't need to look for an
	 *  array id that was created "extra", i.e., for handling an array equality or for passing through information
	 *  about something that is just skipped by the TransFormula.
	 *  
	 *  @param term the subterm of mTransformula that we are looking for an arrayIdentifier for
	 *  @return 
	 */
	public VPTfArrayIdentifier getOrConstructArrayIdentifier(final Term term) {
		assert new ContainsSubterm(term).containsSubterm(mTransFormula.getFormula()) : "(see comments)";
		/*
		 * an array id is identified by a IProgramVarOrConst and inVar/outVar information
		 * Note: We don't need to take this stateBuilder's inVars/outVars here, because we assume that the argument 
		 *  term is a subterm of the current transition formula.
		 */
		return getOrConstructArrayIdentifier(
				mPreAnalysis.getIProgramVarOrConstOrLiteral(term,
						VPDomainHelpers.computeProgramVarMappingFromTransFormula(mTransFormula)),
				VPDomainHelpers.projectToTerm(mTransFormula.getInVars(), term),
				VPDomainHelpers.projectToTerm(mTransFormula.getOutVars(), term));
	}

	/**
	 * A VPTfArrayIdentifier (and thus an array term inside a transition formula) is identified by a IProgramVarOrConst 
	 * together with inVar/outVar information.
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

		/*
		 *  Note: need to use containsKey, because we allow null-values (and could not distinguish between "not
		 *   in the map" and "has a null value", by using .get(function) as usual.
		 */
		if (inVars.containsKey(function)) {
			inVar = new Pair<>((IProgramVar) function, inVars.get(function));
		}
		if (outVars.containsKey(function)) {
			outVar = new Pair<>((IProgramVar) function, outVars.get(function));
		}
		return getOrConstructArrayIdentifier(function, inVar, outVar);
	}


	/**
	 * Standard map-lookup/update method used by the other getOrConstructArrayIdentifier methods.
	 * 
	 * @param function
	 * @param inVar
	 * @param outVar
	 * @return
	 */
	private VPTfArrayIdentifier getOrConstructArrayIdentifier(final IProgramVarOrConst function,
			Pair<IProgramVar, TermVariable> inVar, Pair<IProgramVar, TermVariable> outVar) {
		VPTfArrayIdentifier result = mPvocToInVarToOutVarToArrayIdentifier.get(function, inVar, outVar);

		if (result == null) {
			result = new VPTfArrayIdentifier(function, inVar, outVar);
			mPvocToInVarToOutVarToArrayIdentifier.put(function, inVar, outVar, result);
		}
		return result;
	}
	


	public VPTfStateBuilder create() {
//		/*
//		 * the out nodes should be exactly all nodes that are "outOrThrough"
//		 */
//		assert mNodeIdToEqGraphNode.values().containsAll(mOutNodes);
//		assert mOutNodes.containsAll(mNodeIdToEqGraphNode.values().stream()
//				.filter(node -> node.mNodeIdentifier.isOutOrThrough())
//				.collect(Collectors.toSet()));
		
		final Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> outNodes = mNodeIdToEqGraphNode.values()
				.stream()
				.filter(node -> node.mNodeIdentifier.isOutOrThrough())
				.collect(Collectors.toSet());
		
		/*
		 * Generate disequality set for constants 
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
		final VPTfStateBuilder result = new VPTfStateBuilder(mPreAnalysis, mTfStatePreparer, mAction, mInVars, mOutVars, 
				mAllNodeIds, mNodeIdToEqGraphNode, mTermToArrayWrapper, mTermToElementWrapper, disEqualitySet, 
				outNodes, mArrayIdToFunctionNodes);

		assert result.isTopConsistent();
		return result;
	}	
	
	class WrapperFactory {
		/**
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
									eqNode.getVariables())).mNodeIdentifier;

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
		
		private TransFormula getTransFormula() {
			return mTransFormula;
		}

		private VPDomainPreanalysis getPreAnalysis() {
			return mPreAnalysis;
		}
	}
	
}
