package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqAtomicBaseNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunctionNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNonAtomicBaseNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IArrayWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IElementWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.SelectTermWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.StoreTermWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPAuxVarNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfArrayIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfStateBuilder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
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

	private VPTfStateBuilderPreparer mTfStatePreparer;
	private VPDomainPreanalysis mPreAnalysis;
	private TransFormula mTransFormula;
	
	private Set<VPTfNodeIdentifier> mAllNodeIds = new HashSet<>();
	private Map<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> mNodeIdToEqGraphNode =
			new HashMap<>();
	private Map<TermVariable, VPAuxVarNodeIdentifier> mAuxVarNodeIds = new HashMap<>();
	private HashRelation<VPTfArrayIdentifier, VPTfNodeIdentifier> mArrayIdToFunctionNodes = new HashRelation<>();
	
	
	private NestedMap3<EqNode, Map<IProgramVar, TermVariable>, Map<IProgramVar, TermVariable>, VPTfNodeIdentifier> 
		mNonAuxVarNodeIds = new NestedMap3<>();
	
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
			final VPTfStateBuilderPreparer tfStatePreparer, final IAction action,//final TransFormula tf,
			final Set<EqNode> allConstantEqNodes, final Set<IProgramVarOrConst> inVars, 
			final Set<IProgramVarOrConst> outVars) {
		mTfStatePreparer = tfStatePreparer;
		mPreAnalysis = preAnalysis;
		mAction = action;
		mTransFormula = action.getTransformula();
		mInVars = inVars;
		mOutVars = outVars;

		createEqGraphNodes(preAnalysis);

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
	private void createEqGraphNodes(final VPDomainPreanalysis preAnalysis) {
		
		/*
		 * collect (dis)equality subterms
		 */
		final Set<ApplicationTerm> xQualities =
				new ApplicationTermFinder(new HashSet<>(Arrays.asList(new String[] { "=", "distinct" })), false)
						.findMatchingSubterms(mTransFormula.getFormula());
		
		/*
		 * we track here, which arrays are equated in the formula
		 */
		HashRelation<VPTfArrayIdentifier, VPTfArrayIdentifier> equatedArrays = new HashRelation<>();

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
				final IArrayWrapper aw1 = getOrConstructArrayWrapper(lhs);
				final IArrayWrapper aw2 = getOrConstructArrayWrapper(rhs);
				equatedArrays.addPair(aw1.getBaseArray(), aw2.getBaseArray());
				equatedArrays.addPair(aw2.getBaseArray(), aw1.getBaseArray());
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
		 */
		if (mAction instanceof IInternalAction) {
			final String proc = mAction.getPrecedingProcedure();
			
			for (EqNode eqNode : mPreAnalysis.getEqNodesForScope(proc)) {
				getOrConstructThroughNode(eqNode, equatedArrays);
			}
		} else {
			/*
			 *  context switch case (Call or Return)
			 *  we construct nodes for the intersection of the scopes
			 *  (we might want to carry over relations to globals, essentially)
			 */
			for (EqNode eqNode : mPreAnalysis.getEqNodesForScope(mAction.getPrecedingProcedure(), 
					mAction.getSucceedingProcedure())) {
				getOrConstructThroughNode(eqNode, equatedArrays);
			}
		}
	}

	/**
	 * Gets or constructs nodes for the given eqNode.
	 * 
	 * For function nodes this works recursively on the children.
	 * 
	 * What is constructed depends on which nodes are already present:
	 * <ul>
	 *  <li> If any version of the given EqNode is present, we do nothing.
	 *  <li> If the given EqNode is constant, we can construct it easily as it will be "through".
	 *  <li> Otherwise and if the given EqNode is atomic, we create a "through" version of it.
	 *  <li> Otherwise and if the given EqNode is a function node, we create a "through" version of it, we have the 
	 *     interesting case.
 	 *   <ul>
 	 *    <li> we check for all children of the top-EqNode what we already have (recursive call)
 	 *    <li> we may get back an inOrThrough-version, an outOrThrough-version, or both
 	 *    <li> we collect the matching versions for all the components
 	 *    <li> we check which variants of the function symbol we already have and depending on those we build
 	 *       one ore two function nodes from the children and the function symbols.
	 *   </ul>
	 * </ul>
	 * 
	 * @param eqNode
	 * @param equatedArrays 
	 * @return
	 */
	private Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> getOrConstructThroughNode(EqNode eqNode, 
			HashRelation<VPTfArrayIdentifier, VPTfArrayIdentifier> equatedArrays) {
		final Set<VPTfNodeIdentifier> alreadyConstructed = getAlreadyConstructedInOutNodeIds(eqNode);
		assert alreadyConstructed.size() <= 2;
		
		if (!alreadyConstructed.isEmpty()) {
			// already have EqNode for this (in, out, both, or through) --> do nothing
			return alreadyConstructed.stream()
					.map(nodeId -> getOrConstructEqGraphNode(nodeId))
					.collect(Collectors.toSet());
		}
		
		if (eqNode.isConstant()) {
			return Collections.singleton(
					getOrConstructEqGraphNode(eqNode, Collections.emptyMap(), Collections.emptyMap()));
		}

		if (eqNode instanceof EqFunctionNode) {
			final EqFunctionNode eqfn = (EqFunctionNode) eqNode;

			/*
			 * For each of this EqFunctionNodes' arguments, get the in/out/through nodes we already have or construct
			 * the through node freshly.
			 * (makes recursive call to this method)
			 */
			final List<Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>>> children = eqfn.getArgs().stream()
					.map(childEqNode -> getOrConstructThroughNode(childEqNode, equatedArrays))
					.collect(Collectors.toList());
			
			/*
			 * Separate the children into inOrThrough and outOrThrough.
			 * If for either of these we cannot get the complete argument list, we won't construct the corresponding
			 * version for the current input EqFunctionNode, to indicate this, we set the corresponding childrenList
			 *  to null in this step.
			 */
			List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> inOrThroughChildren = new ArrayList<>();
			List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> outOrThroughChildren = new ArrayList<>();
			for (Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> child : children) {
				final Iterator<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> it = child.iterator();
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> firstChild = it.next();
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> secondChild = it.hasNext() ? it.next() : null;
				assert !firstChild.mNodeIdentifier.isInOrThrough() 
					|| secondChild == null || secondChild.mNodeIdentifier.isOutOrThrough();
				assert secondChild == null || !secondChild.mNodeIdentifier.isInOrThrough() 
					|| firstChild.mNodeIdentifier.isOutOrThrough();
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> inChild = 
						firstChild.mNodeIdentifier.isInOrThrough() ? firstChild : secondChild;
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> outChild = 
						firstChild.mNodeIdentifier.isOutOrThrough() ? firstChild : secondChild;
				
				if (inChild != null && inOrThroughChildren != null) {
					inOrThroughChildren.add(inChild);
				} else {
					inOrThroughChildren = null;
				}
				
				if (outChild != null && outOrThroughChildren != null) {
					outOrThroughChildren.add(outChild);
				} else {
					outOrThroughChildren = null;
				}
			}
			

			
			// build node for inOrThrough case
			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> inOrThroughResult = 
					constructThroughFunctionNodeIfMissing(eqfn, inOrThroughChildren, equatedArrays, true);

			// build node for outOrThrough case
			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> outOrThroughResult = 
					constructThroughFunctionNodeIfMissing(eqfn, outOrThroughChildren, equatedArrays, false);
			


			/*
			 * put the result into a set, return it
			 */
			final Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> result = new HashSet<>();
			if (inOrThroughResult != null) {
				result.add(inOrThroughResult);
			}
			if (outOrThroughResult != null) {
				result.add(outOrThroughResult);
			}
			return result;
		} else if (eqNode instanceof EqNonAtomicBaseNode) {
			// (we may have to dive deeper to get to the base nodes)
			// TODO
//			return null;
			throw new AssertionError("TODO");
		} else if (eqNode instanceof EqAtomicBaseNode){
			// construct a fresh "through" version of the node
			assert eqNode.getVariables().size() == 1 : "we have a non-constant atomic base node, right?..";

			final IProgramVar var = eqNode.getVariables().iterator().next();

			Map<IProgramVar, TermVariable> map = Collections.singletonMap(var, null);
			VPTfNodeIdentifier newNodeId = getOrConstructNodeIdentifier(eqNode, map, map);
			
			return Collections.singleton(getOrConstructEqGraphNode(newNodeId));
		} else {
			throw new AssertionError("unexpected case!");
		}
		
	}


	/**
	 * compute the signature "so far" (i.e. without this EqFunctionNode's symbol) from the in/outChildren,
	 * then extend it to the signature for the result node and construct that result node.
	 * @param equatedArrays 
	 */
	private EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> constructThroughFunctionNodeIfMissing(
			final EqFunctionNode eqfn, List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> xOrThroughChildren,
			HashRelation<VPTfArrayIdentifier, VPTfArrayIdentifier> equatedArrays, boolean chooseInOrThrough) {
		if (xOrThroughChildren == null) {
			return null;
		}
		
		final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> xOrThroughResult;

		Map<IProgramVar, TermVariable> childrenInVars = new HashMap<>();
		Map<IProgramVar, TermVariable> childrenOutVars = new HashMap<>();
		for (EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> inChild : xOrThroughChildren) {
			childrenInVars.putAll(inChild.mNodeIdentifier.getInVars());
			childrenOutVars.putAll(inChild.mNodeIdentifier.getOutVars());
		}
		childrenInVars = Collections.unmodifiableMap(childrenInVars);
		childrenOutVars = Collections.unmodifiableMap(childrenOutVars);

		final VPTfArrayIdentifier xOrThroughArrayId = 
				getArrayIdentifierConstructThroughIfMissing(eqfn.getFunction(), chooseInOrThrough);

		if (xOrThroughArrayId != null) {
			final Map<IProgramVar, TermVariable> inVars = new HashMap<>(childrenInVars);
			final Map<IProgramVar, TermVariable> outVars = new HashMap<>(childrenOutVars);
			inVars.putAll(xOrThroughArrayId.getInVars());
			outVars.putAll(xOrThroughArrayId.getOutVars());
			xOrThroughResult = getOrConstructEqGraphNode(eqfn, inVars, outVars);
		} else {
			/*
			 *  we only have an out version for the given function (/array) symbol 
			 *   --> we don't construct an inOrThrough node
			 */
			xOrThroughResult = null;
		}
		
		/*
		 * for array equations/extensionality we need an extra side effect here:
		 *  if our arrayId is equated with some other array in mTransFormula, then we want to add a node with the other
		 *  function symbol and the same children
		 */
		if (xOrThroughArrayId != null && equatedArrays.getDomain().contains(xOrThroughArrayId)) {
			
			final List<EqNode> childrenAsEqNodes = xOrThroughChildren.stream()
					.map(eqgn -> eqgn.mNodeIdentifier.getEqNode()).collect(Collectors.toList());
			
			for (VPTfArrayIdentifier otherArrayId : equatedArrays.getImage(xOrThroughArrayId)) {
				//for architectural reasons we need the EqNode here..
				final EqFunctionNode funcNode = mPreAnalysis.getEqFunctionNode(otherArrayId.getProgramVarOrConst(), 
						childrenAsEqNodes);
				if (funcNode == null) {
					// the function node we would need here is not tracked..
					continue;
				}
				final Map<IProgramVar, TermVariable> inVars = new HashMap<>(childrenInVars);
				final Map<IProgramVar, TermVariable> outVars = new HashMap<>(childrenOutVars);
				inVars.putAll(otherArrayId.getInVars());
				outVars.putAll(otherArrayId.getOutVars());
				getOrConstructEqGraphNode(funcNode, inVars, outVars);
			}
		}

		return xOrThroughResult;
	}

	private Set<VPTfNodeIdentifier> getAlreadyConstructedInOutNodeIds(EqNode eqNode) {
		
		final NestedMap2<Map<IProgramVar, TermVariable>, 
			Map<IProgramVar, TermVariable>, 
			VPTfNodeIdentifier> inVarsToOutVarsToNodeId = mNonAuxVarNodeIds.get(eqNode);
		if (inVarsToOutVarsToNodeId == null) {
			return Collections.emptySet();
		} else {
			Set<VPTfNodeIdentifier> result = new HashSet<>();
			for (Triple<Map<IProgramVar, TermVariable>, Map<IProgramVar, TermVariable>, VPTfNodeIdentifier> tr 
					: inVarsToOutVarsToNodeId.entrySet()) {
				result.add(tr.getThird());
			}
			assert result.size() <= 2;
			return result;
		}
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

		final VPTfNodeIdentifier nodeIdentifier = getOrConstructNodeIdentifier(eqNode, inVars, outVars);

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
				final VPTfNodeIdentifier argNodeId = getOrConstructNodeIdentifier(indexEqnode, argInVars, argOutVars);
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
		return result;
	}
	
	private VPTfNodeIdentifier getOrConstructNodeIdentifier(final EqNode eqNode, 
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		VPTfNodeIdentifier result = mNonAuxVarNodeIds.get(eqNode, inVars, outVars);

		if (result == null) {
			result = new VPTfNodeIdentifier(eqNode, inVars, outVars, this);
			mNonAuxVarNodeIds.put(eqNode, inVars, outVars, result);
			mAllNodeIds.add(result);
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
	 * Looks either for an inOrThrough-version or for an outOrThrough-version of the given array variable (depending
	 *  on the boolean input flag).
	 * <ul>
	 *  <li> if a fitting one already exists, returns it
	 *  <li> if neither exists, creates a through version for it
	 *  <li> if a not-fitting one already exists (e.g. out, if we want inOrThrough), returns null (!)
	 * </ul>
	 * 
	 * @param array
	 * @param inOrThroughOrOutOrThroughChooseIn
	 * @return
	 */
	private VPTfArrayIdentifier getArrayIdentifierConstructThroughIfMissing(final IProgramVarOrConst array,
			final boolean inOrThroughOrOutOrThroughChooseIn) {
		
		final NestedMap2<Pair<IProgramVar, TermVariable>, 
			Pair<IProgramVar, TermVariable>, 
			VPTfArrayIdentifier> inToOutToArrayId = mPvocToInVarToOutVarToArrayIdentifier.get(array);
		
		if (inToOutToArrayId == null) {
			/*
			 * We don't have an arrayId for the given array yet --> construct a through version!
			 */
			Pair<IProgramVar, TermVariable> pair = array instanceof IProgramVar ? 
					new Pair<>((IProgramVar) array, null) :
						null;
			return getOrConstructArrayIdentifier(array, pair, pair);
		}
		
		for (Triple<Pair<IProgramVar, TermVariable>, Pair<IProgramVar, TermVariable>, VPTfArrayIdentifier> en : 
			inToOutToArrayId.entrySet()) {
			assert en.getThird() != null;
			if (en.getFirst() != null && en.getSecond() != null) {
				// found a through array id
				return en.getThird();
			} else if (en.getFirst() == null && en.getSecond() != null) {
				// found an out array id
				if (inOrThroughOrOutOrThroughChooseIn) {
					return null;
				} else {
					return en.getThird();
				}
			} else if (en.getFirst() != null && en.getSecond() == null) {
				// found an in array id
				if (inOrThroughOrOutOrThroughChooseIn) {
					return en.getThird();
				} else {
					return null;
				}
			} else {
				assert en.getFirst() == null && en.getSecond() == null;
				throw new AssertionError("we have stored an array id that is neither in nor out nor through??");
			}
			
		}
		throw new AssertionError("does not happen, right?...");
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
				throw new AssertionError("missed case?");
			}
		}
		
		private TransFormula getTransFormula() {
			return mTransFormula;
		}

		private VPDomainPreanalysis getPreAnalysis() {
			return mPreAnalysis;
		}
	}
	
}
