package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

public class VPTransitionStateBuilder extends IVPStateOrTfStateBuilder<VPTfState, VPNodeIdentifier, VPArrayIdentifier> {
	
	private Set<IProgramVar> mVars = new HashSet<>();
	
	private Map<Term, VPNodeIdentifier> mTermToNodeId = new HashMap<>();
	private Map<VPNodeIdentifier, EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> mNodeIdToEqGraphNode = new HashMap<>();
	private	NestedMap3<EqNode, 
			Map<IProgramVar, TermVariable>, 
			Map<IProgramVar, TermVariable>, 
			VPNodeIdentifier> mNonAuxVarNodeIds = new NestedMap3<>();
	private Map<TermVariable, VPAuxVarNodeIdentifier> mAuxVarNodeIds = new HashMap<>();

	private HashRelation<VPArrayIdentifier, VPNodeIdentifier> mArrayIdToFunctionNodes = new HashRelation<>();

	private final TransFormula mTransFormula;

	public VPTransitionStateBuilder(VPDomainPreanalysis preAnalysis,
			TransFormula tf, Set<EqNode> allConstantEqNodes) {
		mTransFormula = tf;
		createEqGraphNodes(tf, preAnalysis, allConstantEqNodes);
		
		for (EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> tfegn : getAllEqGraphNodes()) {
			tfegn.setupNode();
		}
		assert isTopConsistent();
	}

	
	/**
	 * copy constructor
	 * @param builder
	 */
	public VPTransitionStateBuilder(VPTransitionStateBuilder builder) {
		super(builder);
		assert builder.isTopConsistent();
		mTransFormula = builder.mTransFormula;
		mVars = new HashSet<>(builder.mVars);
		// the nodeIdentifiers are shared between all "sibling" builders (i.e. builders for the same TransFormula)
		mTermToNodeId = new HashMap<>(builder.mTermToNodeId);
		mNonAuxVarNodeIds = builder.mNonAuxVarNodeIds.copy();
		mAuxVarNodeIds = new HashMap<>(builder.mAuxVarNodeIds);
		mArrayIdToFunctionNodes = builder.mArrayIdToFunctionNodes.copy();
		
		// nodes need to be deepcopied..
		mNodeIdToEqGraphNode = new HashMap<>();
		for (Entry<VPNodeIdentifier, EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> en : builder.mNodeIdToEqGraphNode.entrySet()) {
			EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> egnInOldState = en.getValue();
			final VPNodeIdentifier nodeId = en.getKey();
			final EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> newGraphNode = 
					new EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>(nodeId);
			assert newGraphNode != null;
			mNodeIdToEqGraphNode.put(nodeId, newGraphNode);
			assert !builder.mIsTop || newGraphNode.getRepresentative() == newGraphNode;		
		}

		for (Entry<VPNodeIdentifier, EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> en : builder.mNodeIdToEqGraphNode.entrySet()) {
			EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> egnInOldState = en.getValue();
			final VPNodeIdentifier nodeId = en.getKey();
			final EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> newGraphNode = 
					this.getEqGraphNode(nodeId);
			EqGraphNode.copyFields(egnInOldState, newGraphNode, this);
		}

		assert isTopConsistent();
	}


	private void createEqGraphNodes(
			TransFormula tf, VPDomainPreanalysis preAnalysis, Set<EqNode> allConstantEqNodes) {

		/*
		 * The EqGraphNodes we need for the given TransFormula can come from four sources:
		 *  1. array accesses in the TransFormula
		 *    --> we obtain them by the extraction methods of the MultiDimensionsalX classes
		 *  2. variables in the TransFormula (outside of array accesses)
		 *    --> we can see them in the invars and outvars of the TransFormula
		 *  3. constants in the TransFormula
		 *    --> we can just take the constant EqNodes from the preanalysis 
		 *    (is this more than necessary? maybe not: we have to carry over all 
		 *     relations to constants from the VPStates through the TransFormulas, even if they don't
		 *     occur in some TransFormula)
		 *  4. the auxVars of the Transformula
		 */
		
		
		Map<TermVariable, IProgramVar> tvToPvMap = 
				VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf);

		/*
		 * 1. array accesses in the TransFormula
		 */
		final List<MultiDimensionalSelect> mdSelectsAll =
				MultiDimensionalSelect.extractSelectShallow(tf.getFormula(), false);
		for (MultiDimensionalSelect mds : mdSelectsAll) {
			EqNode eqNode = preAnalysis.getEqNode(mds.getSelectTerm(), tvToPvMap);
			if (eqNode == null) {
				// we don't track that select (because we don't track the corresponding array)
				continue;
			}

			ApplicationTerm selectTerm = mds.getSelectTerm();
			
			getOrConstructEqGraphNode(
					eqNode, 
					VPDomainHelpers.projectToTerm(tf.getInVars(), selectTerm), 
					VPDomainHelpers.projectToTerm(tf.getOutVars(), selectTerm), 
					selectTerm);
		}
		final List<MultiDimensionalStore> mdStoresAll =
				MultiDimensionalStore.extractArrayStoresShallow(tf.getFormula());
		for (MultiDimensionalStore mds : mdStoresAll) {
			EqNode eqNode = preAnalysis.getEqNode(mds.getStoreTerm(), tvToPvMap);
			if (eqNode == null) {
				// we don't track that select (because we don't track the corresponding array)
				continue;
			}

			ApplicationTerm selectTerm = mds.getStoreTerm();
			
			getOrConstructEqGraphNode(
					eqNode, 
					VPDomainHelpers.projectToTerm(tf.getInVars(), selectTerm), 
					VPDomainHelpers.projectToTerm(tf.getOutVars(), selectTerm), 
					selectTerm); 
			
			EqNode storedValueNode = preAnalysis.getEqNode(mds.getValue(), tvToPvMap);
			getOrConstructEqGraphNode(
					storedValueNode, 
					VPDomainHelpers.projectToTerm(tf.getInVars(), mds.getValue()), 
					VPDomainHelpers.projectToTerm(tf.getOutVars(), mds.getValue()), 
					mds.getValue());
		}
		
		/*
		 * 2. variables in the TransFormula (outside of array accesses)
		 */
		for (Entry<TermVariable, IProgramVar> en : tvToPvMap.entrySet()) {
			EqNode varEqNode = preAnalysis.getEqNode(en.getValue().getTerm(), Collections.emptyMap());

			if (varEqNode == null) {
				// we don't track that variable
				continue;
			}
			
			getOrConstructEqGraphNode(
					varEqNode, 
					VPDomainHelpers.projectToTerm(tf.getInVars(), en.getKey()), 
					VPDomainHelpers.projectToTerm(tf.getOutVars(),  en.getKey()), 
					en.getKey());
		}
		
		/*
		 * 3. constants in the TransFormula
		 */
		for (EqNode constantEqNode : allConstantEqNodes) {
			assert constantEqNode.isConstant();
	
			// technical note: the constant select/store terms that occur in tf have been treated by
			//  step 1. already. -- therefore it should be ok to use EqNode.getTerm for the term argument of the 
			//  getOrConstruct method; because say we have a constant store in this formula, it has 
			//  already been put into the map.
			
			getOrConstructEqGraphNode(constantEqNode, 
					Collections.emptyMap(), 
					Collections.emptyMap(), 
					constantEqNode.getTerm(preAnalysis.getManagedScript()));
		}
		
		/*
		 * 4. the auxVars of the TransFormula
		 */
		for (TermVariable auxVar : tf.getAuxVars()) {
			getOrConstructEqGraphNode(null, 
					Collections.emptyMap(), 
					Collections.emptyMap(), 
					auxVar);
		}
	}
	
	public void merge(Term t1, Term t2) {
		EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> egn1 = mNodeIdToEqGraphNode.get(mTermToNodeId.get(t1));
		assert egn1 != null;
		EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> egn2 = mNodeIdToEqGraphNode.get(mTermToNodeId.get(t2));
		assert egn2 != null;
		
		merge(egn1, egn2);
		assert isTopConsistent();
	}
	
	private EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> getOrConstructEqGraphNode(
			final EqNode eqNode, 
			final Map<IProgramVar, TermVariable> inVars, 
			final Map<IProgramVar, TermVariable> outVars,
			final Term term) {
		if (eqNode == null) {
			// we have an AuxVar
			assert inVars.isEmpty();
			assert outVars.isEmpty();
			VPAuxVarNodeIdentifier nodeId = getAuxVarNodeIdentifier((TermVariable) term);
			mTermToNodeId.put(term, nodeId);
			EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> result = mNodeIdToEqGraphNode.get(nodeId);
			if (result == null) {
				result = new EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>(nodeId);
				mNodeIdToEqGraphNode.put(nodeId, result);
			}
			return result;
		}
		
		
		// we have a "normal" (i.e. non-AuxVar-) EqGraphNode
		
		VPNodeIdentifier nodeIdentifier = getNodeIdentifier(eqNode, inVars, outVars);
		mTermToNodeId.put(term, nodeIdentifier);

		EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> result = mNodeIdToEqGraphNode.get(nodeIdentifier);
		if (result != null) {
			return result;
		}

		/*
		 * the corresponding EqGraphNode has not yet been created
		 */
		
		result = new EqGraphNode<>(nodeIdentifier);
		mNodeIdToEqGraphNode.put(nodeIdentifier, result);
		
		if (eqNode instanceof EqFunctionNode) {
			EqFunctionNode eqFunctionNode = (EqFunctionNode) eqNode;
			
			ArrayIndex arrayIndex = extractArgumentsFromStoreOrSelect(term);
			
			assert eqFunctionNode.getArgs().size() == arrayIndex.size();
			
			List<EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> argNodes = new ArrayList<>();

			for (int i = 0; i < ((EqFunctionNode) eqNode).getArgs().size(); i++) {
				Term indexTerm = arrayIndex.get(i);
				EqNode indexEqnode = eqFunctionNode.getArgs().get(i);
				Map<IProgramVar, TermVariable> argInVars = VPDomainHelpers.projectToTerm(inVars, term);
				Map<IProgramVar, TermVariable> argOutVars = VPDomainHelpers.projectToTerm(outVars, term);
				EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> argNode = getOrConstructEqGraphNode(
						indexEqnode, 
						argInVars, 
						argOutVars, 
						indexTerm); 

				argNode.addToCcpar(result); // later EqGraphNode.setupNode() will make initCCPar out of this
				argNodes.add(argNode);
			}
			// later EqGraphNode.setupNode() will make initCcchild out of this:
			VPArrayIdentifier arrayId = new VPArrayIdentifier(
					VPDomainHelpers.getArrayTerm((ApplicationTerm) term));
			result.addToCcchild(arrayId, argNodes);
			
			mArrayIdToFunctionNodes.addPair(arrayId, nodeIdentifier);
		}
		
		
		return result;
	}
	


	private ArrayIndex extractArgumentsFromStoreOrSelect(Term term) {
		List<MultiDimensionalSelect> selects = MultiDimensionalSelect.extractSelectShallow(term, false);
		if (selects.size() > 0) {
			assert selects.size() == 1;
			return selects.get(0).getIndex();
		}
		List<MultiDimensionalStore> stores = MultiDimensionalStore.extractArrayStoresShallow(term);
		if (stores.size() > 0) {
			assert stores.size() == 1;
			return stores.get(0).getIndex();
		}
		assert false : "no select or store term inside term";
		return null;
	}


	
	@Override
	VPTfState build() {
		assert mTransFormula != null;
		assert mNodeIdToEqGraphNode != null;
		assert mTermToNodeId != null;
		assert mArrayIdToFunctionNodes != null;
		assert mDisEqualitySet != null;
		assert mVars != null;
		assert isTopConsistent();
		return new VPTfState(
				mTransFormula, 
				mNodeIdToEqGraphNode,
				mTermToNodeId,
				mArrayIdToFunctionNodes, 
				mDisEqualitySet, 
				mIsTop, 
				mVars);
	}


	@Override
	EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> getEqGraphNode(VPNodeIdentifier i) {
		return mNodeIdToEqGraphNode.get(i);
	}

	public void addVariables(Set<IProgramVar> variables) {
		mVars.addAll(variables);
	}
	
	public VPNodeIdentifier getNodeIdentifier(EqNode eqNode, 
			Map<IProgramVar, TermVariable> inVars, 
			Map<IProgramVar, TermVariable> outVars) {
		VPNodeIdentifier result = mNonAuxVarNodeIds.get(eqNode, inVars, outVars);
		
		if (result == null) {
			result = new VPNodeIdentifier(eqNode, inVars, outVars);
			mNonAuxVarNodeIds.put(eqNode, inVars, outVars, result);
		}
		return result;
	}
	
	public VPAuxVarNodeIdentifier getAuxVarNodeIdentifier(TermVariable tv) {
		VPAuxVarNodeIdentifier result = mAuxVarNodeIds.get(tv);
		if (result == null) {
			result = new VPAuxVarNodeIdentifier(tv);
			mAuxVarNodeIds.put(tv, result);
		}
		return result;
	}


	@Override
	Collection<EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> getAllEqGraphNodes() {
		return mNodeIdToEqGraphNode.values();
	}

	public VPNodeIdentifier getNodeId(Term value) {
		return mTermToNodeId.get(value);
	}

}
