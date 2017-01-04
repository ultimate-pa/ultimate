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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPTransFormulaStateBuilderPreparer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers.InOutStatus;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunctionNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPAuxVarNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfArrayIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class VPTfStateBuilder extends IVPStateOrTfStateBuilder<VPTfState, VPTfNodeIdentifier, VPTfArrayIdentifier> {
	
	private Set<IProgramVar> mVars = new HashSet<>();
	
	private Map<Term, VPTfNodeIdentifier> mTermToNodeId = new HashMap<>();
	private Map<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> mNodeIdToEqGraphNode = new HashMap<>();
	private	NestedMap3<EqNode, 
			Map<IProgramVar, TermVariable>, 
			Map<IProgramVar, TermVariable>, 
			VPTfNodeIdentifier> mNonAuxVarNodeIds = new NestedMap3<>();
	private Map<TermVariable, VPAuxVarNodeIdentifier> mAuxVarNodeIds = new HashMap<>();

	private HashRelation<VPTfArrayIdentifier, VPTfNodeIdentifier> mArrayIdToFunctionNodes = new HashRelation<>();

	private final TransFormula mTransFormula;
	
	
	VPTransFormulaStateBuilderPreparer mTfStatePreparer;
	
	NestedMap3<IProgramVarOrConst, 
		Pair<IProgramVar, TermVariable>,  
		Pair<IProgramVar, TermVariable>, 
		VPTfArrayIdentifier> mPvocToInVarToOutVarToArrayIdentifier = new NestedMap3<>();

	private final VPDomainPreanalysis mPreAnalysis;


	public VPTfStateBuilder(VPDomainPreanalysis preAnalysis,
			VPTransFormulaStateBuilderPreparer tfStatePreparer,
			TransFormula tf, Set<EqNode> allConstantEqNodes) {
		mTfStatePreparer = tfStatePreparer;
		mPreAnalysis = preAnalysis;
		mTransFormula = tf;
		createEqGraphNodes(preAnalysis, allConstantEqNodes);
		
		for (EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> tfegn : getAllEqGraphNodes()) {
			tfegn.setupNode();
		}
		
		/*
		 * Generate disequality set for constants
		 * TODO: do this more efficiently
		 */
		final Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> disEqualitySet = new HashSet<>();
		for (final VPTfNodeIdentifier node1 : mTermToNodeId.values()) {
			for (final VPTfNodeIdentifier node2 : mTermToNodeId.values()) {
				if (!node1.isLiteral() || !node2.isLiteral()) {
					continue;
				}
				if (!node1.equals(node2)) {
					disEqualitySet.add(new VPDomainSymmetricPair<>(node1, node2));
				}
			}
		}
		this.addDisEqualites(disEqualitySet);
		
		
		assert isTopConsistent();
	}

	
	/**
	 * copy constructor
	 * @param builder
	 */
	public VPTfStateBuilder(VPTfStateBuilder builder) {
		super(builder);
		assert builder.isTopConsistent();
		mPvocToInVarToOutVarToArrayIdentifier = builder.mPvocToInVarToOutVarToArrayIdentifier;
		mPreAnalysis = builder.mPreAnalysis;
		mTfStatePreparer = builder.mTfStatePreparer;
		mTransFormula = builder.mTransFormula;
		mVars = new HashSet<>(builder.mVars);
		// the arrayIdentifiers are shared between all "sibling" builders (i.e. builders for the same TransFormula)
		mPvocToInVarToOutVarToArrayIdentifier = builder.mPvocToInVarToOutVarToArrayIdentifier;
		// the nodeIdentifiers are shared between all "sibling" builders (i.e. builders for the same TransFormula)
		mTermToNodeId = new HashMap<>(builder.mTermToNodeId); // TODO: do we really need a fresh map here?? if yes, then also for the arrayId?
		mNonAuxVarNodeIds = builder.mNonAuxVarNodeIds.copy();
		mAuxVarNodeIds = new HashMap<>(builder.mAuxVarNodeIds);
		mArrayIdToFunctionNodes = builder.mArrayIdToFunctionNodes.copy();
		
		// nodes need to be deepcopied..
		mNodeIdToEqGraphNode = new HashMap<>();
		for (Entry<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> en : builder.mNodeIdToEqGraphNode.entrySet()) {
			EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> egnInOldState = en.getValue();
			final VPTfNodeIdentifier nodeId = en.getKey();
			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newGraphNode = 
					new EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>(nodeId);
			assert newGraphNode != null;
			mNodeIdToEqGraphNode.put(nodeId, newGraphNode);
			assert !builder.mIsTop || newGraphNode.getRepresentative() == newGraphNode;		
		}

		for (Entry<VPTfNodeIdentifier, EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> en : builder.mNodeIdToEqGraphNode.entrySet()) {
			EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> egnInOldState = en.getValue();
			final VPTfNodeIdentifier nodeId = en.getKey();
			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newGraphNode = 
					this.getEqGraphNode(nodeId);
			EqGraphNode.copyFields(egnInOldState, newGraphNode, this);
			
			newGraphNode.setupNode();
		}

		assert isTopConsistent();
	}


	private void createEqGraphNodes(VPDomainPreanalysis preAnalysis, Set<EqNode> allConstantEqNodes) {

		/*
		 * The EqGraphNodes we need for the given TransFormula can come from four sources:
		 *  (Paradigm: whenever the TransFormula can introduce a (dis-)equality about something, we need
		 *   EqGraphNodes to track that.)
		 *  1. array accesses in the TransFormula
		 *    --> we obtain them by the extraction methods of the MultiDimensionsalX classes
		 *  2. variables in the TransFormula (outside of array accesses)
		 *    --> we can see them in the invars and outvars of the TransFormula
		 *  3. constants in the TransFormula
		 *    --> we can just take the constant EqNodes from the preanalysis 
		 *    (is this more than necessary? maybe not: we have to carry over all 
		 *     relations to constants from the VPStates through the TransFormulas, even if they don't
		 *     occur in some TransFormula)
		 *  4. the auxVars of the TransFormula
		 *  5. Array equalities in the TransFormula
		 *    --> for both arrays we need all the EqFunctionNodes that have the array as function
		 *  6. Array updates in the TransFormula
		 *    --> if there is the same array on both sides, we need the corresponding function node for both versions
		 *    --> if there is a different array on both sides, we should treat this like an array equality
		 *  
		 *  
		 */
		
		
		Map<TermVariable, IProgramVar> tvToPvMap = 
				VPDomainHelpers.computeProgramVarMappingFromTransFormula(mTransFormula);

		/*
		 * 1. array accesses in the TransFormula
		 */
		final List<MultiDimensionalSelect> mdSelectsAll =
				MultiDimensionalSelect.extractSelectShallow(mTransFormula.getFormula(), false);
		for (MultiDimensionalSelect mds : mdSelectsAll) {
			EqNode eqNode = preAnalysis.getEqNode(mds.getSelectTerm(), tvToPvMap);
			if (eqNode == null) {
				// we don't track that select (because we don't track the corresponding array)
				continue;
			}

			ApplicationTerm selectTerm = mds.getSelectTerm();
			
			getOrConstructEqGraphNode(
					eqNode, 
					VPDomainHelpers.projectToTermAndVars(mTransFormula.getInVars(), selectTerm, eqNode.getVariables()), 
//					VPDomainHelpers.projectToVars(mTransFormula.getInVars(), eqNode.getVariables()),
					VPDomainHelpers.projectToTermAndVars(mTransFormula.getOutVars(), selectTerm, eqNode.getVariables()), 
//					VPDomainHelpers.projectToTerm(mTransFormula.getOutVars(), selectTerm), 
//					VPDomainHelpers.projectToVars(mTransFormula.getOutVars(), eqNode.getVariables()), 
					selectTerm);
		}
		final List<MultiDimensionalStore> mdStoresAll =
				MultiDimensionalStore.extractArrayStoresShallow(mTransFormula.getFormula());
		for (MultiDimensionalStore mds : mdStoresAll) {
			EqNode eqNode = preAnalysis.getEqNode(mds.getStoreTerm(), tvToPvMap);
			if (eqNode == null) {
				// we don't track that select (because we don't track the corresponding array)
				continue;
			}

			ApplicationTerm storeTerm = mds.getStoreTerm();
			
			getOrConstructEqGraphNode(
					eqNode, 
					VPDomainHelpers.projectToTermAndVars(mTransFormula.getInVars(), storeTerm, eqNode.getVariables()), 
//					VPDomainHelpers.projectToTerm(mTransFormula.getInVars(), storeTerm), 
//					VPDomainHelpers.projectToVars(mTransFormula.getInVars(), eqNode.getVariables()), 
					VPDomainHelpers.projectToTermAndVars(mTransFormula.getOutVars(), storeTerm, eqNode.getVariables()), 
//					VPDomainHelpers.projectToTerm(mTransFormula.getOutVars(), storeTerm), 
//					VPDomainHelpers.projectToVars(mTransFormula.getOutVars(), eqNode.getVariables()), 
					storeTerm); 
			
			EqNode storedValueNode = preAnalysis.getEqNode(mds.getValue(), tvToPvMap);
			getOrConstructEqGraphNode(
					storedValueNode, 
					VPDomainHelpers.projectToTermAndVars(mTransFormula.getInVars(), mds.getValue(), storedValueNode.getVariables()), 
//					VPDomainHelpers.projectToTerm(mTransFormula.getInVars(), mds.getValue()), 
//					VPDomainHelpers.projectToVars(mTransFormula.getInVars(), storedValueNode.getVariables()), 
					VPDomainHelpers.projectToTermAndVars(mTransFormula.getOutVars(), mds.getValue(), storedValueNode.getVariables()), 
//					VPDomainHelpers.projectToTerm(mTransFormula.getOutVars(), mds.getValue()), 
//					VPDomainHelpers.projectToVars(mTransFormula.getOutVars(), storedValueNode.getVariables()), 
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
					VPDomainHelpers.projectToTerm(mTransFormula.getInVars(), en.getKey()), 
					VPDomainHelpers.projectToTerm(mTransFormula.getOutVars(),  en.getKey()), 
					en.getKey());
		}
		
		/*
		 * 3. constants in the TransFormula
		 */
		for (EqNode constantEqNode : allConstantEqNodes) {
			assert constantEqNode.isConstant();
	
			// technical note: the constant select/store terms that occur in mTransFormula have been treated by
			//  step 1. already. -- therefore it should be ok to use EqNode.getTerm for the term argument of the 
			//  getOrConstruct method; because say we have a constant store in this formula, it has 
			//  already been put into the map.
			
			getOrConstructEqGraphNode(constantEqNode, 
					Collections.emptyMap(), 
					Collections.emptyMap(), 
					constantEqNode.getTerm());
		}
		
		/*
		 * 4. the auxVars of the TransFormula
		 */
		for (TermVariable auxVar : mTransFormula.getAuxVars()) {
			getOrConstructEqGraphNode(auxVar);
		}
		
		/*
		 * 5. ArrayEqualities
		 * say we have an array equality a = b
		 * Then we need to introduce nodes for all indices that we track for both a and b, right?..
		 *  note that the above steps may already have introduced nodes for some indices
		 *  the index nodes introduced here have inVars and outVars in their nodeIdentifiers, however 
		 *   those don't correspond to any TermVariable (the value of the entries is set to null right now)
		 *   whether a node a[i] is an in or an out or a through-node depends on a.
		 *   
		 *  Question: Would an optimization be to only construct the function-nodes that only differ in their function?
		 *      (e.g. if there are nodes a[i] a[j] b[j] b[k], then we only construct a[j] and b[j] because those are 
		 *        the two nodes we need to equate, without further knowledge we may not equate a[i] and b[j])
		 *  Answer: No. Because we might have the knowledge i = k already in our state and then we can conclude a[i] = b[k]
		 */
		List<ArrayEquality> arrayEqualities = ArrayEquality.extractArrayEqualities(mTransFormula.getFormula());
		for (ArrayEquality ae : arrayEqualities) {
			IProgramVarOrConst lhsPvoc = 
					preAnalysis.getIProgramVarOrConstOrLiteral(ae.getLhs(), tvToPvMap);
			constructIndexnodes(lhsPvoc, preAnalysis);
			
			IProgramVarOrConst rhsPvoc = 
					preAnalysis.getIProgramVarOrConstOrLiteral(ae.getRhs(), tvToPvMap);
			constructIndexnodes(rhsPvoc, preAnalysis);
		}
		
		/*
		 * 6. ArrayUpdates
		 * case 1: newArray and oldArray are the same IProgramVar (like in a normal array update)
		 *   then an index node for the oldArray has been created, we may need to create one for the newArray
		 * case 2: newArray and oldArray have a different IProgramVarOrConst
		 *   this case is treated here like an array equality
		 */
		List<ArrayUpdate> arrayUpdates = ArrayUpdate.extractArrayUpdates(mTransFormula.getFormula());
		for (ArrayUpdate au : arrayUpdates) {
			IProgramVarOrConst newArrayPvoc = 
					preAnalysis.getIProgramVarOrConstOrLiteral(au.getNewArray(), tvToPvMap);
			IProgramVarOrConst oldArrayPvoc = 
					preAnalysis.getIProgramVarOrConstOrLiteral(au.getOldArray(), tvToPvMap);
			
			if (newArrayPvoc == oldArrayPvoc) {
				// case 1: newArray and oldArray are the same IProgramVar (like in a normal array update)
				//  --> a function node for oldArray (which occurs in a store in au's formula) has already been constructed
				//     we construct the same node except for the newArray
				EqFunctionNode storeEqNode = (EqFunctionNode) preAnalysis.getEqNode(au.getMultiDimensionalStore().getStoreTerm(), tvToPvMap);
				
				Map<IProgramVar, TermVariable> resultInVars = new HashMap<>();
				Map<IProgramVar, TermVariable> resultOutVars = new HashMap<>();
				translateXVarsFromFunctionToIndices(storeEqNode.getArgs(), InOutStatus.OUT, mTransFormula, resultInVars, resultOutVars);
				assert resultInVars.isEmpty();
				
				if (newArrayPvoc instanceof IProgramVar) {
					// the updated array is an outVar for our new EqGraphNode, along with its indices
					resultOutVars.put((IProgramVar) newArrayPvoc, au.getNewArray());
				}
				
				getOrConstructEqGraphNode(storeEqNode, 
						Collections.emptyMap(), 
						resultOutVars);
			} else {
				// case 2: newArray and oldArray have a different IProgramVarOrConst
				//  we treat this like an array equality (step 5, in createEqGraphNodes)
				constructIndexnodes(oldArrayPvoc, preAnalysis);
				constructIndexnodes(newArrayPvoc, preAnalysis);
			}
		}
			

	}


	/**
	 * Constructs all the index nodes for the given array
	 * (example: say array is a, and a[i]  and a[b[j]] and a[k] occur somewhere in the program, this VPTfStateBuilder
	 *  will get EqGraphNodes for each of these EqNodes -- their in/out properties depend on that of a in mTransFormula)
	 * 
	 * @param array
	 * @param mTransFormula
	 * @param preAnalysis
	 */
	private void constructIndexnodes(IProgramVarOrConst array, VPDomainPreanalysis preAnalysis) {
		Set<EqFunctionNode> lhsFuncNodes = 
				preAnalysis.getFunctionNodesForArray(array);
		
		for (EqFunctionNode funcEqNode : lhsFuncNodes) {
			Map<IProgramVar, TermVariable> resultInVars = new HashMap<>();
			Map<IProgramVar, TermVariable> resultOutVars = new HashMap<>();
			InOutStatus inOutStatus = getInOutStatusOfPvoc(funcEqNode.getFunction(), mTransFormula);
			translateXVarsFromFunctionToIndices(funcEqNode.getArgs(), inOutStatus, mTransFormula, resultInVars, resultOutVars);

			getOrConstructEqGraphNode(funcEqNode, 
					resultInVars, 
					resultOutVars);
		}
	}
	
	/**
	 * Fills the given  [in|out]varMaps for the indices in the given EqFunctionNode according the given
	 *  in/out/through status.
	 * @param lhsPvoc 
	 */
	private static void translateXVarsFromFunctionToIndices(Collection<EqNode> indexNodes,
			InOutStatus inOutStatus, 
			TransFormula tf, 
			Map<IProgramVar, TermVariable> tfInVars, 
			Map<IProgramVar, TermVariable> tfOutVars) {
		for (EqNode indexNode : indexNodes) {
			for (IProgramVar pv : indexNode.getVariables()) {
				if (inOutStatus == InOutStatus.IN 
						|| inOutStatus == InOutStatus.THROUGH 
						|| inOutStatus == InOutStatus.UPDATE) {
					tfInVars.put(pv, null);
				}
				if (inOutStatus == InOutStatus.OUT 
						|| inOutStatus == InOutStatus.THROUGH 
						|| inOutStatus == InOutStatus.UPDATE) {
					tfOutVars.put(pv, null);
				}
			}

			if (indexNode instanceof EqFunctionNode) {
				translateXVarsFromFunctionToIndices(((EqFunctionNode) indexNode).getArgs(), inOutStatus, tf, tfInVars, tfOutVars);
			}
		}
	}



	private static InOutStatus getInOutStatusOfPvoc(IProgramVarOrConst function, TransFormula tf) {
		InOutStatus functionInOutStatus;
		if (function instanceof IProgramVarOrConst) {
			functionInOutStatus = VPDomainHelpers.computeInOutStatus((IProgramVar) function, tf);
		} else {
			// TODO: constants are like a THROUGH-variable for our purposes here, right?
			//     (or UPDATE, as this makes no difference here)
			functionInOutStatus = InOutStatus.THROUGH;
		}
		return functionInOutStatus;
	}


	public void merge(Term t1, Term t2) {
		EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> egn1 = mNodeIdToEqGraphNode.get(mTermToNodeId.get(t1));
		assert egn1 != null;
		EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> egn2 = mNodeIdToEqGraphNode.get(mTermToNodeId.get(t2));
		assert egn2 != null;
		
		merge(egn1, egn2);
		assert isTopConsistent();
	}

	private EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getOrConstructEqGraphNode(TermVariable tv) {
		// we have an AuxVar
		VPAuxVarNodeIdentifier nodeId = getAuxVarNodeIdentifier(tv);
		mTermToNodeId.put(tv, nodeId);
		EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> result = mNodeIdToEqGraphNode.get(nodeId);
		if (result == null) {
			result = new EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>(nodeId);
			mNodeIdToEqGraphNode.put(nodeId, result);
		}
		return result;
	}

	private EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getOrConstructEqGraphNode(
			final EqNode eqNode, 
			final Map<IProgramVar, TermVariable> inVars, 
			final Map<IProgramVar, TermVariable> outVars) {
		
		// we have a "normal" (i.e. non-AuxVar-) EqGraphNode
		
		VPTfNodeIdentifier nodeIdentifier = getNodeIdentifier(eqNode, inVars, outVars);

		EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> result = mNodeIdToEqGraphNode.get(nodeIdentifier);
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
			
			
			List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> argNodes = new ArrayList<>();

			for (int i = 0; i < ((EqFunctionNode) eqNode).getArgs().size(); i++) {
				EqNode indexEqnode = eqFunctionNode.getArgs().get(i);
//				Map<IProgramVar, TermVariable> argInVars = VPDomainHelpers.projectToTerm(inVars, term);
				Map<IProgramVar, TermVariable> argInVars = VPDomainHelpers.projectOut(inVars, eqFunctionNode.getFunction());
//				Map<IProgramVar, TermVariable> argOutVars = VPDomainHelpers.projectToTerm(outVars, term);
				Map<IProgramVar, TermVariable> argOutVars = VPDomainHelpers.projectOut(outVars, eqFunctionNode.getFunction());
				EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> argNode = getOrConstructEqGraphNode(
						indexEqnode, 
						argInVars, 
						argOutVars); 

				argNode.addToCcpar(result); // later EqGraphNode.setupNode() will make initCCPar out of this
				argNodes.add(argNode);
			}
			// later EqGraphNode.setupNode() will make initCcchild out of this:
			VPTfArrayIdentifier arrayId = 
					getArrayIdentifier(eqFunctionNode.getFunction(), inVars, outVars);
//					new VPArrayIdentifier(
//					VPDomainHelpers.getArrayTerm((ApplicationTerm) term));
			result.addToCcchild(arrayId, argNodes);
			
			mArrayIdToFunctionNodes.addPair(arrayId, nodeIdentifier);
		}
		
		
		return result;
	}
		

	
	/**
	 * 
	 * @param eqNode
	 * @param inVars
	 * @param outVars
	 * @param term given for updating mTermToEqGraphNode -- needs to be non-null for every EqGraphNode that corresponds to
	 *             a subterm in mTransFormula (others might be introduced, for example for ArrayEqualties)
	 * @return
	 */
	private EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getOrConstructEqGraphNode(
			final EqNode eqNode, 
			final Map<IProgramVar, TermVariable> inVars, 
			final Map<IProgramVar, TermVariable> outVars,
			final Term term) {
	
		assert term != null;
		
		// we have a "normal" (i.e. non-AuxVar-) EqGraphNode
		
		VPTfNodeIdentifier nodeIdentifier = getNodeIdentifier(eqNode, inVars, outVars);

		mTermToNodeId.put(term, nodeIdentifier);

		EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> result = mNodeIdToEqGraphNode.get(nodeIdentifier);
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
			
			// when @param term is null, 
			ArrayIndex arrayIndex = term != null ? extractArgumentsFromStoreOrSelect(term) : null;
//			List<Term> arrayIndex = eqFunctionNode.getArgs().stream().map(node -> node.getTerm()).collect(Collectors.toList());
			
			assert arrayIndex == null || eqFunctionNode.getArgs().size() == arrayIndex.size();
			
			List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> argNodes = new ArrayList<>();

			for (int i = 0; i < ((EqFunctionNode) eqNode).getArgs().size(); i++) {
				Term indexTerm = arrayIndex != null ? arrayIndex.get(i) : null;
				EqNode indexEqnode = eqFunctionNode.getArgs().get(i);
//				Map<IProgramVar, TermVariable> argInVars = VPDomainHelpers.projectToTerm(inVars, term);
				Map<IProgramVar, TermVariable> argInVars = VPDomainHelpers.projectOut(inVars, eqFunctionNode.getFunction());
//				Map<IProgramVar, TermVariable> argOutVars = VPDomainHelpers.projectToTerm(outVars, term);
				Map<IProgramVar, TermVariable> argOutVars = VPDomainHelpers.projectOut(outVars, eqFunctionNode.getFunction());
				EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> argNode = getOrConstructEqGraphNode(
						indexEqnode, 
						argInVars, 
						argOutVars, 
						indexTerm); 

				argNode.addToCcpar(result); // later EqGraphNode.setupNode() will make initCCPar out of this
				argNodes.add(argNode);
			}
			// later EqGraphNode.setupNode() will make initCcchild out of this:
			VPTfArrayIdentifier arrayId = 
					getArrayIdentifier(
							VPDomainHelpers.getArrayTerm((ApplicationTerm) term), 
							mTransFormula);
//					VPDomainHelpers.getArrayTerm((ApplicationTerm) term));
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
	public VPTfState build() {
		assert mTransFormula != null;
		assert mNodeIdToEqGraphNode != null;
		assert mTermToNodeId != null;
		assert mArrayIdToFunctionNodes != null;
		assert mDisEqualitySet != null;
		assert mVars != null;
		assert isTopConsistent();
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);

		return new VPTfState(
				mTransFormula, 
				this,
				mNodeIdToEqGraphNode,
				mTermToNodeId,
				mArrayIdToFunctionNodes, 
				mDisEqualitySet, 
				mIsTop, 
				mVars);
	}


	@Override
	public EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> getEqGraphNode(VPTfNodeIdentifier i) {
		return mNodeIdToEqGraphNode.get(i);
	}

	public void addVariables(Set<IProgramVar> variables) {
		mVars.addAll(variables);
	}
	
	public VPTfNodeIdentifier getNodeIdentifier(EqNode eqNode, 
			Map<IProgramVar, TermVariable> inVars, 
			Map<IProgramVar, TermVariable> outVars) {
		VPTfNodeIdentifier result = mNonAuxVarNodeIds.get(eqNode, inVars, outVars);
		
		if (result == null) {
			result = new VPTfNodeIdentifier(eqNode, inVars, outVars, this);
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
	Collection<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> getAllEqGraphNodes() {
		return mNodeIdToEqGraphNode.values();
	}

	public VPTfNodeIdentifier getNodeId(Term value) {
		return mTermToNodeId.get(value);
	}
	
	
	public VPTfArrayIdentifier getArrayIdentifier(Term term, TransFormula transFormula) {
		return getArrayIdentifier(
				mPreAnalysis.getIProgramVarOrConstOrLiteral(term, 
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(transFormula)),
				VPDomainHelpers.projectToTerm(transFormula.getInVars(), term),
				VPDomainHelpers.projectToTerm(transFormula.getOutVars(), term));
	}

	/**
	 * 
	 * @param function
	 * @param inVars
	 * @param outVars
	 * @return
	 * 
	 * TODO should we move this to the VPTfStateBuilder, like the management for VPNodeIdenfifiers??
	 */
	public VPTfArrayIdentifier getArrayIdentifier(IProgramVarOrConst function, 
			Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {
		Pair<IProgramVar, TermVariable> inVar = null;;
		Pair<IProgramVar, TermVariable> outVar = null;;
		
		TermVariable iTv = inVars.get(function);
		if (iTv != null) {
			inVar = new Pair<>((IProgramVar) function, iTv);
		}
		TermVariable oTv = outVars.get(function);
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
	
	public Set<VPTfNodeIdentifier> getFunctionNodesForArray(VPTfArrayIdentifier array) {
		return mArrayIdToFunctionNodes.getImage(array);
	}
}
