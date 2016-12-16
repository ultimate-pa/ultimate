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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

public class VPTransitionStateBuilder extends IVPStateOrTfStateBuilder<VPTfState> {
	
	Set<IProgramVar> mVars = new HashSet<>();
	
	Map<Term, TFEqGraphNode> mTermToEqGraphNodeMap = new HashMap<>();
	private NestedMap3<EqNode, 
		Map<IProgramVar, TermVariable>, 
		Map<IProgramVar, TermVariable>, 
		TFEqGraphNode> mEqNodeToInVarsToOutVarsToEqGraphNode;

	private HashRelation<VPArrayIdentifier, VPNodeIdentifier> mArrayIdToFunctionNodes;

	private TransFormula mTransFormula;

	public VPTransitionStateBuilder(VPDomainPreanalysis preAnalysis,
			TransFormula tf, Set<EqNode> allConstantEqNodes) {
		createEqGraphNodes(tf, preAnalysis, allConstantEqNodes);
		
		for (TFEqGraphNode tfegn : mTermToEqGraphNodeMap.values()) {
			tfegn.setupNode();
		}
	}

	
	private void createEqGraphNodes(
			TransFormula tf, VPDomainPreanalysis preAnalysis, Set<EqNode> allConstantEqNodes) {

		Map<Term, TFEqGraphNode> termToEqGraphNode = new HashMap<>();
		NestedMap3<EqNode, 
				Map<IProgramVar, TermVariable>, 
				Map<IProgramVar, TermVariable>, 
				TFEqGraphNode> 
		 			eqNodeToInVarsToOutVarsToEqGraphNode = new NestedMap3<>();
		
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
					projectToTerm(tf.getInVars(), selectTerm), 
					projectToTerm(tf.getOutVars(), selectTerm), 
					selectTerm, 
					termToEqGraphNode, 
					eqNodeToInVarsToOutVarsToEqGraphNode);
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
					projectToTerm(tf.getInVars(), selectTerm), 
					projectToTerm(tf.getOutVars(), selectTerm), 
					selectTerm, 
					termToEqGraphNode, 
					eqNodeToInVarsToOutVarsToEqGraphNode);
			
			EqNode storedValueNode = preAnalysis.getEqNode(mds.getValue(), tvToPvMap);
			getOrConstructEqGraphNode(
					storedValueNode, 
					projectToTerm(tf.getInVars(), mds.getValue()), 
					projectToTerm(tf.getOutVars(), mds.getValue()), 
					mds.getValue(), 
					termToEqGraphNode, 
					eqNodeToInVarsToOutVarsToEqGraphNode);
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
					projectToTerm(tf.getInVars(), en.getKey()), 
					projectToTerm(tf.getOutVars(),  en.getKey()), 
					en.getKey(), 
					termToEqGraphNode, 
					eqNodeToInVarsToOutVarsToEqGraphNode);
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
					constantEqNode.getTerm(preAnalysis.getManagedScript()), 
					termToEqGraphNode, 
					eqNodeToInVarsToOutVarsToEqGraphNode);
		}
		
		/*
		 * 4. the auxVars of the TransFormula
		 */
		for (TermVariable auxVar : tf.getAuxVars()) {
			getOrConstructEqGraphNode(null, 
					Collections.emptyMap(), 
					Collections.emptyMap(), 
					auxVar, 
					termToEqGraphNode, 
					eqNodeToInVarsToOutVarsToEqGraphNode);
		}
		
		mTermToEqGraphNodeMap = Collections.unmodifiableMap(termToEqGraphNode);
		mEqNodeToInVarsToOutVarsToEqGraphNode = eqNodeToInVarsToOutVarsToEqGraphNode;
	}
	
	public void merge(Term t1, Term t2) {
		TFEqGraphNode egn1 = mTermToEqGraphNodeMap.get(t1);
		assert egn1 != null;
		TFEqGraphNode egn2 = mTermToEqGraphNodeMap.get(t2);
		assert egn2 != null;
		
		merge(egn1, egn2);
	}
	
	private TFEqGraphNode getOrConstructEqGraphNode(
			final EqNode eqNode, 
			final Map<IProgramVar, TermVariable> inVars, 
			final Map<IProgramVar, TermVariable> outVars, 
			final Term term,
			final Map<Term, TFEqGraphNode> termToEqGraphNode,
			final NestedMap3<EqNode, Map<IProgramVar, TermVariable>, Map<IProgramVar, TermVariable>, TFEqGraphNode> 
				eqNodeToInVarsToOutVarsToEqGraphNode) {

		TFEqGraphNode result = termToEqGraphNode.get(term);
		if (result != null) {
			return result;
		}
		
		// there is no entry for the given term, yet, there are several possible reasons
		
		/*
		 * reason 1: .. it is a store term and we only have an entry for the select term or vice versa
		 *  then we need to find the already existent TFEqGraphNode and update the term-map
		 */
		result = eqNodeToInVarsToOutVarsToEqGraphNode.get(eqNode, inVars, outVars);
		if (result != null) {
			termToEqGraphNode.put(term, result);
			return result;
		}

		/*
		 * reason 2: the corresponding EqGraphNode has not yet been created
		 */
		
		result = new TFEqGraphNode(eqNode, inVars, outVars, term);
		
		if (eqNode instanceof EqFunctionNode) {
			EqFunctionNode eqFunctionNode = (EqFunctionNode) eqNode;
			
			ArrayIndex arrayIndex = extractArgumentsFromStoreOrSelect(term);
			
			assert eqFunctionNode.getArgs().size() == arrayIndex.size();
			
			List<EqGraphNode> argNodes = new ArrayList<>();

			for (int i = 0; i < ((EqFunctionNode) eqNode).getArgs().size(); i++) {
				Term indexTerm = arrayIndex.get(i);
				EqNode indexEqnode = eqFunctionNode.getArgs().get(i);
				Map<IProgramVar, TermVariable> argInVars = projectToTerm(inVars, term);
				Map<IProgramVar, TermVariable> argOutVars = projectToTerm(outVars, term);
				TFEqGraphNode argNode = getOrConstructEqGraphNode(
						indexEqnode, 
						argInVars, 
						argOutVars, 
						indexTerm, 
						termToEqGraphNode, 
						eqNodeToInVarsToOutVarsToEqGraphNode);

				argNode.addToCcpar(result); // later EqGraphNode.setupNode() will make initCCPar out of this
				argNodes.add(argNode);
			}
			// later EqGraphNode.setupNode() will make initCcchild out of this:
			VPArrayIdentifier arrayId = new VPArrayIdentifier(((EqFunctionNode) eqNode).getFunction());
			result.getCcchild().addPair(arrayId, argNodes);
			
			mArrayIdToFunctionNodes.addPair(arrayId, new VPNodeIdentifier(term));
		}
		
		eqNodeToInVarsToOutVarsToEqGraphNode.put(eqNode, inVars, outVars, result);
		termToEqGraphNode.put(term, result);
		
		return result;
	}
	
	/**
	 * Only keeps those entries in the given map whose value is a free variable in the given Term.
	 */
	private Map<IProgramVar, TermVariable> projectToTerm(Map<IProgramVar, TermVariable> xVars, Term term) {
		Map<IProgramVar, TermVariable> result = new HashMap<>();
		for (Entry<IProgramVar, TermVariable> en : xVars.entrySet()) {
			if (Arrays.asList(term.getFreeVars()).contains(en.getValue())) {
				result.put(en.getKey(), en.getValue());
			}
		}
		return result;
	}

	private ArrayIndex extractArgumentsFromStoreOrSelect(Term term) {
		List<MultiDimensionalSelect> selects = MultiDimensionalSelect.extractSelectDeep(term, true);
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
		assert mTermToEqGraphNodeMap != null;
		assert mArrayIdToFunctionNodes != null;
		assert mDisEqualitySet != null;
		assert mVars != null;
		return new VPTfState(
				mTransFormula, 
				mTermToEqGraphNodeMap, 
				mArrayIdToFunctionNodes, 
				mDisEqualitySet, mIsTop, mVars);
	}


	@Override
	EqGraphNode getEqGraphNode(VPNodeIdentifier i) {
		return mTermToEqGraphNodeMap.get(i.getIdTerm());
	}

	public void addVariables(Set<IProgramVar> variables) {
		mVars.addAll(variables);
	}
}
