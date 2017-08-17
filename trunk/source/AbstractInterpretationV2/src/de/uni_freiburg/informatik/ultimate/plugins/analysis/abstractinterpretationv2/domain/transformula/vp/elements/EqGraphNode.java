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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * This class contain information such as representative, reverse
 * representative, ccpar and ccchild of @EqNode. Each @EqNode will map to
 * one @EqGraphNode, i.e., the relation between @EqNode and @EqGraphNode is one
 * to one mapping. Since @EqNode supposed to be immutable, all the mutable
 * information will be handled by this class.
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqGraphNode<NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
		FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {

	/**
	 * identifies an EqGraphNode uniquely _within one state or transitionstate_
	 */
	public final NODE mNodeIdentifier;

	private EqGraphNode<NODE, FUNCTION> mRepresentative;
	private Set<EqGraphNode<NODE, FUNCTION>> mReverseRepresentative;
	private Set<NODE> mCcpar;
//	private HashRelation<FUNCTION, List<EqGraphNode<NODE, FUNCTION>>> mCcchild;
	private HashRelation<FUNCTION, List<NODE>> mCcchild;

//	private NODE mInitCcpar;
	/**
	 * the parents that this nodes has in the function application graph
	 * example: we have nodes a[i], b[i], i; then initCcpar of i are the other two nodes
	 */
	private Set<NODE> mInitCcpar;
//	private List<EqGraphNode<NODE, FUNCTION>> mInitCcchild;
	private List<NODE> mInitCcchild;

	public EqGraphNode(NODE id) {
		assert id != null;
		
		mNodeIdentifier = id;
		mRepresentative = this;
		mReverseRepresentative = new HashSet<>();
		mReverseRepresentative.add(this);
		mCcpar = new HashSet<>();
		mCcchild = new HashRelation<>();
//		this.mInitCcpar = null;
		mInitCcpar = new HashSet<>();
		if (id.isFunctionApplication()) {
			mInitCcchild = Collections.unmodifiableList(id.getArguments());
			mCcchild.addPair(mNodeIdentifier.getAppliedFunction(), Collections.unmodifiableList(id.getArguments()));
		}
	}
	
//	/**
//	 * This may only be called when all EqGraphNodes for the given state (and thus mapping form Eqnodes to EqGraphNodes)
//	 * have been created.
//	 * Then this method sets up initCCpar and initCcchild according to the mapping and the parent/argument information in
//	 * the EqNode
//	 * @param eqNodeToEqGraphNode
//	 */
//	public void setupNode() {
//		mInitCcpar = new HashSet<>(this.mCcpar);
//		mInitCcpar = Collections.unmodifiableSet(mInitCcpar);
//		
//		if (mNodeIdentifier.isFunction()) {
//			FUNCTION arrayId = mNodeIdentifier.getFunction();
//			assert this.mCcchild.getImage(arrayId).size() == 1;
//			mInitCcchild = new ArrayList<>(this.mCcchild.getImage(arrayId).iterator().next());
//			mInitCcchild = Collections.unmodifiableList(mInitCcchild);
//		}
//	}

	public void setNodeToInitial() {
//		mRepresentative = this;
//		mReverseRepresentative.clear();
//		mReverseRepresentative.add(this);
		
		// do nothing to this.reverseRepresentative, because it is not really a property of this node (by convention)
		
		setRepresentative(this);
		
		

		mCcpar.clear();
		mCcpar.addAll(mInitCcpar);

		mCcchild = new HashRelation<>();
		/*
		 * Only function node have initCcchild.
		 */
		if (mNodeIdentifier.isFunctionApplication()) {
			mCcchild.addPair(mNodeIdentifier.getAppliedFunction(), mInitCcchild);
		}
		
		

	}	
	
	public EqGraphNode<NODE, FUNCTION> find() {
		if (this.getRepresentative().equals(this)) {
			return this;
		}
		return this.getRepresentative().find();
	}

//	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, 
//					NODEID extends IEqNodeIdentifier<NODEID, ARRAYID>, 
//					ARRAYID> 
//				void copyFields(EqGraphNode<NODEID, ARRAYID> source, 
//						EqGraphNode<NODEID, ARRAYID> target, 
//						IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder) {
//		assert target.mNodeIdentifier.equals(source.mNodeIdentifier);
//		
//		EqGraphNode<NODEID, ARRAYID> targetRepresentative = builder.getEqGraphNode(source.getRepresentative().mNodeIdentifier);
//		target.setRepresentative(targetRepresentative);
//		if (target != targetRepresentative) {
//			// we may have to update a disequality such that it talks about the representative
//			HashSet<VPDomainSymmetricPair<NODEID>> diseqsetcopy = new HashSet<>(builder.getDisEqualitySet());
//			for (VPDomainSymmetricPair<NODEID> diseq : diseqsetcopy) {
//				if (diseq.contains(target.mNodeIdentifier)) {
//					builder.removeDisEquality(diseq);
//					builder.addDisEquality(targetRepresentative.mNodeIdentifier, 
//									diseq.getOther(target.mNodeIdentifier));
//				}
//			}
//		}
//		
//		target.getReverseRepresentative().clear();
//		for (EqGraphNode<NODEID, ARRAYID> reverseRe : source.getReverseRepresentative()) {
//			target.getReverseRepresentative().add(builder.getEqGraphNode(reverseRe.mNodeIdentifier));
//		}
//		target.getCcpar().clear();
//		for (EqGraphNode<NODEID, ARRAYID> ccpar : source.getCcpar()) {
//			target.getCcpar().add(builder.getEqGraphNode(ccpar.mNodeIdentifier));
//		}
//		
//		target.mCcchild = new HashRelation<>();
//		for (ARRAYID arrayId : source.getCcchild().getDomain()) {
//			for (List<EqGraphNode<NODEID, ARRAYID>> nodes : source.getCcchild().getImage(arrayId)) {
//				List<EqGraphNode<NODEID, ARRAYID>> newList = nodes.stream()
//						.map(otherNode -> builder.getEqGraphNode(otherNode.mNodeIdentifier))
//						.collect(Collectors.toList());
//				target.getCcchild().addPair(arrayId, newList);
//			}
//		}
//		
//		
//		assert !builder.isTop() || target.getRepresentative() == target;
//	}

	public EqGraphNode<NODE, FUNCTION> getRepresentative() {
		return mRepresentative;
	}

	public void setRepresentative(EqGraphNode<NODE, FUNCTION> representative) {
		
		EqGraphNode<NODE, FUNCTION> oldRepresentative = mRepresentative;
		oldRepresentative.removeReverseRepresentative(this);

		mRepresentative = representative;
		representative.addToReverseRepresentative(this);

        assert this.mRepresentative.mNodeIdentifier != this.mNodeIdentifier || this.mRepresentative == this
        		: "if (eqNodes are identical) then (graphnodes must be identical)";
	}

	public Set<EqGraphNode<NODE, FUNCTION>> getReverseRepresentative() {
		return Collections.unmodifiableSet(mReverseRepresentative);
	}

//	public void setReverseRepresentative(Set<EqGraphNode<NODE, FUNCTION>> reverseRepresentative) {
//		this.mReverseRepresentative = reverseRepresentative;
//	}

	private void addToReverseRepresentative(EqGraphNode<NODE, FUNCTION> reverseRepresentative) {
		this.mReverseRepresentative.add(reverseRepresentative);
	}

//	public Set<EqGraphNode<NODE, FUNCTION>> getCcpar() {
	public Set<NODE> getCcpar() {
		return Collections.unmodifiableSet(mCcpar);
	}

//	public void setCcpar(Set<EqGraphNode<NODE, FUNCTION>> ccpar) {
	public void setCcpar(Set<NODE> ccpar) {
		this.mCcpar = ccpar;
	}
	
	public void setCcchild(HashRelation<FUNCTION, List<NODE>> ccchild) {
		this.mCcchild = ccchild;
	}

	public void addToCcpar(NODE ccpar) {
		this.mCcpar.add(ccpar);
	}
	
	public void addToCcpar(Collection<NODE> ccpar) {
		this.mCcpar.addAll(ccpar);
	}

	public HashRelation<FUNCTION, List<NODE>> getCcchild() {
		return mCcchild;
	}
	
//	public void addToCcchild(FUNCTION pVorC, List<EqGraphNode<NODE, FUNCTION>> ccchild) {
	public void addToCcchild(FUNCTION pVorC, List<NODE> ccchild) {
		this.mCcchild.addPair(pVorC, ccchild);
	}
	
//	public void addToCcchild(HashRelation<FUNCTION, List<EqGraphNode<NODE, FUNCTION>>> ccchild2) {
	public void addToCcchild(HashRelation<FUNCTION, List<NODE>> ccchild2) {
		for (final Entry<FUNCTION, List<NODE>> entry : ccchild2.entrySet()) {
			addToCcchild(entry.getKey(), entry.getValue());
		}
	}

	/**
	 * this is a set just for compatibility with "normal" ccPar, right? (EDIT no more.. EDIT no!, this must be a set!!
	 *  see documentation of mInitCcpar)
	 * @return
	 */
//	public NODE getInitCcpar() {
	public Set<NODE> getInitCcpar() {
		return Collections.unmodifiableSet(mInitCcpar);
	}

	public List<NODE> getInitCcchild() {
		return Collections.unmodifiableList(mInitCcchild);
	}

//	public void setInitCcchild(List<NODE> initCcchild) {
//		this.mInitCcchild = initCcchild;
//	}

	public NODE getNode() {
		return mNodeIdentifier;
	}

	public String toString() {

		final StringBuilder sb = new StringBuilder();

		sb.append(mNodeIdentifier.toString());
		if (mRepresentative != this) {
			sb.append(" ||| representative: ");
			sb.append(mRepresentative.mNodeIdentifier.toString());
		}
		
//		sb.append(" ||| reverseRepresentative: ");
//		for (EqGraphNode node : reverseRepresentative) {
//			sb.append(node.eqNode.toString());
//			sb.append("  ");
//		}
//		sb.append(" ||| ccpar: ");
//		for (EqGraphNode node : ccpar) {
//			sb.append(node.eqNode.toString());
//			sb.append("  ");
//		}
//		sb.append(" ||| ccchild: ");
//		for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : ccchild.entrySet()) {
//			sb.append(entry.getKey().toString() + ": {");
//			for (EqGraphNode node : entry.getValue()) {
//				sb.append(node.toString());
//				sb.append("  ");
//			}
//			sb.append("}, ");
//		}

		return sb.toString();
	}

//	public EqGraphNode<NODE, FUNCTION> renameVariables(Map<Term, Term> substitutionMapping) {
//		// TODO Auto-generated method stub
//		return null;
//	}

//	public void setInitCcpar(NODE initCCpar) {
////		assert mInitCcpar.isEmpty() : "init ccpar should never change, except from no parent to some parent";
//		assert mInitCcpar == null : "init ccpar should never change, except from no parent to some parent";
//		mInitCcpar = initCCpar;
//	}

	public void addToInitCcpar(NODE node) {
		mInitCcpar.add(node);
		mCcpar.add(node);
	}

	public void removeFromCcpar(Set<NODE> nodes) {
		mCcpar.removeAll(nodes);
	}

	public void removeFromCcchild(HashRelation<FUNCTION, List<NODE>> ccchild) {
		mCcchild.removeAllPairs(ccchild);
	}

	private void removeReverseRepresentative(EqGraphNode<NODE, FUNCTION> graphNodeForNodeToBeHavocced) {
		assert mReverseRepresentative.contains(graphNodeForNodeToBeHavocced);
		mReverseRepresentative.remove(graphNodeForNodeToBeHavocced);
	}

	/**
	 * after havoccing a node, we have to make sure no other node still remembers it, in particular in its ccpar and 
	 * ccchild fields..
	 * 
	 * @param nodeToBeHavocced
	 * @return
	 */
	public void purgeNodeFromFields(NODE nodeToBeHavocced) {
		mCcpar.remove(nodeToBeHavocced);
//		for (Entry<FUNCTION, List<NODE>> en : mCcchild.entrySet()) {
//			en.getValue().remove(nodeToBeHavocced);
//		}
//		mCcchild..entrySet().removeIf(en -> en.getValue().contains(nodeToBeHavocced));
			
		final HashRelation<FUNCTION, List<NODE>> newCchild = new HashRelation<>();
		for (Entry<FUNCTION, List<NODE>> en : mCcchild.entrySet()) {
			if (en.getValue().contains(nodeToBeHavocced)) {
				continue;
			}
			newCchild.addPair(en.getKey(), en.getValue());
		}
		mCcchild = newCchild;
	}
}
