/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPSFO;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class VPState<ACTION extends IIcfgTransition<IcfgLocation>> extends IVPStateOrTfState<EqNode, IProgramVarOrConst>
		implements IAbstractState<VPState<ACTION>, IProgramVarOrConst> {

	private static final String TERM_FUNC_NAME_AND = "and";
	private static final String TERM_TRUE = "true";
	private static final String TERM_FUNC_NAME_DISTINCT = "distinct";

	private final Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> mEqNodeToEqGraphNodeMap;

	protected final Set<IProgramVarOrConst> mVars;

	protected final VPDomain<ACTION> mDomain;
	private final ManagedScript mScript;
	private final Term mTerm;
	private final VPDomainPreanalysis mPreAnalysis;
	protected final VPStateFactory<ACTION> mStateFactory;

	/**
	 * Constructor for bottom state only.
	 *
	 * @param domain
	 */
	VPState(final VPDomain<ACTION> domain, final Set<IProgramVarOrConst> vars) {
		this(Collections.emptyMap(), Collections.emptySet(), vars, domain, false);
	}

	/**
	 * Constructor to be used by VPStateFactory.createTopState() only.
	 */
	VPState(final Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> eqNodeToEqGraphNodeMap,
			final Set<VPDomainSymmetricPair<EqNode>> disEqualitySet, final Set<IProgramVarOrConst> vars,
			final VPDomain<ACTION> domain, final boolean isTop) {
		super(disEqualitySet, isTop);
		mEqNodeToEqGraphNodeMap = Collections.unmodifiableMap(eqNodeToEqGraphNodeMap);
		mDomain = domain;
		mScript = mDomain.getManagedScript();
		mPreAnalysis = mDomain.getPreAnalysis();
		mStateFactory = mDomain.getVpStateFactory();
		mVars = Collections.unmodifiableSet(vars);

		mTerm = constructTerm();

		assert sanityCheck();
		assert isTopConsistent();
	}

	private boolean sanityCheck() {
		for (final VPDomainSymmetricPair<EqNode> pair : getDisEqualities()) {
			if (!mEqNodeToEqGraphNodeMap.containsKey(pair.getFirst())) {
				return false;
			}
			if (!mEqNodeToEqGraphNodeMap.containsKey(pair.getSecond())) {
				return false;
			}
		}
		return true;
	}

	public Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> getEqNodeToEqGraphNodeMap() {
		return mEqNodeToEqGraphNodeMap;
	}

	@Override
	public VPState<ACTION> addVariable(final IProgramVarOrConst variable) {
		if (mVars.contains(variable)) {
			return this;
		}
		final VPStateBuilder<ACTION> copy = mStateFactory.copy(this);
		copy.addVars(Collections.singleton(variable));
		return copy.build();
	}

	@Override
	public VPState<ACTION> addVariables(final Collection<IProgramVarOrConst> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final VPStateBuilder<ACTION> copy = mStateFactory.copy(this);
		copy.addVars(variables);
		return copy.build();
	}

	@Override
	public VPState<ACTION> removeVariable(final IProgramVarOrConst variable) {
		if (!mVars.contains(variable)) {
			return this;
		}
		final VPStateBuilder<ACTION> copy = mStateFactory.copy(this);
		copy.removeVars(Collections.singleton(variable));
		return copy.build();
	}

	@Override
	public VPState<ACTION> removeVariables(final Collection<IProgramVarOrConst> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final VPStateBuilder<ACTION> copy = mStateFactory.copy(this);
		copy.removeVars(variables);
		return copy.build();
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mVars.contains(var);
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return mVars;
	}

	@Override
	public VPState<ACTION> patch(final VPState<ACTION> dominator) {

		final Set<IProgramVar> dominatorVars = dominator.getVariables().stream()
				.filter(pvoc -> pvoc instanceof IProgramVar)
				.map(pvoc -> (IProgramVar) pvoc)
				.collect(Collectors.toSet());
		final VPState<ACTION> thisHavocced = mStateFactory.havocVariables(dominatorVars, this);
		
		Set<VPState<ACTION>> resultStates = Collections.singleton(thisHavocced);
		
		final List<EqGraphNode<EqNode, IProgramVarOrConst>> thisHavoccedEqGraphNodesAsList = 
				new ArrayList<>(thisHavocced.getAllEqGraphNodes());
		
		for (int i = 0; i < thisHavoccedEqGraphNodesAsList.size(); i++) {
			for (int j = 0; j < i; j++) {
				final EqGraphNode<EqNode, IProgramVarOrConst> eqgn1 = thisHavoccedEqGraphNodesAsList.get(i);
				final EqGraphNode<EqNode, IProgramVarOrConst> eqgn2 = thisHavoccedEqGraphNodesAsList.get(j);

				if (eqgn1 == eqgn2) {
					continue;
				}
				
				if (!dominator.getAllEqGraphNodes().contains(eqgn1)
						|| !dominator.getAllEqGraphNodes().contains(eqgn2)) {
					/*
					 *  if the dominator does not know either of the nodes, than he definitely won't have a constraint
					 *  on them
					 */
					continue;
				}
	
				final EqNode eqn1 = eqgn1.mNodeIdentifier;
				final EqNode eqn2 = eqgn2.mNodeIdentifier;
				
				if (dominator.areEqual(eqn1, eqn2)) {
					assert !dominator.areUnEqual(eqn1, eqn2);
					resultStates = VPFactoryHelpers.addEquality(eqn1, eqn2, resultStates, mStateFactory);
				}  else	if (dominator.areUnEqual(eqn1, eqn2)) {
					resultStates = VPFactoryHelpers.addDisEquality(eqn1, eqn2, resultStates, mStateFactory);
				}
				assert resultStates.size() == 1;
			}
		}
		
		assert resultStates.size() == 1;
		return resultStates.iterator().next();
	}

	@Override
	public boolean isEmpty() {
		return mVars.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return false;
	}

	@Override
	public boolean isEqualTo(final VPState<ACTION> other) {

		if (!mVars.equals(other.mVars)) {
			return false;
		}

		mScript.lock(this);
		final TermVarsProc tvpThis = TermVarsProc.computeTermVarsProc(getTerm(mScript.getScript()), mScript.getScript(),
				mDomain.getSymbolTable());
		final TermVarsProc tvpOther = TermVarsProc.computeTermVarsProc(other.getTerm(mScript.getScript()),
				mScript.getScript(), mDomain.getSymbolTable());

		/*
		 * build a term that says (not (this.getTerm() <--> other.getTerm))
		 */
		final Term equiv = mScript.term(this, TERM_FUNC_NAME_DISTINCT,
				new Term[] { tvpThis.getClosedFormula(), tvpOther.getClosedFormula() });

		mScript.echo(this, new QuotedObject("VPState<ACTION>.isEqualTo()"));
		mScript.push(this, 1);
		mScript.assertTerm(this, equiv);
		final LBool res = mScript.checkSat(this);
		mScript.pop(this, 1);

		mScript.unlock(this);

		return res == LBool.UNSAT;

	}

	@Override
	public SubsetResult isSubsetOf(final VPState<ACTION> other) {
		if (isEqualTo(other)) {
			return SubsetResult.EQUAL;
		}
		return SubsetResult.NONE;
	}

	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("VPState\n");
		sb.append("vars: " + mVars.toString() + "\n");
		// sb.append("eqGraphNodes: " + getAllEqGraphNodes().toString() + "\n");
		sb.append("Graph:\n");
		for (final EqGraphNode<EqNode, IProgramVarOrConst> egn : getAllEqGraphNodes()) {
			if (egn.getRepresentative() != egn) {
				sb.append(egn.toString() + "\n");
			}
		}
		sb.append("DisEqualities:" + getDisEqualities() + "\n");
		return sb.toString();
	}

	@Override
	public String toString() {
		if (mTerm == null) {
			return "VPState<ACTION>, uninitialized";
		}
		return toLogString();
	}

	@Override
	public Term getTerm(final Script s) {
		assert mTerm != null;
		return mTerm;
	}

	private Term constructTerm() {

		mScript.lock(this);
		final Term trueTerm = mScript.term(this, TERM_TRUE);

		Term disEqualityFirst;
		Term disEqualitySecond;
		final Set<Term> distinctTermSet = new HashSet<>();
		Term disEquality;

		for (final VPDomainSymmetricPair<EqNode> pair : getDisEqualities()) {
			disEqualityFirst = pair.getFirst().getTerm();
			disEqualitySecond = pair.getSecond().getTerm();
			distinctTermSet.add(mScript.term(this, TERM_FUNC_NAME_DISTINCT, disEqualityFirst, disEqualitySecond));
		}

		if (distinctTermSet.isEmpty()) {
			disEquality = trueTerm;
		} else if (distinctTermSet.size() == 1) {
			disEquality = mScript.term(this, TERM_FUNC_NAME_AND, distinctTermSet.iterator().next(), trueTerm);
		} else {
			disEquality =
					mScript.term(this, TERM_FUNC_NAME_AND, distinctTermSet.toArray(new Term[distinctTermSet.size()]));
		}

		Term equalityFirst;
		Term equalitySecond;
		final Set<Term> equalityTermSet = new HashSet<>();
		Term equality;

		for (final EqGraphNode<EqNode, IProgramVarOrConst> graphNode : mEqNodeToEqGraphNodeMap.values()) {
			if (!graphNode.equals(graphNode.getRepresentative())) {
				equalityFirst = graphNode.mNodeIdentifier.getTerm();
				equalitySecond = graphNode.getRepresentative().mNodeIdentifier.getTerm();
				equalityTermSet.add(mScript.term(this, "=", equalityFirst, equalitySecond));
			}
		}

		if (equalityTermSet.isEmpty()) {
			equality = trueTerm;
		} else if (equalityTermSet.size() == 1) {
			equality = mScript.term(this, TERM_FUNC_NAME_AND, equalityTermSet.iterator().next(), trueTerm);
		} else {
			equality =
					mScript.term(this, TERM_FUNC_NAME_AND, equalityTermSet.toArray(new Term[equalityTermSet.size()]));
		}

		final Term result = mScript.term(this, TERM_FUNC_NAME_AND, disEquality, equality);
		mScript.unlock(this);

		return result;
	}

	public Set<EqNode> getEquivalenceRepresentatives() {
		final Set<EqNode> result = new HashSet<>();
		for (final EqGraphNode<EqNode, IProgramVarOrConst> egn : mEqNodeToEqGraphNodeMap.values()) {
			if (egn.getRepresentative() == egn) {
				result.add(egn.mNodeIdentifier);
			}
		}
		return result;
	}

	/**
	 * TODO: more efficient implementation? (of the methods using this method?)
	 *
	 * @param node
	 * @return All the eqNodes that are in the same equivalence class as node in this state.
	 */
	public Set<EqNode> getEquivalentEqNodes(final EqNode node) {
		if (node == null) {
			return Collections.emptySet();
		}
		final EqGraphNode<EqNode, IProgramVarOrConst> nodeGraphNode = mEqNodeToEqGraphNodeMap.get(node);
		final Set<EqNode> result = new HashSet<>();
		for (final EqGraphNode<EqNode, IProgramVarOrConst> egn : mEqNodeToEqGraphNodeMap.values()) {
			if (egn.find() == nodeGraphNode.find()) {
				result.add(egn.mNodeIdentifier);
			}
		}
		return result;
	}

	public boolean mayEqual(final EqNode accessingNode1, final EqNode accessingNode2) {
		return accessingNode1 == accessingNode2 || !getDisEqualities()
				.contains(new VPDomainSymmetricPair<>(find(accessingNode1), find(accessingNode2)));
	}

	public Set<EqNode> getUnequalNodes(final EqNode callParamNode) {
		final Set<EqNode> result = new HashSet<>();

		for (final VPDomainSymmetricPair<EqNode> pair : getDisEqualities()) {
			if (pair.contains(callParamNode)) {
				result.add(pair.getOther(callParamNode));
			}
		}
		return result;
	}

	@Override
	public EqGraphNode<EqNode, IProgramVarOrConst> getEqGraphNode(final EqNode nodeIdentifier) {
		return mEqNodeToEqGraphNodeMap.get(nodeIdentifier);
	}

	@Override
	public Set<EqGraphNode<EqNode, IProgramVarOrConst>> getAllEqGraphNodes() {
		return new HashSet<>(mEqNodeToEqGraphNodeMap.values());
	}

	@Override
	public EqNode find(final EqNode id) {
		return mEqNodeToEqGraphNodeMap.get(id).find().mNodeIdentifier;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashHsieh(31, mVars, getTerm(mScript.getScript()));
	}

	@Override
	public boolean equals(final Object obj) {
		mPreAnalysis.getBenchmark().unpause(VPSFO.vpStateEqualsClock);
		if (this == obj) {
			mPreAnalysis.getBenchmark().stop(VPSFO.vpStateEqualsClock);
			return true;
		}
		if (obj == null) {
			mPreAnalysis.getBenchmark().stop(VPSFO.vpStateEqualsClock);
			return false;
		}
		if (getClass() != obj.getClass()) {
			mPreAnalysis.getBenchmark().stop(VPSFO.vpStateEqualsClock);
			return false;
		}
		@SuppressWarnings("unchecked")
		final VPState<ACTION> other = (VPState<ACTION>) obj;
		if (isEqualTo(other)) {
			// TODO: Note that computing isEqualTo can be quite expensive!
			mPreAnalysis.getBenchmark().stop(VPSFO.vpStateEqualsClock);
			return true;
		}
		mPreAnalysis.getBenchmark().stop(VPSFO.vpStateEqualsClock);
		return false;
	}

	/**
	 * Returns true iff term1 _must_ equal term2 in this VPState. (In particular returns false if this VPState does not
	 * have any constraint on the term1 and term2.)
	 */
	public boolean areEqual(final Term term1, final Term term2) {
		final EqNode node1 = mPreAnalysis.getEqNode(term1);
		final EqNode node2 = mPreAnalysis.getEqNode(term2);
		if (node1 == null || node2 == null) {
			// the analysis did not track at least one of the given terms
			return false;
		}
		return areEqual(node1, node2);
	}

	/**
	 * Returns true iff term1 and term2 _must_ be unequal in this VPState. (In particular returns false if this VPState
	 * does not have any constraint on the term1 and term2.)
	 */
	public boolean areUnEqual(final Term term1, final Term term2) {
		final EqNode node1 = mPreAnalysis.getEqNode(term1);
		final EqNode node2 = mPreAnalysis.getEqNode(term2);
		if (node1 == null || node2 == null) {
			// the analysis did not track at least one of the given terms
			return false;
		}
		return areUnEqual(node1, node2);
	}

	@Override
	public VPState<ACTION> intersect(final VPState<ACTION> other) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public VPState<ACTION> union(final VPState<ACTION> other) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public VPState<ACTION> compact() {
		throw new UnsupportedOperationException("Not yet implemented");
	}
}
