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

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
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
 *
 */
public class VPState<ACTION extends IIcfgTransition<IcfgLocation>> extends IVPStateOrTfState<EqNode, IProgramVarOrConst>
		implements IAbstractState<VPState<ACTION>, IProgramVar> {

	private static final String TERM_FUNC_NAME_AND = "and";
	private static final String TERM_TRUE = "true";
	private static final String TERM_FUNC_NAME_DISTINCT = "distinct";

	private final Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> mEqNodeToEqGraphNodeMap;

	private final VPDomain<ACTION> mDomain;
	final private ManagedScript mScript;
	private Term mTerm;
	final private VPDomainPreanalysis mPreAnalysis;
	final private VPStateFactory<ACTION> mFactory;

	/**
	 * Constructor for bottom state only.
	 *
	 * @param domain
	 */
	// VPState(final ManagedScript script, final VPDomainPreanalysis preAnalysis, final VPStateFactory<ACTION> factory,
	// final Set<IProgramVar> vars) {
	VPState(final VPDomain<ACTION> domain, final Set<IProgramVar> vars) {
		this(Collections.emptyMap(), Collections.emptySet(), vars, domain, false);
	}

	/*
	 * Constructor to be used by VPStateFactory.createTopState() only.
	 */
	VPState(final Map<EqNode, EqGraphNode<EqNode, IProgramVarOrConst>> eqNodeToEqGraphNodeMap,
			final Set<VPDomainSymmetricPair<EqNode>> disEqualitySet, final Set<IProgramVar> vars,
			final VPDomain<ACTION> domain,
			// final ManagedScript script,
			// final VPDomainPreanalysis preAnalysis,
			// final VPStateFactory<ACTION> factory,
			final boolean isTop) {
		super(disEqualitySet, isTop, vars);
		// mVars = Collections.unmodifiableSet(vars);
		mEqNodeToEqGraphNodeMap = Collections.unmodifiableMap(eqNodeToEqGraphNodeMap);
		// mDisEqualitySet = Collections.unmodifiableSet(disEqualitySet);
		mDomain = domain;
		mScript = mDomain.getManagedScript();
		mPreAnalysis = mDomain.getPreAnalysis();
		mFactory = mDomain.getVpStateFactory();
		// mIsTop = isTop;

		constructTerm();

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
	public VPState<ACTION> addVariable(final IProgramVar variable) {
		if (mVars.contains(variable)) {
			return this;
		}
		final VPStateBuilder<ACTION> copy = mFactory.copy(this);
		copy.addVars(Collections.singleton(variable));
		return copy.build();
	}

	@Override
	public VPState<ACTION> addVariables(final Collection<IProgramVar> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final VPStateBuilder<ACTION> copy = mFactory.copy(this);
		copy.addVars(variables);
		return copy.build();
	}

	@Override
	public VPState<ACTION> removeVariable(final IProgramVar variable) {
		if (!mVars.contains(variable)) {
			return this;
		}
		final VPStateBuilder<ACTION> copy = mFactory.copy(this);
		copy.removeVars(Collections.singleton(variable));
		// VPState<ACTION> result = mDomain.getVpStateFactory().havocVariables(Collections.singleton(variable),
		// copy.build());
		final VPState<ACTION> result = copy.build();
		return result;
	}

	@Override
	public VPState<ACTION> removeVariables(final Collection<IProgramVar> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final VPStateBuilder<ACTION> copy = mFactory.copy(this);
		copy.removeVars(variables);
		// VPState<ACTION> result = mDomain.getVpStateFactory().havocVariables(new HashSet<>(variables), copy.build());
		final VPState<ACTION> result = copy.build();
		return result;
	}

	@Override
	public boolean containsVariable(final IProgramVar var) {
		return mVars.contains(var);
	}

	@Override
	public Set<IProgramVar> getVariables() {
		return mVars;
	}

	@Override
	public VPState<ACTION> patch(final VPState<ACTION> dominator) {
		/*
		 * plan: - copy dominator - add variables from this - add the following relations from this: where at least one
		 * of the related variables does not occur in dominator's variables TODO: is this correct??
		 */

		if (this.isBottom() || dominator.isBottom()) {
			final Set<IProgramVar> newVars = new HashSet<>(mVars);
			newVars.addAll(dominator.mVars);
			final VPState<ACTION> resultState = mFactory.getBottomState(newVars);
			return resultState;
		}

		final VPStateBuilder<ACTION> builder = mFactory.copy(dominator);

		builder.addVars(mVars);

		builder.setIsTop(isTop() && dominator.isTop());

		VPState<ACTION> resultState = builder.build();

		/*
		 * for each variable that is in this.mVars, but not in dominator.mVars: obtain all relations with something that
		 * is in this or in dominator, and add them.
		 */
		for (final IProgramVar var : mVars) {
			if (dominator.getVariables().contains(var)) {
				continue;
			}

			final EqNode nodeFromVar = mPreAnalysis.getEqNode(var.getTerm(), Collections.emptyMap());

			// TODO inefficient.. (we only need edges from the tree but add the clique..)
			final Set<EqNode> equalEqNodes = this.getEquivalentEqNodes(nodeFromVar);
			for (final EqNode equalEqNode : equalEqNodes) {
				//// Set<VPState<ACTION>> newStates = mDomain.getVpStateFactory().addEquality(nodeFromVar, equalEqNode,
				//// resultStates);
				// Set<VPState<ACTION>> newStates = new HashSet<>();
				// for (VPState<ACTION> rs : resultStates) {
				// newStates.addAll(mDomain.getVpStateFactory().addEquality(nodeFromVar, equalEqNode, rs));
				//// resultStates.addAll(newStates);
				// }
				// resultStates.addAll(newStates);
				// TODO: this disjoinAll-strategy is a fallback essentially --> is there something better??
				final Set<VPState<ACTION>> states =
						VPFactoryHelpers.addEquality(nodeFromVar, equalEqNode, resultState, mFactory);
				resultState = VPFactoryHelpers.disjoinAll(states, mFactory);
			}

			// TODO: inefficient, again, but we have to do this also for the otherwise implicit disequalites with
			// other members of the equivalence class, right?
			final Set<EqNode> unEqualEqNodes = this.getUnequalNodes(nodeFromVar);
			for (final EqNode unequalRepresentative : unEqualEqNodes) {
				for (final EqNode unEqualNode : this.getEquivalentEqNodes(unequalRepresentative)) {
					// Set<VPState<ACTION>> newStates = mDomain.getVpStateFactory().addDisEquality(nodeFromVar,
					// unEqualNode,
					// resultStates);
					// resultStates.addAll(newStates);
					final Set<VPState<ACTION>> states =
							VPFactoryHelpers.addDisEquality(nodeFromVar, unEqualNode, resultState, mFactory);
					resultState = VPFactoryHelpers.disjoinAll(states, mFactory);
				}
			}
		}

		// VPState<ACTION> resultState = mDomain.getVpStateFactory().disjoinAll(resultStates);

		return resultState;
	}

	@Override
	public boolean isEmpty() {
		return mVars.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return false;
	}

	// public boolean isTop() {
	// return mIsTop;
	// }

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
		// return "VPState<ACTION>:\n" + mTerm.toString();
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

		// final StringBuilder sb = new StringBuilder();
		//
		// sb.append("VPState<ACTION>:\n");
		// sb.append("Vars: " + mVars + "\n");
		// sb.append("Graph: \n");
		// for (final EqGraphNode graphNode : mEqNodeToEqGraphNodeMap.values()) {
		// if (graphNode.getRepresentative() == graphNode) {
		// // print only the interesting graph nodes in full
		// sb.append(graphNode.eqNode.toString());
		// } else {
		// sb.append(graphNode.toString());
		// }
		// sb.append('\n');
		// }
		//
		// sb.append("Disequality Set: \n");
		// for (final VPDomainSymmetricPair<EqNode> pair : mDisEqualitySet) {
		// sb.append(pair.getFirst().toString());
		// sb.append(", ");
		// sb.append(pair.getSecond().toString());
		// sb.append('\n');
		// }
		//
		// return sb.toString();
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

	private void constructTerm() {

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
				equalityFirst = graphNode.nodeIdentifier.getTerm();
				equalitySecond = graphNode.getRepresentative().nodeIdentifier.getTerm();
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

		mTerm = mScript.term(this, TERM_FUNC_NAME_AND, disEquality, equality);
		mScript.unlock(this);

		// return mTerm;
	}

	public Set<EqNode> getEquivalenceRepresentatives() {
		final Set<EqNode> result = new HashSet<>();
		for (final EqGraphNode<EqNode, IProgramVarOrConst> egn : mEqNodeToEqGraphNodeMap.values()) {
			if (egn.getRepresentative() == egn) {
				result.add(egn.nodeIdentifier);
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
				result.add(egn.nodeIdentifier);
			}
		}
		return result;
	}

	// public VPDomain<ACTION> getDomain() {
	// return mDomain;
	// }

	public boolean mayEqual(final EqNode accessingNode1, final EqNode accessingNode2) {
		return accessingNode1 == accessingNode2 || !getDisEqualities()
				.contains(new VPDomainSymmetricPair<>(find(accessingNode1), find(accessingNode2)));
	}

	// private EqNode find(EqNode node) {
	// return mEqNodeToEqGraphNodeMap.get(node).find().nodeIdentifier.getEqNode();
	// }

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
		return mEqNodeToEqGraphNodeMap.get(id).find().nodeIdentifier;
	}

	// public boolean mayEqual(final EqNode accessingNode1, final EqNode accessingNode2) {
	// return mayEqual(new VPNodeIdentifier(accessingNode1), new VPNodeIdentifier(accessingNode2));
	// }

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

	@Override
	public Class<IProgramVar> getVariablesType() {
		return IProgramVar.class;
	}

	/**
	 * Returns true iff term1 _must_ equal term2 in this VPState.
	 * (In particular returns false if this VPState does not have any constraint on the
	 *  term1 and term2.)
	 */
	public boolean areEqual(final Term term1, final Term term2) {
		EqNode node1 = mPreAnalysis.getEqNode(term1);
		EqNode node2 = mPreAnalysis.getEqNode(term2);
		if (node1 == null || node2 == null) {
			// the analysis did not track at least one of the given terms
			return false;
		}
		return areEqual(node1, node2);
	}

	/**
	 * Returns true iff term1 and term2 _must_ be unequal in this VPState.
	 * (In particular returns false if this VPState does not have any constraint on the
	 *  term1 and term2.)
	 */
	public boolean areUnEqual(final Term term1, final Term term2) {
		EqNode node1 = mPreAnalysis.getEqNode(term1);
		EqNode node2 = mPreAnalysis.getEqNode(term2);
		if (node1 == null || node2 == null) {
			// the analysis did not track at least one of the given terms
			return false;
		}
		return areUnEqual(node1, node2);
	}
}
