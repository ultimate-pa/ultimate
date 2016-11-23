/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Domain of variable partition.
 *
 * Note: This domain is work in progress and does not work.
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 */
public class VPDomain implements IAbstractDomain<VPState, CodeBlock, IProgramVar> {

	private final VPPostOperator mPost;
	private final VPMergeOperator mMerge;
	private final ILogger mLogger;
	
	private final Set<EqGraphNode> mEqGraphNodeSet;
	private final Map<Term, EqBaseNode> mTermToBaseNodeMap;
	private final Map<Term, Set<EqFunctionNode>> mTermToFnNodeMap;
	private final Map<EqNode, EqGraphNode> mEqNodeToEqGraphNodeMap;
	private Set<VPDomainSymmetricPair<EqNode>> mDisEqualityMap;
	
	private final VPStateTop mTopState;
	private final VPStateBottom mBottomState;
	private final ManagedScript mScript;
	private final Boogie2SMT mBoogie2Smt;
	private final Map<Term, EqNode> mTermToEqNode;
	
	public VPDomain(final ILogger logger, 
			final ManagedScript script, 
			final IUltimateServiceProvider services,
			Boogie2SMT boogie2smt, 
			final Set<EqGraphNode> eqGraphNodeSet, 
			final Map<Term, EqBaseNode> termToBaseNodeMap,
			final Map<Term, Set<EqFunctionNode>> termToFnNodeMap,
			final Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap,
			final Map<Term, EqNode> termToEqNode) {
		mLogger = logger;
		mEqGraphNodeSet = eqGraphNodeSet;
		mTermToBaseNodeMap = termToBaseNodeMap == null ? null : Collections.unmodifiableMap(termToBaseNodeMap);
		mTermToFnNodeMap = termToFnNodeMap == null ? null : Collections.unmodifiableMap(termToFnNodeMap);
		mEqNodeToEqGraphNodeMap = eqNodeToEqGraphNodeMap;
		mDisEqualityMap = new HashSet<VPDomainSymmetricPair<EqNode>>();
		mBottomState = new VPStateBottom(this);
		mTopState = new VPStateTop(mEqGraphNodeSet, mTermToBaseNodeMap, mTermToFnNodeMap, mEqNodeToEqGraphNodeMap, mDisEqualityMap, this);
		mPost = new VPPostOperator(script, services, this);
		mMerge = new VPMergeOperator();
		mScript = script;
		mBoogie2Smt = boogie2smt;
		mTermToEqNode = termToEqNode;
	}

	@Override
	public VPState createFreshState() {
		return new VPState(mEqGraphNodeSet, mEqNodeToEqGraphNodeMap, mDisEqualityMap, this);
	}

	@Override
	public IAbstractStateBinaryOperator<VPState> getWideningOperator() {
		return mMerge;
	}

	@Override
	public IAbstractStateBinaryOperator<VPState> getMergeOperator() {
		return mMerge;
	}

	@Override
	public IAbstractPostOperator<VPState, CodeBlock, IProgramVar> getPostOperator() {
		return mPost;
	}

	@Override
	public int getDomainPrecision() {
		throw new UnsupportedOperationException("this domain has no precision");
	}

	public Boogie2SMT getBoogie2Smt() {
		return mBoogie2Smt;
	}

	private final class VPMergeOperator implements IAbstractStateBinaryOperator<VPState> {

		@Override
		public VPState apply(final VPState first, final VPState second) {
			return first.disjoin(second);
		}
	}

	public Set<EqGraphNode> getmEqGraphNodeSet() {
		return mEqGraphNodeSet;
	}

	public Map<Term, EqBaseNode> getmTermToBaseNodeMap() {
		return mTermToBaseNodeMap;
	}

	public Map<Term, Set<EqFunctionNode>> getmTermToFnNodeMap() {
		return mTermToFnNodeMap;
	}

	public Map<EqNode, EqGraphNode> getmEqNodeToEqGraphNodeMap() {
		return mEqNodeToEqGraphNodeMap;
	}
	
	public HashRelation<IProgramVar, IProgramVar> getArrayToIndices() {
		// TODO: implement
		return null;
	}
	
	public VPStateTop getmTopState() {
		return mTopState;
	}

	public VPStateBottom getBottomState() {
		return mBottomState;
	}

	public ManagedScript getManagedScript() {
		return mScript;
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public EqNode getEqNodeFromTerm(Term term) {
		return mTermToEqNode.get(term);
	}
}
