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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
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
	private final HashRelation<IProgramVarOrConst, EqFunctionNode> mArrayIdToEqFnNodes;
	private final Map<EqNode, EqGraphNode> mEqNodeToEqGraphNodeMap;
	private Set<VPDomainSymmetricPair<EqGraphNode>> mDisEqualityMap;
	
	private final VPStateTop mTopState;
	private final VPStateBottom mBottomState;
	private final ManagedScript mManagedScript;
	private final Boogie2SMT mBoogie2Smt;
	private final Map<Term, EqNode> mTermToEqNodeMap;
	private final RCFGArrayIndexCollector mPreAnalysis;
	private final VPStateOperations mVpStateOperations;
	
	public VPDomain(final ILogger logger, 
			final ManagedScript script, 
			final IUltimateServiceProvider services,
			final Boogie2SMT boogie2smt, 
			final RCFGArrayIndexCollector preAnalysis) {
		assert script != null;
		mLogger = logger;
		mPreAnalysis = preAnalysis;
		mManagedScript = script;
		mEqGraphNodeSet = preAnalysis.getEqGraphNodeSet();
		mArrayIdToEqFnNodes = preAnalysis.getArrayIdToFnNodeMap();
		mEqNodeToEqGraphNodeMap = preAnalysis.getEqNodeToEqGraphNodeMap();
		mDisEqualityMap = new HashSet<>();
		mBottomState = new VPStateBottom(this);
		mTermToEqNodeMap = preAnalysis.getTermToEqNodeMap();
		mTopState = new VPStateTop(mEqNodeToEqGraphNodeMap, mDisEqualityMap, this);
		mPost = new VPPostOperator(script, services, this);
		mMerge = new VPMergeOperator();
		mBoogie2Smt = boogie2smt;
		mVpStateOperations = new VPStateOperations(this);
	}

	@Override
	public VPState createFreshState() {
		return new VPState(mEqNodeToEqGraphNodeMap, mDisEqualityMap, this);
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
			return getVpStateOperations().disjoin(first, second);
		}
	}
	
	boolean isArray(final Term term) {
		return getArrayIdToEqFnNodeMap()
				.getDomain().contains(getPreAnalysis().getIProgramVarOrConst(term));
	}

	public Set<EqGraphNode> getEqGraphNodeSet() {
		return mEqGraphNodeSet;
	}

	public Map<Term, EqNode> getTermToEqNodeMap() {
		return mTermToEqNodeMap;
	}

	public  HashRelation<IProgramVarOrConst, EqFunctionNode> getArrayIdToEqFnNodeMap() {
		return mArrayIdToEqFnNodes;
	}

	public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
		return mEqNodeToEqGraphNodeMap;
	}
	
	public HashRelation<IProgramVar, IProgramVar> getArrayToIndices() {
		// TODO: implement
		return null;
	}
	
	public VPStateTop getTopState() {
		return mTopState;
	}

	public VPStateBottom getBottomState() {
		return mBottomState;
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public EqNode getEqNodeFromTerm(Term term) {
		return mTermToEqNodeMap.get(term);
	}

	public RCFGArrayIndexCollector getPreAnalysis() {
		return mPreAnalysis;
	}
	
	public VPStateOperations getVpStateOperations() {
		return mVpStateOperations;
	}
}
