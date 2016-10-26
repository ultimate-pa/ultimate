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

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

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
	
	private Set<VPDomainSymmetricPair<EqNode>> mDisEqualityMap = new HashSet<VPDomainSymmetricPair<EqNode>>();
	
	public VPDomain(final ILogger logger, ManagedScript script, 
			IUltimateServiceProvider services,
			final Set<EqGraphNode> eqGraphNodeSet, 
			final Map<Term, EqBaseNode> termToBaseNodeMap,
			final Map<Term, Set<EqFunctionNode>> termToFnNodeMap,
			final Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap) {
		mPost = new VPPostOperator(script, services);
		mMerge = new VPMergeOperator();
		mLogger = logger;
		mEqGraphNodeSet = eqGraphNodeSet;
		mTermToBaseNodeMap = termToBaseNodeMap;
		mTermToFnNodeMap = termToFnNodeMap;
		mEqNodeToEqGraphNodeMap = eqNodeToEqGraphNodeMap;
	}

	@Override
	public VPState createFreshState() {
		return new VPState(mEqGraphNodeSet, mTermToBaseNodeMap, mTermToFnNodeMap, mEqNodeToEqGraphNodeMap, mDisEqualityMap);
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

	private final class VPMergeOperator implements IAbstractStateBinaryOperator<VPState> {

		@Override
		public VPState apply(final VPState first, final VPState second) {
			final VPState rtr = first.union(second);
			if (mLogger.isDebugEnabled()) {
				final StringBuilder sb = new StringBuilder();
				sb.append("merge(");
				sb.append(first.toLogString());
				sb.append(',');
				sb.append(second.toLogString());
				sb.append(") = ");
				sb.append(rtr.toLogString());
				mLogger.debug(sb);
			}
			return rtr;
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

}
