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

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Domain of variable partition.
 *
 * Note: This domain is work in progress and does not work.
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 */
public class VPDomain<ACTION extends IIcfgTransition<IcfgLocation>>
		implements IAbstractDomain<VPState<ACTION>, ACTION, IProgramVar> {

	private final VPPostOperator<ACTION> mPost;
	private final VPMergeOperator mMerge;
	private final ILogger mLogger;

	private final HashRelation<IProgramVarOrConst, EqFunctionNode> mArrayIdToEqFnNodes;

	private final ManagedScript mManagedScript;
	private final Map<Term, EqNode> mTermToEqNodeMap;
	private final VPDomainPreanalysis mPreAnalysis;
	private final VPStateFactory<ACTION> mVpStateFactory;
	private final IIcfgSymbolTable mSymboltable;
	private final VPTransFormulaStateBuilderPreparer mTfPreparer;
	private final VpTfStateFactory mTfStateFactory;

	public VPDomain(final ILogger logger, final ManagedScript script, final IUltimateServiceProvider services,
			final IIcfgSymbolTable symbolTable, final VPDomainPreanalysis preAnalysis,
			final VPTransFormulaStateBuilderPreparer tfPreparer) {
		assert script != null;
		mLogger = logger;
		mPreAnalysis = preAnalysis;
		mManagedScript = script;
		mArrayIdToEqFnNodes = preAnalysis.getArrayIdToFnNodeMap();
		mTermToEqNodeMap = preAnalysis.getTermToEqNodeMap();
		mMerge = new VPMergeOperator();
		mSymboltable = symbolTable;
		mTfPreparer = tfPreparer;
		mVpStateFactory = new VPStateFactory<>(this);
		mTfStateFactory = new VpTfStateFactory(tfPreparer, preAnalysis);
		mPost = new VPPostOperator(script, services, this);
	}

	@Override
	public VPState<ACTION> createFreshState() {
		return getVpStateFactory().createEmptyStateBuilder().build();
	}

	@Override
	public IAbstractStateBinaryOperator<VPState<ACTION>> getWideningOperator() {
		return mMerge;
	}

	@Override
	public IAbstractStateBinaryOperator<VPState<ACTION>> getMergeOperator() {
		return mMerge;
	}

	@Override
	public IAbstractPostOperator<VPState<ACTION>, ACTION, IProgramVar> getPostOperator() {
		return mPost;
	}

	@Override
	public int getDomainPrecision() {
		throw new UnsupportedOperationException("this domain has no precision");
	}

	private final class VPMergeOperator implements IAbstractStateBinaryOperator<VPState<ACTION>> {

		@Override
		public VPState<ACTION> apply(final VPState<ACTION> first, final VPState<ACTION> second) {
			return VPFactoryHelpers.disjoin(first, second, getVpStateFactory());
		}
	}

	public Map<Term, EqNode> getTermToEqNodeMap() {
		return mTermToEqNodeMap;
	}

	public HashRelation<IProgramVarOrConst, EqFunctionNode> getArrayIdToEqFnNodeMap() {
		return mArrayIdToEqFnNodes;
	}

	public HashRelation<IProgramVar, IProgramVar> getArrayToIndices() {
		// TODO: implement
		assert false;
		return null;
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public VPDomainPreanalysis getPreAnalysis() {
		return mPreAnalysis;
	}

	public VPStateFactory<ACTION> getVpStateFactory() {
		return mVpStateFactory;
	}

	public IIcfgSymbolTable getSymbolTable() {
		return mSymboltable;
	}

	public Set<EqNode> getLiteralEqNodes() {
		// TODO only compute this once!
		final Set<EqNode> literalSet = new HashSet<>();
		for (final EqNode eqNode : getTermToEqNodeMap().values()) {
			if (eqNode.isLiteral()) {
				literalSet.add(eqNode);
			}
		}
		return literalSet;
	}

	public VPTransFormulaStateBuilderPreparer getTfPreparer() {
		return mTfPreparer;
	}

	public VpTfStateFactory getTfStateFactory() {
		return mTfStateFactory;
	}

	@Override
	public VPState<ACTION> createTopState() {
		throw new UnsupportedOperationException("Not implemented: createTopState");
	}

	@Override
	public VPState<ACTION> createBottomState() {
		throw new UnsupportedOperationException("Not implemented: createBottomState");
	}
}
