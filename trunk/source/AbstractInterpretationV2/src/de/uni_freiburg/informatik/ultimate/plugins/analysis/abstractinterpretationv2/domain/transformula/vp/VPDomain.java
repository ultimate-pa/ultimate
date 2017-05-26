/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Yu-Wen Chen (yuwenchen1105@gmail.com
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPFactoryHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPStateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VpTfStateFactory;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

/**
 * Domain of variable partition.
 *
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 */
public class VPDomain<ACTION extends IIcfgTransition<IcfgLocation>>
		implements IAbstractDomain<EqConstraint<ACTION, EqNode, EqFunction>, ACTION, IProgramVarOrConst> {

	private final VPPostOperator<ACTION> mPost;
	private final VPMergeOperator mMerge;
	private final ILogger mLogger;

	private final ManagedScript mManagedScript;
	private final VPDomainPreanalysis mPreAnalysis;
	private final IIcfgSymbolTable mSymboltable;
	private final VPTfStateBuilderPreparer mTfPreparer;
	private final boolean mDebugMode;

	public VPDomain(final ILogger logger, final ManagedScript script, final IUltimateServiceProvider services,
			final IIcfgSymbolTable symbolTable, final VPDomainPreanalysis preAnalysis,
			final VPTfStateBuilderPreparer tfPreparer) {
		assert script != null;
		mLogger = logger;
		mPreAnalysis = preAnalysis;
		mManagedScript = script;
		mMerge = new VPMergeOperator();
		mSymboltable = symbolTable;
		mTfPreparer = tfPreparer;
		mPost = new VPPostOperator<>(script, services, this);
		mDebugMode = mPreAnalysis.isDebugMode();
	}

	@Override
	public IAbstractStateBinaryOperator<VPState<ACTION>> getWideningOperator() {
		return mMerge;
	}

	@Override
	public IAbstractPostOperator<VPState<ACTION>, ACTION, IProgramVarOrConst> getPostOperator() {
		return mPost;
	}

	private final class VPMergeOperator implements IAbstractStateBinaryOperator<VPState<ACTION>> {
		@Override
		public VPState<ACTION> apply(final VPState<ACTION> first, final VPState<ACTION> second) {
			return VPFactoryHelpers.disjoin(first, second, getVpStateFactory());
		}
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
		for (final EqNode eqNode : mPreAnalysis.getAllEqNodes()) {
			if (eqNode.isLiteral()) {
				literalSet.add(eqNode);
			}
		}
		return literalSet;
	}

	public VPTfStateBuilderPreparer getTfPreparer() {
		return mTfPreparer;
	}

	public VpTfStateFactory getTfStateFactory() {
		return mTfStateFactory;
	}

	@Override
	public VPState<ACTION> createTopState() {
		return getVpStateFactory().createEmptyStateBuilder().build();
	}

	@Override
	public VPState<ACTION> createBottomState() {
		throw new UnsupportedOperationException("Not implemented: createBottomState");
	}

	public boolean isDebugMode() {
		return mDebugMode;
	}

	public Benchmark getVpBenchmark() {
		return mPreAnalysis.getBenchmark();
	}
}
