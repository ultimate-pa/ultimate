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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqStateFactory;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

/**
 * Domain of variable partition.
 *
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class VPDomain<ACTION extends IIcfgTransition<IcfgLocation>>
		implements IAbstractDomain<EqState<ACTION>, ACTION, IProgramVarOrConst> {

	private final EqPostOperator<ACTION> mPost;
	private final VPMergeOperator mMerge;
	private final ILogger mLogger;

	private final ManagedScript mManagedScript;
	private final VPDomainPreanalysis mPreAnalysis;
	private final IIcfgSymbolTable mSymboltable;
	private final boolean mDebugMode;

	private final EqConstraintFactory<ACTION, EqNode> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private final EqStateFactory<ACTION> mEqStateFactory;
	private final CfgSmtToolkit mCsToolkit;
	private final IUltimateServiceProvider mServices;

	public VPDomain(final ILogger logger, final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			 final VPDomainPreanalysis preAnalysis) {
		mLogger = logger;
		mPreAnalysis = preAnalysis;
		mManagedScript = csToolkit.getManagedScript();
		mMerge = new VPMergeOperator();
		mSymboltable = csToolkit.getSymbolTable();
		mCsToolkit = csToolkit;
		mServices = services;

		mEqNodeAndFunctionFactory = new EqNodeAndFunctionFactory(preAnalysis, mManagedScript);
		mEqConstraintFactory = new EqConstraintFactory<>(mEqNodeAndFunctionFactory, mServices, mCsToolkit);
		mEqStateFactory = new EqStateFactory<>(mEqNodeAndFunctionFactory, mEqConstraintFactory, mSymboltable);
		mEqConstraintFactory.setEqStateFactory(mEqStateFactory);

		mPost = new EqPostOperator<>(mEqNodeAndFunctionFactory, mEqConstraintFactory, mPreAnalysis);

		mDebugMode = mPreAnalysis.isDebugMode();
	}

	@Override
	public IAbstractStateBinaryOperator<EqState<ACTION>> getWideningOperator() {
		return mMerge;
	}

	@Override
	public IAbstractPostOperator<EqState<ACTION>, ACTION, IProgramVarOrConst> getPostOperator() {
		return mPost;
	}

	private final class VPMergeOperator implements IAbstractStateBinaryOperator<EqState<ACTION>> {
		@Override
		public EqState<ACTION> apply(final EqState<ACTION> first, final EqState<ACTION> second) {
			return first.union(second);
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

	public IIcfgSymbolTable getSymbolTable() {
		return mSymboltable;
	}

	@Override
	public EqState<ACTION> createTopState() {
		return mEqStateFactory.getTopState();
	}

	@Override
	public EqState<ACTION> createBottomState() {
		throw new UnsupportedOperationException("Not implemented: createBottomState");
	}

	public boolean isDebugMode() {
		return mDebugMode;
	}

	public Benchmark getVpBenchmark() {
		return mPreAnalysis.getBenchmark();
	}

	public EqStateFactory<ACTION> getEqStateFactory() {
		return mEqStateFactory;
	}

	@Override
	public boolean useHierachicalPre() {
		return true;
	}


}
