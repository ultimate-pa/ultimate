/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy;

import java.util.List;
import java.util.NoSuchElementException;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpgStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpAbStrategyModule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class BasicRefinementStrategy<L extends IIcfgTransition<?>> implements ITARefinementStrategy<L> {

	private static final int DEFAULT_INTERPOLANT_THRESHOLD = 2;

	private final ITraceCheckStrategyModule<L, ?>[] mTraceChecks;
	private final IIpgStrategyModule<?, L>[] mInterpolantGenerators;
	private final IIpAbStrategyModule<L> mInterpolantAutomatonBuilder;
	private int mCurrentIndexTraceCheck;
	private int mCurrentIndexInterpolantGenerator;

	private final RefinementStrategyExceptionBlacklist mBlacklist;

	private final IPredicateUnifier mDefaultPredicateUnifier;

	public BasicRefinementStrategy(final StrategyFactory<L>.StrategyModuleFactory factory,
			final ITraceCheckStrategyModule<L, ?>[] traceChecks, final IIpgStrategyModule<?, L>[] interpolantGenerators,
			final IIpAbStrategyModule<L> interpolantAutomatonBuilder,
			final RefinementStrategyExceptionBlacklist blacklist) {
		mTraceChecks = Objects.requireNonNull(traceChecks);
		mInterpolantGenerators = Objects.requireNonNull(interpolantGenerators);
		mInterpolantAutomatonBuilder = Objects.requireNonNull(interpolantAutomatonBuilder);
		mBlacklist = Objects.requireNonNull(blacklist);
		mCurrentIndexTraceCheck = 0;
		mCurrentIndexInterpolantGenerator = 0;
		mDefaultPredicateUnifier = factory.getDefaultPredicateUnifier();
	}

	public BasicRefinementStrategy(final StrategyFactory<L>.StrategyModuleFactory factory,
			final StrategyModules<L> modules, final RefinementStrategyExceptionBlacklist blacklist) {
		this(factory, modules.mTraceChecks, modules.mInterpolantGenerators, modules.mInterpolantAutomatonBuilder,
				blacklist);
	}

	public BasicRefinementStrategy(final StrategyFactory<L>.StrategyModuleFactory factory,
			final IIpTcStrategyModule<?, L>[] traceChecks, final IIpAbStrategyModule<L> interpolantAutomatonBuilder,
			final RefinementStrategyExceptionBlacklist blacklist) {
		this(factory, traceChecks, traceChecks, interpolantAutomatonBuilder, blacklist);
	}

	@Override
	public String getName() {
		return getClass().getSimpleName();
	}

	@Override
	public boolean hasNextFeasilibityCheck() {
		return mCurrentIndexTraceCheck < mTraceChecks.length;
	}

	@Override
	public ITraceCheckStrategyModule<L, ?> nextFeasibilityCheck() {
		if (mCurrentIndexTraceCheck < mTraceChecks.length) {
			return mTraceChecks[mCurrentIndexTraceCheck++];
		}
		throw new NoSuchElementException();
	}

	@Override
	public boolean hasNextInterpolantGenerator(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		if (needsMoreInterpolants(perfectIpps, imperfectIpps)) {
			return mCurrentIndexInterpolantGenerator < mInterpolantGenerators.length;
		}
		return false;

	}

	@Override
	public IIpgStrategyModule<?, L> nextInterpolantGenerator() {
		if (mCurrentIndexInterpolantGenerator < mInterpolantGenerators.length) {
			return mInterpolantGenerators[mCurrentIndexInterpolantGenerator++];
		}
		throw new NoSuchElementException();
	}

	@Override
	public IIpAbStrategyModule<L> getInterpolantAutomatonBuilder() {
		return mInterpolantAutomatonBuilder;
	}

	@Override
	public RefinementStrategyExceptionBlacklist getExceptionBlacklist() {
		return mBlacklist;
	}

	@Override
	public IHoareTripleChecker getHoareTripleChecker(final IRefinementEngine<L, ?> engine) {
		return null;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier(final IRefinementEngine<L, ?> engine) {
		return mDefaultPredicateUnifier;
	}

	@Override
	public List<QualifiedTracePredicates> mergeInterpolants(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		return DataStructureUtils.concat(perfectIpps, imperfectIpps);
	}

	/**
	 * Override this method to provide a custom rule to return interpolants. The default rule is as follows. We do not
	 * try to find more interpolants if ...
	 * <ul>
	 * <li>we already have a perfect sequence, or
	 * <li>if we have at least 2 imperfect sequences.
	 * </ul>
	 *
	 * @return true if we should try with another interpolant generator, false if we should build an automaton from the
	 *         interpolants we have.
	 */
	protected boolean needsMoreInterpolants(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		if (!perfectIpps.isEmpty()) {
			return false;
		}
		return imperfectIpps.size() < DEFAULT_INTERPOLANT_THRESHOLD;
	}

	protected ITraceCheckStrategyModule<L, ?>[] getTraceCheckModules() {
		return mTraceChecks;
	}

	protected IIpgStrategyModule<?, L>[] getInterpolantGeneratorModules() {
		return mInterpolantGenerators;
	}

	protected IIpAbStrategyModule<L> getInterpolantAutomatonBuilderModule() {
		return mInterpolantAutomatonBuilder;
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 */
	public static final class StrategyModules<L extends IAction> {
		private final ITraceCheckStrategyModule<L, ?>[] mTraceChecks;
		private final IIpgStrategyModule<?, L>[] mInterpolantGenerators;
		private final IIpAbStrategyModule<L> mInterpolantAutomatonBuilder;

		public StrategyModules(final ITraceCheckStrategyModule<L, ?>[] traceChecks,
				final IIpgStrategyModule<?, L>[] interpolantGenerators,
				final IIpAbStrategyModule<L> interpolantAutomatonBuilder) {
			mTraceChecks = traceChecks;
			mInterpolantAutomatonBuilder = interpolantAutomatonBuilder;
			mInterpolantGenerators = interpolantGenerators;
		}
	}
}
