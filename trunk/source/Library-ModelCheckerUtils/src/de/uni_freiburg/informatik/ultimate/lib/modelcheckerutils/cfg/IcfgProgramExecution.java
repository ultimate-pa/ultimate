/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.results.NoBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.ProgramExecutionFormatter;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgProgramExecution implements IProgramExecution<IIcfgTransition<IcfgLocation>, Term> {

	private final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> mTrace;
	private final Map<Integer, ProgramState<Term>> mPartialProgramStateMapping;
	private final Map<TermVariable, Boolean>[] mBranchEncoders;
	private final boolean mIsConcurrent;

	public IcfgProgramExecution(final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders, final boolean isConcurrent) {
		assert partialProgramStateMapping != null;
		assert branchEncoders != null;
		assert trace != null;
		assert partialProgramStateMapping.size() - 1 <= trace.size();

		mIsConcurrent = isConcurrent;
		mTrace = trace;
		mPartialProgramStateMapping = partialProgramStateMapping;
		mBranchEncoders = branchEncoders;
	}

	public static IcfgProgramExecution create(final List<? extends IIcfgTransition<?>> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders) {
		return create(trace, partialProgramStateMapping, branchEncoders, null);
	}

	@SuppressWarnings("unchecked")
	public static IcfgProgramExecution create(final List<? extends IIcfgTransition<?>> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping) {
		return create(trace, partialProgramStateMapping,
				new ArrayList<Map<TermVariable, Boolean>>().toArray(new Map[0]), null);
	}

	public static IcfgProgramExecution create(final List<? extends IIcfgTransition<?>> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders, final List<IRelevanceInformation> relevanceInformation) {
		final boolean isConcurrent = isConcurrent(trace);
		final Map<String, Integer> threadIdMap;
		final int[] threadIds;
		if (isConcurrent) {
			threadIdMap = createThreadIds(trace);
			threadIds = createThreadIdsFromMap(trace, threadIdMap);
		} else {
			threadIdMap = null;
			threadIds = null;
		}
		return new IcfgProgramExecution(createATESequence(trace, relevanceInformation, threadIdMap, threadIds),
				partialProgramStateMapping, branchEncoders, threadIds != null);
	}

	private static int[] createThreadIdsFromMap(final List<? extends IIcfgTransition<?>> trace,
			final Map<String, Integer> threadIdMap) {
		final int[] rtr = new int[trace.size()];
		int i = 0;
		for (final IIcfgTransition<?> trans : trace) {
			final Integer id = threadIdMap.get(trans.getPrecedingProcedure());
			rtr[i] = id;
			++i;
		}

		return rtr;
	}

	private static boolean isConcurrent(final List<? extends IIcfgTransition<?>> trace) {
		return trace.stream().anyMatch(a -> a instanceof IIcfgForkTransitionThreadOther<?>
				|| a instanceof IIcfgJoinTransitionThreadOther<?> || a instanceof IIcfgForkTransitionThreadCurrent<?>
				|| a instanceof IIcfgJoinTransitionThreadCurrent<?>);
	}

	private static final Map<String, Integer> createThreadIds(final List<? extends IIcfgTransition<?>> trace) {
		int nextThreadId = -1;
		final Map<String, Integer> threadIdMap = new HashMap<>();
		for (final IIcfgTransition<?> trans : trace) {
			Integer id = threadIdMap.get(trans.getPrecedingProcedure());
			if (id == null) {
				id = nextThreadId;
				nextThreadId++;
				threadIdMap.put(trans.getPrecedingProcedure(), id);
			}
		}
		return threadIdMap;
	}

	/**
	 * Convert a sequence of {@link IIcfgTransition}s and a sequence of {@link IRelevanceInformation}s together with
	 * matching thread ids to a sequence of {@link AtomicTraceElement}s.
	 *
	 * @param mThreadIds2
	 *
	 */
	private static List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> createATESequence(
			final List<? extends IIcfgTransition<?>> trace, final List<IRelevanceInformation> relevanceInformation,
			final Map<String, Integer> threadIdMap, final int[] threadIds) {
		assert trace != null;
		assert relevanceInformation == null || trace.size() == relevanceInformation.size() : "incompatible sizes";
		assert threadIds == null || threadIds.length == trace.size();
		final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> translatedAtes = new ArrayList<>();
		for (int i = 0; i < trace.size(); i++) {
			@SuppressWarnings("unchecked")
			final IIcfgTransition<IcfgLocation> te = (IIcfgTransition<IcfgLocation>) trace.get(i);
			final AtomicTraceElementBuilder<IIcfgTransition<IcfgLocation>> ateBuilder =
					new AtomicTraceElementBuilder<>();
			ateBuilder.setStepAndElement(te);
			ateBuilder.setProcedures(te.getPrecedingProcedure(), te.getSucceedingProcedure());
			if (threadIdMap != null) {
				ateBuilder.setThreadId(threadIds[i]);
			}
			if (relevanceInformation != null) {
				ateBuilder.setRelevanceInformation(relevanceInformation.get(i));
			}

			if (te instanceof IIcfgForkTransitionThreadOther<?>) {
				if (threadIdMap != null) {
					final Integer forkedProcedureId = threadIdMap.get(te.getTarget().getProcedure());
					assert forkedProcedureId != null;
					ateBuilder.setForkedThreadId(forkedProcedureId);
				}
				ateBuilder.setStepInfo(StepInfo.FORK);
				assert threadIdMap != null;
			} else if (te instanceof IIcfgForkTransitionThreadCurrent<?>) {
				if (threadIdMap != null) {
					final Integer forkedProcedureId = threadIdMap.get(te.getTarget().getProcedure());
					assert forkedProcedureId != null;
					ateBuilder.setForkedThreadId(forkedProcedureId);
				}
				ateBuilder.setStepInfo(StepInfo.FORK);
				assert threadIdMap != null;
			} else if (te instanceof IIcfgJoinTransitionThreadOther<?>) {
				ateBuilder.setStepInfo(StepInfo.JOIN);
				assert threadIdMap != null;
			} else if (te instanceof IIcfgJoinTransitionThreadCurrent<?>) {
				ateBuilder.setStepInfo(StepInfo.JOIN);
				assert threadIdMap != null;
			} else if (te instanceof IIcfgCallTransition<?>) {
				ateBuilder.setStepInfo(StepInfo.PROC_CALL);
			} else if (te instanceof IIcfgReturnTransition<?, ?>) {
				ateBuilder.setStepInfo(StepInfo.PROC_RETURN);
			}
			translatedAtes.add(ateBuilder.build());
		}
		return translatedAtes;
	}

	public Map<TermVariable, Boolean>[] getBranchEncoders() {
		return mBranchEncoders;
	}

	@Override
	public int getLength() {
		return mTrace.size();
	}

	@Override
	public AtomicTraceElement<IIcfgTransition<IcfgLocation>> getTraceElement(final int i) {
		return mTrace.get(i);
	}

	@Override
	public ProgramState<Term> getProgramState(final int i) {
		if (i < 0 || i >= mTrace.size()) {
			throw new IllegalArgumentException("out of range");
		}
		return mPartialProgramStateMapping.get(i);
	}

	@Override
	public ProgramState<Term> getInitialProgramState() {
		return mPartialProgramStateMapping.get(-1);
	}

	@Override
	public String toString() {
		final ProgramExecutionFormatter<IIcfgTransition<IcfgLocation>, Term> pef =
				new ProgramExecutionFormatter<>(new IcfgBacktranslationValueProvider());
		return pef.formatProgramExecution(this);
	}

	@Override
	public Class<Term> getExpressionClass() {
		return Term.class;
	}

	@Override
	public Class<? extends IIcfgTransition<IcfgLocation>> getTraceElementClass() {
		return IcfgEdge.class;
	}

	public Class<? extends IIcfgTransition<? extends IcfgLocation>> getsTraceElementClass() {
		return IcfgEdge.class;
	}

	public IcfgProgramExecution addRelevanceInformation(final List<IRelevanceInformation> relevanceInformation) {
		final List<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> newAtes = new ArrayList<>();
		final Iterator<AtomicTraceElement<IIcfgTransition<IcfgLocation>>> iter = mTrace.iterator();
		final Iterator<IRelevanceInformation> relIter = relevanceInformation.iterator();
		boolean isConcurrent = false;
		while (iter.hasNext()) {
			final AtomicTraceElement<IIcfgTransition<IcfgLocation>> ate =
					AtomicTraceElementBuilder.from(iter.next()).setRelevanceInformation(relIter.next()).build();
			isConcurrent = isConcurrent || ate.hasThreadId();
			newAtes.add(ate);
		}
		return new IcfgProgramExecution(newAtes, mPartialProgramStateMapping, mBranchEncoders, isConcurrent);
	}

	@Override
	public IBacktranslationValueProvider<IIcfgTransition<IcfgLocation>, Term> getBacktranslationValueProvider() {
		return new NoBacktranslationValueProvider<>();
	}

	@Override
	public boolean isConcurrent() {
		return mIsConcurrent;
	}

}
