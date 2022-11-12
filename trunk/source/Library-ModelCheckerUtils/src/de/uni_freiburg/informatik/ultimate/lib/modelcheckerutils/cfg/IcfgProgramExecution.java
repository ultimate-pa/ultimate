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
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.lib.results.NoBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.ProgramExecutionFormatter;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgProgramExecution<L extends IAction> implements IProgramExecution<L, Term> {

	private final List<AtomicTraceElement<L>> mTrace;
	private final Map<Integer, ProgramState<Term>> mPartialProgramStateMapping;
	private final Map<TermVariable, Boolean>[] mBranchEncoders;
	private final boolean mIsConcurrent;
	private final Class<L> mTransitionClazz;

	public IcfgProgramExecution(final List<AtomicTraceElement<L>> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders, final boolean isConcurrent,
			final Class<L> transitionClazz) {
		assert partialProgramStateMapping != null;
		assert branchEncoders != null;
		assert trace != null;
		assert partialProgramStateMapping.size() - 1 <= trace.size();

		mIsConcurrent = isConcurrent;
		mTrace = trace;
		mPartialProgramStateMapping = partialProgramStateMapping;
		assert isProgramStateMappingInRange(trace, partialProgramStateMapping);
		mBranchEncoders = branchEncoders;
		mTransitionClazz = transitionClazz;
	}

	private boolean isProgramStateMappingInRange(final List<AtomicTraceElement<L>> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping) {
		for (final Entry<Integer, ProgramState<Term>> entry : partialProgramStateMapping.entrySet()) {
			if (entry.getKey() < -1) {
				assert false : "Position of state below -1: " + entry;
				return false;
			} else if (entry.getKey() >= trace.size()) {
				assert false : "Position of state above end of trace: " + entry;
				return false;
			}
			// other positions are fine
		}
		// no violations, every entry is in range
		return true;
	}

	@SuppressWarnings("unchecked")
	public static <L extends IAction> IcfgProgramExecution<L> create(final Class<L> transitionClazz) {
		return create(Collections.emptyList(), Collections.emptyMap(),
				new ArrayList<Map<TermVariable, Boolean>>().toArray(new Map[0]), null, transitionClazz);
	}

	public static <L extends IAction> IcfgProgramExecution<L> create(final List<L> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders) {
		return create(trace, partialProgramStateMapping, branchEncoders, null, getClassFromTrace(trace));
	}

	public static <L extends IAction> IcfgProgramExecution<L> create(final List<L> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders, final Class<L> clazz) {
		return create(trace, partialProgramStateMapping, branchEncoders, null, clazz);
	}

	@SuppressWarnings("unchecked")
	private static <L extends IAction> Class<L> getClassFromTrace(final List<L> trace) {
		return (Class<L>) trace.stream().findFirst()
				.orElseThrow(() -> new UnsupportedOperationException("Empty trace is not supported")).getClass();
	}

	@SuppressWarnings("unchecked")
	public static <L extends IAction> Class<L>
			getClassFromAtomicTraceElements(final List<AtomicTraceElement<L>> trace) {
		return (Class<L>) trace.stream().findFirst()
				.orElseThrow(() -> new UnsupportedOperationException("Empty trace is not supported")).getTraceElement()
				.getClass();
	}

	@SuppressWarnings("unchecked")
	public static <L extends IAction> IcfgProgramExecution<L> create(final List<L> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping) {
		return create(trace, partialProgramStateMapping,
				new ArrayList<Map<TermVariable, Boolean>>().toArray(new Map[0]), null, getClassFromTrace(trace));
	}

	@SuppressWarnings("unchecked")
	public static <L extends IAction> IcfgProgramExecution<L> create(final List<L> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping, final Class<L> clazz) {
		return create(trace, partialProgramStateMapping,
				new ArrayList<Map<TermVariable, Boolean>>().toArray(new Map[0]), null, clazz);
	}

	public static <L extends IAction> IcfgProgramExecution<L> create(final List<L> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders, final List<IRelevanceInformation> relevanceInformation) {
		return create(trace, partialProgramStateMapping, branchEncoders, relevanceInformation,
				getClassFromTrace(trace));
	}

	public static <L extends IAction> IcfgProgramExecution<L> create(final List<L> trace,
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping,
			final Map<TermVariable, Boolean>[] branchEncoders, final List<IRelevanceInformation> relevanceInformation,
			final Class<L> transitionClazz) {
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
		return new IcfgProgramExecution<>(createATESequence(trace, relevanceInformation, threadIdMap, threadIds),
				partialProgramStateMapping, branchEncoders, threadIds != null, transitionClazz);
	}

	private static int[] createThreadIdsFromMap(final List<? extends IAction> trace,
			final Map<String, Integer> threadIdMap) {
		final int[] rtr = new int[trace.size()];
		int i = 0;
		for (final IAction trans : trace) {
			final Integer id = threadIdMap.get(trans.getPrecedingProcedure());
			rtr[i] = id;
			++i;
		}

		return rtr;
	}

	private static boolean isConcurrent(final List<? extends IAction> trace) {
		return trace.stream().anyMatch(a -> a instanceof IIcfgForkTransitionThreadOther<?>
				|| a instanceof IIcfgJoinTransitionThreadOther<?> || a instanceof IIcfgForkTransitionThreadCurrent<?>
				|| a instanceof IIcfgJoinTransitionThreadCurrent<?>);
	}

	/**
	 * Construct mapping from procedures to thread IDs. The thread IDs are constructed for the output of Ultimate and
	 * may not coincide with the auxiliary thread id variables that are introduced by our "petrification" algorithm.
	 * <br />
	 * The fact that we assign each procedure a thread ID is not a soundness issue because the procedures that we see
	 * here are the "thread instances" and not the "thread templates" of our petrification. Thread instances can only be
	 * used once at a time and if a thread instance is used consecutively it will get the same thread ID again. But this
	 * is compatible to the Pthreads execution model.
	 *
	 */
	private static final Map<String, Integer> createThreadIds(final List<? extends IAction> trace) {
		int nextThreadId = 0;
		final Map<String, Integer> threadIdMap = new HashMap<>();
		if (trace.isEmpty()) {
			throw new UnsupportedOperationException("trace has length 0");
		}
		final String initialProcedure = trace.get(0).getPrecedingProcedure();
		threadIdMap.put(initialProcedure, nextThreadId);
		nextThreadId++;
		for (final IAction trans : trace) {
			final Integer id = threadIdMap.get(trans.getPrecedingProcedure());
			if (id == null) {
				throw new AssertionError("No thread ID for procedure " + trans.getPrecedingProcedure());
			}
			if (trans instanceof IcfgForkThreadOtherTransition) {
				final String forkedProcedure = trans.getSucceedingProcedure();
				if (!threadIdMap.containsKey(forkedProcedure)) {
					threadIdMap.put(forkedProcedure, nextThreadId);
					nextThreadId++;
				}
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
	private static <LETTER extends IAction> List<AtomicTraceElement<LETTER>> createATESequence(final List<LETTER> trace,
			final List<IRelevanceInformation> relevanceInformation, final Map<String, Integer> threadIdMap,
			final int[] threadIds) {
		assert trace != null;
		assert relevanceInformation == null || trace.size() == relevanceInformation.size() : "incompatible sizes";
		assert threadIds == null || threadIds.length == trace.size();
		final List<AtomicTraceElement<LETTER>> translatedAtes = new ArrayList<>();
		for (int i = 0; i < trace.size(); i++) {
			final LETTER te = trace.get(i);
			final AtomicTraceElementBuilder<LETTER> ateBuilder = new AtomicTraceElementBuilder<>();
			ateBuilder.setStepAndElement(te);
			ateBuilder.setProcedures(te.getPrecedingProcedure(), te.getSucceedingProcedure());
			if (threadIdMap != null) {
				ateBuilder.setThreadId(threadIds[i]);
			}
			if (relevanceInformation != null) {
				ateBuilder.setRelevanceInformation(relevanceInformation.get(i));
			}

			if (te instanceof IIcfgForkTransitionThreadOther<?>) {
				final IIcfgTransition<?> teTrans = (IIcfgTransition<?>) te;
				if (threadIdMap != null) {
					final Integer forkedProcedureId = threadIdMap.get(teTrans.getTarget().getProcedure());
					assert forkedProcedureId != null;
					ateBuilder.setForkedThreadId(forkedProcedureId);
				}
				ateBuilder.setStepInfo(StepInfo.FORK);
				assert threadIdMap != null;
			} else if (te instanceof IIcfgForkTransitionThreadCurrent<?>) {
				final IIcfgTransition<?> teTrans = (IIcfgTransition<?>) te;
				if (threadIdMap != null) {
					final Integer forkedProcedureId = threadIdMap.get(teTrans.getTarget().getProcedure());
					assert forkedProcedureId != null;
					ateBuilder.setForkedThreadId(forkedProcedureId);
				}
				ateBuilder.setStepInfo(StepInfo.FORK);
				assert threadIdMap != null;
			} else if (te instanceof IIcfgJoinTransitionThreadOther<?>) {
				final IIcfgTransition<?> teTrans = (IIcfgTransition<?>) te;
				if (threadIdMap != null) {
					final Integer joinedThreadId = threadIdMap.get(teTrans.getSource().getProcedure());
					assert joinedThreadId != null;
					ateBuilder.setJoinedThreadId(joinedThreadId);
				}
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
	public AtomicTraceElement<L> getTraceElement(final int i) {
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
		final ProgramExecutionFormatter<L, Term> pef =
				new ProgramExecutionFormatter<>(new IcfgBacktranslationValueProvider<>());
		return pef.formatProgramExecution(this);
	}

	@Override
	public Class<Term> getExpressionClass() {
		return Term.class;
	}

	@Override
	public Class<? extends L> getTraceElementClass() {
		return mTransitionClazz;
	}

	public IcfgProgramExecution<L> addRelevanceInformation(final List<IRelevanceInformation> relevanceInformation) {
		final List<AtomicTraceElement<L>> newAtes = new ArrayList<>();
		final Iterator<AtomicTraceElement<L>> iter = mTrace.iterator();
		final Iterator<IRelevanceInformation> relIter = relevanceInformation.iterator();
		boolean isConcurrent = false;
		while (iter.hasNext()) {
			final AtomicTraceElement<L> ate =
					AtomicTraceElementBuilder.from(iter.next()).setRelevanceInformation(relIter.next()).build();
			isConcurrent = isConcurrent || ate.hasThreadId();
			newAtes.add(ate);
		}
		return new IcfgProgramExecution<>(newAtes, mPartialProgramStateMapping, mBranchEncoders, isConcurrent,
				mTransitionClazz);
	}

	@Override
	public IBacktranslationValueProvider<L, Term> getBacktranslationValueProvider() {
		return new NoBacktranslationValueProvider<>();
	}

	@Override
	public boolean isConcurrent() {
		return mIsConcurrent;
	}

}
