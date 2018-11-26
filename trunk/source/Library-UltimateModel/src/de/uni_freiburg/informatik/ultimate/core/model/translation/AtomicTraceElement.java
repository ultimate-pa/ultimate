/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.core.model.translation;

import java.util.EnumSet;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;

/**
 * An atomic trace element in the sense of a debugger trace of a program. It consists of an
 * {@link AtomicTraceElement#getTraceElement() trace element} , which is probably a statement of some program, and the
 * currently evaluated {@link AtomicTraceElement#getStep() part of this statement}.
 *
 * This class is used to display an error trace for the user.
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <TE>
 *            The type of the trace element and the step.
 */
public class AtomicTraceElement<TE> {

	/**
	 * StepInfo provides additional information for {@link AtomicTraceElement#getStep()}.
	 *
	 * This may be replaced by an actual object later, but for now it should be sufficient.
	 *
	 * @author dietsch@informatik.uni-freiburg.de
	 *
	 */
	public enum StepInfo {
		NONE("NONE"),

		CONDITION_EVAL_TRUE("COND TRUE"),

		CONDITION_EVAL_FALSE("COND FALSE"),

		PROC_CALL("CALL"),

		PROC_RETURN("RET"),

		ARG_EVAL("ARG"),

		EXPR_EVAL("EXPR"),

		FUNC_CALL("FCALL"),

		FORK("FORK"),

		JOIN("JOIN"),

		;

		private final String mText;

		StepInfo(final String text) {
			mText = text;
		}

		@Override
		public String toString() {
			return mText;
		}
	}

	private final TE mElement;
	private final TE mStep;
	private final IToString<TE> mToStringFunc;
	private final EnumSet<AtomicTraceElement.StepInfo> mStepInfo;
	private final IRelevanceInformation mRelevanceInformation;
	private final String mPrecedingProcedure;
	private final String mSucceedingProcedure;

	private final Integer mThreadId;
	private final Integer mForkedThreadId;

	private AtomicTraceElement(final TE element, final TE step, final EnumSet<AtomicTraceElement.StepInfo> info,
			final IToString<TE> toStringProvider, final IRelevanceInformation relInfo, final String precedingProcedure,
			final String succeedingProcedure, final Integer threadId, final Integer forkedThreadId) {
		assert element != null;
		assert step != null;
		assert info != null;
		assert toStringProvider != null;
		assert !(info.size() > 1 && info.contains(StepInfo.NONE)) : "You cannot combine NONE with other values: "
				+ element;
		assert info.size() > 0;
		assert !info.contains(StepInfo.FORK)
				|| forkedThreadId != null : "If this step is a fork, you must have a forked thread id: " + element;
		assert hasAnyStepInfo(info, StepInfo.PROC_CALL, StepInfo.PROC_RETURN) || threadId != null
				|| precedingProcedure == succeedingProcedure : "You must have same procedures except when you have threads or when this is a call or a return: "
						+ element;
		mElement = element;
		mStep = step;
		mStepInfo = info;
		mPrecedingProcedure = precedingProcedure;
		mSucceedingProcedure = succeedingProcedure;
		mToStringFunc = toStringProvider;
		mRelevanceInformation = relInfo;
		mThreadId = threadId;
		mForkedThreadId = forkedThreadId;
	}

	/**
	 * @return The statement which is currently executed. Is never null.
	 */
	public TE getTraceElement() {
		return mElement;
	}

	/**
	 * @return An expression or statement which is evaluated atomically as part of the evaluation of
	 *         {@link #getTraceElement()} or a statement that is equal to {@link #getTraceElement()} when
	 *         {@link #getTraceElement()} itself is evaluated atomically.
	 *
	 *         This is always a reference to some subtree of {@link #getTraceElement()}.
	 */
	public TE getStep() {
		return mStep;
	}

	public boolean hasStepInfo(final AtomicTraceElement.StepInfo info) {
		return mStepInfo.contains(info);
	}

	/**
	 * Check if the step info set contains any of the supplied step infos. If none are supplied, they are contained.
	 */
	public boolean hasAnyStepInfo(final AtomicTraceElement.StepInfo... infos) {
		return hasAnyStepInfo(getStepInfo(), infos);
	}

	public static boolean hasAnyStepInfo(final EnumSet<StepInfo> set, final AtomicTraceElement.StepInfo... infos) {
		if (infos == null || infos.length == 0) {
			return true;
		}
		for (final StepInfo info : infos) {
			if (set.contains(info)) {
				return true;
			}
		}
		return false;
	}

	public EnumSet<AtomicTraceElement.StepInfo> getStepInfo() {
		return EnumSet.copyOf(mStepInfo);
	}

	public boolean hasThreadId() {
		return mThreadId != null;
	}

	public int getThreadId() {
		return mThreadId.intValue();
	}

	public boolean isMainThread() {
		return mThreadId.intValue() == -1;
	}

	public int getForkedThreadId() {
		return mForkedThreadId.intValue();
	}

	public IRelevanceInformation getRelevanceInformation() {
		return mRelevanceInformation;
	}

	public String getPrecedingProcedure() {
		return mPrecedingProcedure;
	}

	public String getSucceedingProcedure() {
		return mSucceedingProcedure;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (mStepInfo.contains(StepInfo.NONE)) {
			sb.append(mToStringFunc.toString(getTraceElement()));
		} else {
			sb.append(getStepInfo());
			sb.append(" ");
			sb.append(mToStringFunc.toString(getStep()));
		}

		if (hasThreadId()) {
			sb.append(" ");
			sb.append(getThreadId());
		}

		final IRelevanceInformation relInfo = getRelevanceInformation();
		if (relInfo != null) {
			sb.append(" ");
			sb.append(relInfo);
		}
		return sb.toString();
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public static final class AtomicTraceElementBuilder<TE> {
		private TE mElement;
		private TE mStep;
		private IToString<TE> mToStringFunc;
		private IRelevanceInformation mRelevanceInformation;
		private String mPrecedingProcedure;
		private String mSucceedingProcedure;
		private Integer mThreadId;

		private EnumSet<AtomicTraceElement.StepInfo> mStepInfo;
		private Integer mForkedThreadId;

		/**
		 * Create an empty {@link AtomicTraceElementBuilder}
		 */
		public AtomicTraceElementBuilder() {
			mToStringFunc = a -> a.toString();
			mStepInfo = EnumSet.of(StepInfo.NONE);
		}

		private AtomicTraceElementBuilder(final AtomicTraceElement<TE> old) {
			mToStringFunc = old.mToStringFunc;
			mStepInfo = EnumSet.copyOf(old.mStepInfo);
			mPrecedingProcedure = old.mPrecedingProcedure;
			mSucceedingProcedure = old.mSucceedingProcedure;
			mStep = old.mStep;
			mElement = old.mElement;
			mThreadId = old.mThreadId;
			mRelevanceInformation = old.mRelevanceInformation;
			mForkedThreadId = old.mForkedThreadId;
		}

		/**
		 * Create an {@link AtomicTraceElementBuilder} that is initialized with the values of an
		 * {@link AtomicTraceElement}.
		 */
		public static <TE> AtomicTraceElementBuilder<TE> from(final AtomicTraceElement<TE> old) {
			return new AtomicTraceElementBuilder<>(old);
		}

		/**
		 * Create a new {@link AtomicTraceElementBuilder} by using all information from an {@link AtomicTraceElement}
		 * except for step and element, which are replaced by the second argument.
		 */
		public static <TE> AtomicTraceElementBuilder<TE> fromReplaceElementAndStep(final AtomicTraceElement<?> old,
				final TE elem) {
			final AtomicTraceElementBuilder<TE> rtr = new AtomicTraceElementBuilder<TE>().setStepAndElement(elem)
					.setStepInfo(old.getStepInfo()).setRelevanceInformation(old.getRelevanceInformation())
					.setProcedures(old.getPrecedingProcedure(), old.getSucceedingProcedure());
			if (old.hasThreadId()) {
				rtr.setThreadId(old.getThreadId());
			}
			if (old.hasStepInfo(StepInfo.FORK)) {
				rtr.setForkedThreadId(old.getForkedThreadId());
			}
			return rtr;
		}

		/**
		 * Create a new {@link AtomicTraceElementBuilder} by using all information from an {@link AtomicTraceElement}
		 * except for step and element, which are replaced by the second argument.
		 */
		public static <TE> AtomicTraceElementBuilder<TE> fromReplaceElementAndStep(final AtomicTraceElement<?> old,
				final TE elem, final TE step) {
			final AtomicTraceElementBuilder<TE> rtr = new AtomicTraceElementBuilder<TE>().setElement(elem).setStep(step)
					.setStepInfo(old.getStepInfo()).setRelevanceInformation(old.getRelevanceInformation())
					.setProcedures(old.getPrecedingProcedure(), old.getSucceedingProcedure());
			if (old.hasThreadId()) {
				rtr.setThreadId(old.getThreadId());
			}
			if (old.hasStepInfo(StepInfo.FORK)) {
				rtr.setForkedThreadId(old.getForkedThreadId());
			}
			return rtr;
		}

		public AtomicTraceElement<TE> build() {
			return new AtomicTraceElement<>(mElement, mStep, mStepInfo, mToStringFunc, mRelevanceInformation,
					mPrecedingProcedure, mSucceedingProcedure, mThreadId, mForkedThreadId);
		}

		public AtomicTraceElementBuilder<TE> setElement(final TE element) {
			mElement = element;
			return this;
		}

		public AtomicTraceElementBuilder<TE> setStep(final TE step) {
			mStep = step;
			return this;
		}

		public AtomicTraceElementBuilder<TE> setStepAndElement(final TE step) {
			mStep = step;
			mElement = step;
			return this;
		}

		public AtomicTraceElementBuilder<TE> setToStringFunc(final IToString<TE> toStringFunc) {
			mToStringFunc = Objects.requireNonNull(toStringFunc);
			return this;
		}

		public AtomicTraceElementBuilder<TE> addStepInfo(final StepInfo... stepInfo) {
			if (stepInfo == null || stepInfo.length == 0) {
				return this;
			}
			if (stepInfo.length == 1 && stepInfo[0] == StepInfo.NONE) {
				mStepInfo = EnumSet.of(StepInfo.NONE);
				return this;
			}

			if (mStepInfo.contains(StepInfo.NONE)) {
				mStepInfo.clear();
			}

			for (final StepInfo info : stepInfo) {
				if (info == StepInfo.NONE) {
					throw new IllegalArgumentException("Cannot combine NONE with any other value");
				}
				mStepInfo.add(info);
			}
			return this;
		}

		public AtomicTraceElementBuilder<TE> setStepInfo(final StepInfo... stepInfo) {
			if (stepInfo == null || stepInfo.length == 0) {
				mStepInfo = EnumSet.of(StepInfo.NONE);
				return this;
			}
			mStepInfo.clear();
			for (final StepInfo info : stepInfo) {
				mStepInfo.add(info);
			}
			if (mStepInfo.size() > 1 && mStepInfo.contains(StepInfo.NONE)) {
				throw new IllegalArgumentException("Cannot combine NONE with any other value");
			}
			return this;
		}

		public AtomicTraceElementBuilder<TE> setStepInfo(final EnumSet<StepInfo> stepInfo) {
			return setStepInfo(stepInfo.toArray(new StepInfo[stepInfo.size()]));
		}

		public AtomicTraceElementBuilder<TE> setRelevanceInformation(final IRelevanceInformation relevanceInformation) {
			mRelevanceInformation = relevanceInformation;
			return this;
		}

		public AtomicTraceElementBuilder<TE> setProcedures(final String precedingProcedure,
				final String succeedingProcedure) {
			mPrecedingProcedure = precedingProcedure;
			mSucceedingProcedure = succeedingProcedure;
			return this;
		}

		public AtomicTraceElementBuilder<TE> setThreadId(final int threadId) {
			mThreadId = threadId;
			return this;
		}

		public AtomicTraceElementBuilder<TE> setForkedThreadId(final int threadId) {
			mForkedThreadId = threadId;
			return this;
		}

	}
}
