package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation;

import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.ISearchStep;

public class SpeculativeSearchIterator<T extends ISearchStep<?, T>> {
	protected final class ResultTask implements ISpeculativeTask<T> {
		private final T mStep;

		private ResultTask(final T step) {
			mStep = step;
		}

		@Override
		public void complete(final boolean keepVariant) {
			throw new UnsupportedOperationException();
		}

		@Override
		public T getStep() {
			return mStep;
		}

		@Override
		public boolean isCanceled() {
			return false;
		}

		@Override
		public boolean isDone() {
			return true;
		}
	}

	protected final class Task implements ISpeculativeTask<T> {
		private final T mStep;
		private Optional<Boolean> mResult = Optional.empty();
		private volatile boolean mCanceled;

		private Task(final T step) {
			mStep = step;
		}

		private void cancel() {
			mCanceled = true;
		}

		@Override
		public void complete(final boolean keepVariant) {
			completeTask(this, keepVariant);
		}

		private boolean getResult() {
			return mResult.get();
		}

		@Override
		public T getStep() {
			return mStep;
		}

		@Override
		public boolean isCanceled() {
			return mCanceled;
		}

		@Override
		public boolean isDone() {
			return mStep.isDone();
		}

		private boolean isPending() {
			return !mResult.isPresent();
		}

		private void setResult(final boolean keepVariant) {
			mResult = Optional.of(keepVariant);
		}
	}

	private final ISpeculativeIterationObserver<T> mObserver;

	private final LinkedList<Task> mPending = new LinkedList<>();

	private T mCurrentStep;

	public SpeculativeSearchIterator(final T initialStep) {
		this(initialStep, new ISpeculativeIterationObserver<T>() {
		});
	}

	public SpeculativeSearchIterator(final T initialStep, final ISpeculativeIterationObserver<T> observer) {
		this.mObserver = observer;
		mCurrentStep = initialStep;
		if (mCurrentStep.isDone()) {
			observer.onSearchComplete(mCurrentStep);
		}
	}

	protected void completeTask(final Task task, final boolean keepVariant) {
		// Store the result to mark the task as not pending anymore
		if (!task.isPending()) {
			throw new IllegalStateException("task has already been completed");
		}
		task.setResult(keepVariant);

		// Result is for a canceled speculative step
		if (task.isCanceled()) {
			mObserver.onCanceledStepComplete(task.getStep(), keepVariant);
			return;
		}

		final int index = mPending.indexOf(task);
		if (index == -1) {
			throw new IllegalArgumentException();
		}

		// If the step is successful cancel all pending speculative tasks
		// that depend on it's failure
		if (keepVariant && index + 1 < mPending.size()) {
			final List<Task> invalidSpeculativeTasks = mPending.subList(index + 1, mPending.size());
			invalidSpeculativeTasks.forEach(t -> t.cancel());
			mObserver.onTasksCanceled(invalidSpeculativeTasks);
			invalidSpeculativeTasks.clear();
		}

		// If this step does not depend on the failure of a preceding still
		// pending task we can process it's result (and all available
		// results of remaining immediate successor steps)
		if (index == 0) {
			removeCompletedTasks();
		}
	}

	public T getCurrentStep() {
		return mCurrentStep != null ? mCurrentStep : mPending.peekFirst().getStep();
	}

	public ISpeculativeTask<T> getNextTask() {
		// No speculation required
		if (mCurrentStep != null) {
			// Search completed
			if (mCurrentStep.isDone()) {
				return new ResultTask(mCurrentStep);
			}

			mObserver.onStepBegin(mCurrentStep);
			final Task task = new Task(mCurrentStep);
			mPending.add(task);
			mCurrentStep = null;
			return task;
		}

		// The current step is already being tested, create and return a
		// successor step assuming the current step will not be successful.
		// Note that the latest speculative step may not have another variant to
		// test, but we must not return a step that is done unless it is the
		// final result.
		if (!mPending.peekLast().isDone()) {
			final Task nextSpeculativeTask = new Task(mPending.peekLast().getStep().next(false));
			mPending.addLast(nextSpeculativeTask);
			if (!nextSpeculativeTask.isDone()) {
				return nextSpeculativeTask;
			}
		}

		// No further speculative step possible,
		// but that may change if one of the pending steps succeeds
		return null;
	}

	public int getPendingTaskCount() {
		return mPending.size();
	}

	public boolean isDone() {
		return mCurrentStep != null && mCurrentStep.isDone();
	}

	private void removeCompletedTasks() {
		Task latestCompletedTask = null;
		while (!mPending.isEmpty()) {
			final Task task = mPending.peekFirst();
			if (task.isDone()) {
				// Search completed
				mPending.clear();
				mCurrentStep = task.getStep();
				mObserver.onSearchComplete(mCurrentStep);
				return;
			}
			if (task.isPending()) {
				mObserver.onStepBegin(task.getStep());
				return;
			}
			if (latestCompletedTask != null) {
				mObserver.onStepBegin(task.getStep());
			}
			mObserver.onStepComplete(task.getStep(), task.getResult());
			mPending.removeFirst();
			latestCompletedTask = task;
		}

		// No pending tasks remain, compute the next step
		if (latestCompletedTask != null) {
			mCurrentStep = latestCompletedTask.getStep().next(latestCompletedTask.getResult());
		}
	}
}
