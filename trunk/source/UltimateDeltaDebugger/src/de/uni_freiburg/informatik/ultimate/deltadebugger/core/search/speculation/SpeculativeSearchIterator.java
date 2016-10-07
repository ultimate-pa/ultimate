package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation;

import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.SearchStep;

public class SpeculativeSearchIterator<T extends SearchStep<?, T>> {
	private final SpeculativeIterationObserver<T> observer;
	private final LinkedList<Task> pending = new LinkedList<>();
	private T currentStep;

	public SpeculativeSearchIterator(T initialStep, SpeculativeIterationObserver<T> observer) {
		this.observer = observer;
		currentStep = initialStep;
		if (currentStep.isDone()) {
			observer.onSearchComplete(currentStep);
		}
	}

	public SpeculativeSearchIterator(T initialStep) {
		this(initialStep, new SpeculativeIterationObserver<T>() {});
	}
	
	public int getPendingTaskCount() {
		return pending.size();
	}
	
	public boolean isDone() {
		return currentStep != null && currentStep.isDone();
	}
	
	public T getCurrentStep() {
		return currentStep != null ? currentStep : pending.peekFirst().getStep();
	}
	
	public SpeculativeTask<T> getNextTask() {
		// No speculation required
		if (currentStep != null) {
			// Search completed
			if (currentStep.isDone()) {
				return new ResultTask(currentStep);
			}

			observer.onStepBegin(currentStep);
			final Task task = new Task(currentStep);
			pending.add(task);
			currentStep = null;
			return task;
		}

		// The current step is already being tested, create and return a
		// successor step assuming the current step will not be successful.
		// Note that the latest speculative step may not have another variant to
		// test, but we must not return a step that is done unless it is the 
		// final result.
		if (!pending.peekLast().isDone()) {
			final Task nextSpeculativeTask = new Task(pending.peekLast().getStep().next(false));
			pending.addLast(nextSpeculativeTask);
			if (!nextSpeculativeTask.isDone()) {
				return nextSpeculativeTask;
			}
		}

		// No further speculative step possible,
		// but that may change if one of the pending steps succeeds
		return null;
	}
	
	
	protected void completeTask(Task task, boolean keepVariant) {
		// Store the result to mark the task as not pending anymore
		if (!task.isPending()) {
			throw new IllegalStateException("task has already been completed");
		}
		task.setResult(keepVariant);
		
		// Result is for a canceled speculative step
		if (task.isCanceled()) {
			observer.onCanceledStepComplete(task.getStep(), keepVariant);
			return;
		}
		
		final int index = pending.indexOf(task);
		if (index == -1) {
			throw new IllegalArgumentException();
		}

		// If the step is successful cancel all pending speculative tasks
		// that depend on it's failure
		if (keepVariant && index + 1 < pending.size()) {
			final List<Task> invalidSpeculativeTasks = pending.subList(index + 1, pending.size());
			invalidSpeculativeTasks.forEach(t -> t.cancel());
			observer.onTasksCanceled(invalidSpeculativeTasks);
			invalidSpeculativeTasks.clear();
		}

		// If this step does not depend on the failure of a preceding still
		// pending task we can process it's result (and all available
		// results of remaining immediate successor steps) 
		if (index == 0) {
			removeCompletedTasks();
		}
	}

	private void removeCompletedTasks() {
		Task latestCompletedTask = null;
		while (!pending.isEmpty()) {
			final Task task = pending.peekFirst();
			if (task.isDone()) {
				// Search completed
				pending.clear();
				currentStep = task.getStep();
				observer.onSearchComplete(currentStep);
				return;
			}
			if (task.isPending()) {
				observer.onStepBegin(task.getStep());
				return;
			}
			if (latestCompletedTask != null) {
				observer.onStepBegin(task.getStep());
			}
			observer.onStepComplete(task.getStep(), task.getResult());
			pending.removeFirst();
			latestCompletedTask = task;
		}

		// No pending tasks remain, compute the next step
		if (latestCompletedTask != null) {
			currentStep = latestCompletedTask.getStep().next(latestCompletedTask.getResult());
		}
	}

	
	protected class Task implements SpeculativeTask<T> {
		private final T step;
		private Optional<Boolean> result = Optional.empty();
		private volatile boolean canceled = false;

		private Task(T step) {
			this.step = step;
		}
		
		@Override
		public boolean isDone() {
			return step.isDone();
		}
		
		@Override
		public boolean isCanceled() {
			return canceled;
		}

		@Override
		public T getStep() {
			return step;
		}
		
		@Override
		public void complete(boolean keepVariant) {
			completeTask(this, keepVariant);
		}
		
		private boolean isPending() {
			return !result.isPresent();
		}
		
		private boolean getResult() {
			return result.get();
		}
		
		private void setResult(boolean keepVariant) {
			result = Optional.of(keepVariant);
		}
		
		private void cancel() {
			canceled = true;
		}
	}
	

	protected class ResultTask implements SpeculativeTask<T> {
		private final T step;

		private ResultTask(T step) {
			this.step = step;
		}
		
		@Override
		public T getStep() {
			return step;
		}

		@Override
		public boolean isDone() {
			return true;
		}
		
		@Override
		public boolean isCanceled() {
			return false;
		}

		@Override
		public void complete(boolean keepVariant) {
			throw new UnsupportedOperationException();
		}
	}
}