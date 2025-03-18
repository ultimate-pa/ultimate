package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;

public class IcfgExecution {
	private final ArrayList<ExecutionStep> mSteps = new ArrayList<>();
	private final ExecutionStep mInitialStep;
	private ExecutionStep mFinalStep;

	public IcfgExecution(final ProgramState initialState, final IcfgLocation initialLocation) {
		mInitialStep = new ExecutionStep(initialState, null, initialLocation);
		mFinalStep = mInitialStep;
		mSteps.add(mInitialStep);
	}

	public void addStep(final ProgramState currentState, final IcfgLocation location) {
		mFinalStep = new ExecutionStep(currentState, mFinalStep, location);
		mSteps.add(mFinalStep);
	}

	public ExecutionStep getStep(final int stepNumber) {
		return mSteps.get(stepNumber);
	}

	public ExecutionStep getInitialStep() {
		return mInitialStep;
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder("   ");
		ExecutionStep currentStep = mInitialStep;

		// out.append(currentStep.toString().replace("\n", "\n "));
		while (currentStep != null) {
			out.append("\n-> (").append(currentStep.getLocation().getLabel()).append(",\n    ");
			out.append(currentStep.toString().replace("\n", "\n    ")).append(")");
			currentStep = currentStep.getNext();
		}

		return out.toString();
	}

	protected class ExecutionStep {
		private final ProgramState mState;
		private final IcfgLocation mLocation;
		private ExecutionStep mNextStep = null;
		private ExecutionStep mPreviousStep = null;

		public ExecutionStep(final ProgramState state, final ExecutionStep previousStep, final IcfgLocation location) {
			mPreviousStep = previousStep;
			mLocation = location;
			if (mPreviousStep != null) {
				mPreviousStep.mNextStep = this;
			}
			mState = state.clone();
		}

		public ExecutionStep getNext() {
			return mNextStep;
		}

		public ExecutionStep getPrevious() {
			return mPreviousStep;
		}

		public ProgramState getState() {
			return mState.clone();
		}

		public HashMap<IProgramVar, Object> getVariableValues() {
			return mState.getVariableValues();
		}

		public IcfgLocation getLocation() {
			return mLocation;
		}

		@Override
		public String toString() {
			return mState.toString();
		}
	}
}
