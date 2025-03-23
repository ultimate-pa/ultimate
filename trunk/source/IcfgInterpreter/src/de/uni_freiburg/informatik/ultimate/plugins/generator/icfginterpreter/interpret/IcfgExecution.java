package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

public class IcfgExecution {
	private final ArrayList<ExecutionStep> mSteps = new ArrayList<>();
	private final ExecutionStep mInitialStep;
	private ExecutionStep mFinalStep;

	public IcfgExecution(final ProgramState initialState, final IcfgLocation initialLocation) {
		mInitialStep = new ExecutionStep(initialState, null, initialLocation, null);
		mFinalStep = mInitialStep;
		mSteps.add(mInitialStep);
	}

	public void addStep(final ProgramState currentState, final IcfgLocation location,
			final UnmodifiableTransFormula transFormula) {
		mFinalStep = new ExecutionStep(currentState, mFinalStep, location, transFormula);
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
		final StringBuilder out = new StringBuilder();
		ExecutionStep currentStep = mInitialStep;

		while (currentStep != null) {
			final ExecutionStep previous = currentStep.getPrevious();
			if (previous != null) {
				out.append(previous.getLocation().getLabel()).append(" ");
			}
			out.append("-> ").append(currentStep.getLocation().getLabel()).append(", ");
			final UnmodifiableTransFormula transFormula = currentStep.getTransFormula();
			if (transFormula != null) {
				out.append(transFormula.toStringDirect());
			}
			out.append("\n    ").append(currentStep.toString().replace("\n", "\n    "));
			out.append("\n");
			currentStep = currentStep.getNext();
		}

		return out.toString().stripTrailing();
	}

	public ArrayList<Entry<IcfgLocation, ProgramState>> getBasicExecution() {
		return Util.map(mSteps, (step) -> {
			return Map.entry(step.mLocation, step.mState);
		}, new ArrayList<Entry<IcfgLocation, ProgramState>>());
	}

	protected class ExecutionStep {
		private final ProgramState mState;
		private final IcfgLocation mLocation;
		private final UnmodifiableTransFormula mTransFormula;
		private ExecutionStep mNextStep = null;
		private ExecutionStep mPreviousStep = null;

		protected ExecutionStep(final ProgramState state, final ExecutionStep previousStep, final IcfgLocation location,
				final UnmodifiableTransFormula transFormula) {
			mPreviousStep = previousStep;
			mLocation = location;
			if (mPreviousStep != null) {
				mPreviousStep.mNextStep = this;
			}
			mState = state;
			mTransFormula = transFormula;
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

		public UnmodifiableTransFormula getTransFormula() {
			return mTransFormula;
		}

		@Override
		public String toString() {
			return mState.toString();
		}
	}
}
