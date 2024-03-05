package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ProgramState.ControllerState;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ProgramState.ThreadState;

public class GlobalVarUpdate<S, T> implements IRule<ProgramState<S, T>> {
	private final Map<S, S> mGlobalUpdate;
	private final T mPredecessor;
	private final T mSuccessor;

	public GlobalVarUpdate(final Map<S, S> globalUpdate, final T predecessor, final T successor) {
		mGlobalUpdate = globalUpdate;
		mPredecessor = predecessor;
		mSuccessor = successor;
	}

	@Override
	public boolean isApplicable(final Configuration<ProgramState<S, T>> config) {
		for (int i = 0; i < config.size(); ++i) {
			final var state = config.get(i);
			if (state.isThreadState()) {
				final var thread = state.getThreadState();
				if (thread.equals(mPredecessor)) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public List<Configuration<ProgramState<S, T>>> successors(final Configuration<ProgramState<S, T>> config) {
		final var result = new ArrayList<Configuration<ProgramState<S, T>>>();

		assert config.get(0).isControllerState();

		for (int i = 1; i < config.size(); ++i) {
			final var state = config.get(i);
			assert state.isThreadState();
			final var thread = state.getThreadState();
			if (thread.equals(mPredecessor)) {
				result.add(apply(config, i));
			}
		}

		return result;
	}

	private Configuration<ProgramState<S, T>> apply(final Configuration<ProgramState<S, T>> config, final int i) {
		final var controllerPred = config.get(0);
		assert controllerPred.isControllerState();
		final var controllerSucc = mGlobalUpdate.get(controllerPred.getControllerState());
		final var subst = Map.<Integer, ProgramState<S, T>> of(0, new ControllerState<S, T>(controllerSucc), i,
				new ThreadState<>(mSuccessor));
		return config.replace(subst);
	}

	@Override
	public int extensionSize() {
		return 0;
	}
}
