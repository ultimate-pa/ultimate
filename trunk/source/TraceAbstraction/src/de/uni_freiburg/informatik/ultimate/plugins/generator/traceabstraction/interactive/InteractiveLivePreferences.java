package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.ExecutionException;

import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;

public class InteractiveLivePreferences {
	private final IInteractive<Object> mInteractive;

	public InteractiveLivePreferences(IInteractive<Object> mInteractive) {
		this.mInteractive = mInteractive;
		registerHandlers();
	}

	public void registerHandlers() {

	}
	
	public interface IPref<T> {
		default Map<IPref<T>,T> newMap() {
			return new HashMap<>();
		};
	}
	
	public enum IntPref implements IPref<Integer> {
		NextCEXSIteration,
		NextIPSIteration,
		NextSSIteration,
	}

	private boolean mPaused = false;
	private final Map<IntPref,Integer> mIntSettings = new HashMap<>();


	public boolean isPaused() {
		return mPaused;
	}

	public void waitIfPaused() throws InterruptedException, ExecutionException {
		if (mPaused) {
			mInteractive.request(Resume.class).get();
			mPaused = false;
			mInteractive.send(RESUMED);
		}
	}

	public static final Resume RESUMED = new Resume();

	public static class Resume {
	}
}
