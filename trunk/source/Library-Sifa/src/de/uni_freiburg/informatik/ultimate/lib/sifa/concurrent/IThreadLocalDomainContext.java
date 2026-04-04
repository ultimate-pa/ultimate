package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

public interface IThreadLocalDomainContext {

	void setCurrentThreadId(String threadId);

	default void clearCurrentThreadId() {
		setCurrentThreadId(null);
	}
}
