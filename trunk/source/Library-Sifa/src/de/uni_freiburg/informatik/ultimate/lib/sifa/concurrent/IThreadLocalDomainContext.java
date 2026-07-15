package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public interface IThreadLocalDomainContext {

	void setCurrentThreadId(String threadId);

	static void setIfApplicable(final IDomain domain, final String threadId) {
		if (domain instanceof final IThreadLocalDomainContext ctx) {
			ctx.setCurrentThreadId(threadId);
		}
	}
}
