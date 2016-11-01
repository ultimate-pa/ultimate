package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.DuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.Minimizer;

@FunctionalInterface
public interface DuplicateVariantTrackerFactory {
	DuplicateVariantTracker<IChangeHandle> create(Minimizer minimizer, List<IChangeHandle> allChanges);
}