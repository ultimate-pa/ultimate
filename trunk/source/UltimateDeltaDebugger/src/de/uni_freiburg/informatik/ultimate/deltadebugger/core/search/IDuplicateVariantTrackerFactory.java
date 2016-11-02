package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IDuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizer;

@FunctionalInterface
public interface IDuplicateVariantTrackerFactory {
	IDuplicateVariantTracker<IChangeHandle> create(IMinimizer minimizer, List<IChangeHandle> allChanges);
}
