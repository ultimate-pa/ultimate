package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.ChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.DuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.Minimizer;

@FunctionalInterface
public interface DuplicateVariantTrackerFactory {
	DuplicateVariantTracker<ChangeHandle> create(Minimizer minimizer, List<ChangeHandle> allChanges);
}