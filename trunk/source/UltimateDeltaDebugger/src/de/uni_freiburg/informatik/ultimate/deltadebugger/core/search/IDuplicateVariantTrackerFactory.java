package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IDuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizer;

/**
 * Factory for {@link IDuplicateVariantTracker}s.
 */
@FunctionalInterface
public interface IDuplicateVariantTrackerFactory {
	/**
	 * @param minimizer
	 *            Minimizer.
	 * @param allChanges
	 *            list of changes
	 * @return a duplicate variant tracker
	 */
	IDuplicateVariantTracker<IChangeHandle> create(IMinimizer minimizer, List<IChangeHandle> allChanges);
}
