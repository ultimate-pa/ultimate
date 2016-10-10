package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation;

import java.util.Optional;
import java.util.function.BooleanSupplier;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.SearchStep;

@FunctionalInterface
public interface CancelableStepTest<T extends SearchStep<?, T>> {
	Optional<Boolean> test(T step, BooleanSupplier isCanceled);
}
