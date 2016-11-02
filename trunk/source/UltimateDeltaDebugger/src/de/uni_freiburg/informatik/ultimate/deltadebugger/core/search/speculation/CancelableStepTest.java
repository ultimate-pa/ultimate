package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation;

import java.util.Optional;
import java.util.function.BooleanSupplier;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.ISearchStep;

@FunctionalInterface
public interface CancelableStepTest<T extends ISearchStep<?, T>> {
	Optional<Boolean> test(T step, BooleanSupplier isCanceled);
}
