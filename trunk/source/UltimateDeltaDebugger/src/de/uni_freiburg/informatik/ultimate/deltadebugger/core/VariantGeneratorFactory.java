package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.Optional;

@FunctionalInterface
public interface VariantGeneratorFactory {
	Optional<VariantGenerator> analyze(PassContext context);
}