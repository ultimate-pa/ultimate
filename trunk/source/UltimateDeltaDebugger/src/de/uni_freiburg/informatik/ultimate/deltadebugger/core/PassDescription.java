package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.Minimizer;

/**
 * A pass is one concrete reduction operation that transforms the input source code string into a reduced source code
 * string. It is created from a variant generator factory, which implements the actual transformation logic, and
 * optional a search algorithm and other options that affect how a reduced source code variant is selected. Meta
 * information like a name is added to be able to generate meaningful output for the user.
 */
public final class PassDescription {
	/**
	 * Builder pattern class.
	 */
	public static class Builder {
		private String name = "<unnamed pass>";
		private String description = "<no description>";
		private VariantGeneratorFactory variantGeneratorFactory;
		private Minimizer minimizer;
		private boolean disableSpeculativeTesting = false;
		private boolean repeatUntilReductionFails = false;

		private Builder(final PassDescription other) {
			name = other.name;
			description = other.description;
			variantGeneratorFactory = other.variantGeneratorFactory;
			minimizer = other.minimizer;
			disableSpeculativeTesting = other.disableSpeculativeTesting;
			repeatUntilReductionFails = other.repeatUntilReductionFails;
		}

		private Builder(final VariantGeneratorFactory variantGeneratorFactory) {
			this.variantGeneratorFactory = variantGeneratorFactory;
		}

		/**
		 * @return new pass description
		 */
		public PassDescription build() {
			return new PassDescription(this);
		}

		/**
		 * @param description
		 *            description of the pass
		 * @return this builder
		 */
		public Builder description(final String description) {
			this.description = description;
			return this;
		}

		/**
		 * @param disableSpeculativeTesting
		 *            flag to disable speculative testing
		 * @return this builder
		 */
		public Builder disableSpeculativeTesting(final boolean disableSpeculativeTesting) {
			this.disableSpeculativeTesting = disableSpeculativeTesting;
			return this;
		}

		/**
		 * @param minimizer
		 *            minimizer of the pass
		 * @return this builder
		 */
		public Builder minimizer(final Minimizer minimizer) {
			this.minimizer = minimizer;
			return this;
		}

		/**
		 * @param name
		 *            name of the pass
		 * @return this builder
		 */
		public Builder name(final String name) {
			this.name = name;
			return this;
		}

		/**
		 * @param repeatUntilReductionFails
		 *            flag to repeat the same pass until no reduction occurs
		 * @return this builder
		 */
		public Builder repeatUntilReductionFails(final boolean repeatUntilReductionFails) {
			this.repeatUntilReductionFails = repeatUntilReductionFails;
			return this;
		}

		/**
		 * @param variantGeneratorFactory
		 *            a function to create a new variant generator instance
		 * @return this builder
		 */
		public Builder variantGeneratorFactory(final VariantGeneratorFactory variantGeneratorFactory) {
			this.variantGeneratorFactory = variantGeneratorFactory;
			return this;
		}
	}

	/**
	 * @param variantGeneratorFactory
	 *            required variant generator factory function
	 * @return new Builder instance to set optional attributes
	 */
	public static Builder builder(final VariantGeneratorFactory variantGeneratorFactory) {
		return new Builder(variantGeneratorFactory);
	}

	private final String name;
	private final String description;
	private final VariantGeneratorFactory variantGeneratorFactory;
	private final Minimizer minimizer;

	private final boolean disableSpeculativeTesting;

	private final boolean repeatUntilReductionFails;

	private PassDescription(final Builder builder) {
		name = builder.name;
		description = builder.description;
		minimizer = builder.minimizer;
		disableSpeculativeTesting = builder.disableSpeculativeTesting;
		repeatUntilReductionFails = builder.repeatUntilReductionFails;
		variantGeneratorFactory = builder.variantGeneratorFactory;
	}

	/**
	 * @param name
	 *            name of the new pass
	 * @param other
	 *            other pass instance to copy attributes from
	 * @return new Builder instance to set optional attributes
	 */
	public Builder copy() {
		return new Builder(this);
	}

	/**
	 * Speculative (parallel) testing, which is based on the expectation that a test is more likely to fail than
	 * succeed, may not be useful for certain passes/minimizer combinations.
	 *
	 * @return true to disable speculative testing
	 */
	public boolean disableSpeculativeTesting() {
		return disableSpeculativeTesting;
	}

	/**
	 * More detailed information about what this pass does.
	 *
	 * @return description
	 */
	public String getDescription() {
		return description;
	}

	/**
	 * Optional a pass can specify a preferred minimizer to use
	 *
	 * @return the preferred minimizer to use
	 */
	public Optional<Minimizer> getMinimizer() {
		return Optional.ofNullable(minimizer);
	}

	/**
	 * The name to use to refer to this pass in the generated logger/console output.
	 *
	 * @return name of the pass
	 */
	public String getName() {
		return name;
	}

	/**
	 * The actual reduction algorithm is accessed using a variant generator.
	 *
	 * @return the factory function to create the underlying variant generator
	 */
	public VariantGeneratorFactory getVariantGeneratorFactory() {
		return variantGeneratorFactory;
	}

	/**
	 * @return whether a pass should be repeated until no more reduction succeeds
	 */
	public boolean repeatUntilReductionFails() {
		return repeatUntilReductionFails;
	}

}