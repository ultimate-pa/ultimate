/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizer;

/**
 * A pass is one concrete reduction operation that transforms the input source code string into a reduced source code
 * string. It is created from a variant generator factory, which implements the actual transformation logic, and
 * optional a search algorithm and other options that affect how a reduced source code variant is selected. Meta
 * information like a name is added to be able to generate meaningful output for the user.
 */
public final class PassDescription {
	private final String mName;
	private final String mDescription;
	private final IVariantGeneratorFactory mVariantGeneratorFactory;
	private final IMinimizer mMinimizer;
	
	private final boolean mDisableSpeculativeTesting;
	private final boolean mRepeatUntilReductionFails;
	
	/**
	 * @param builder
	 *            Builder.
	 */
	private PassDescription(final Builder builder) {
		mName = builder.mNameInner;
		mDescription = builder.mDescriptionInner;
		mVariantGeneratorFactory = builder.mVariantGeneratorFactoryInner;
		mMinimizer = builder.mMinimizerInner;
		mDisableSpeculativeTesting = builder.mDisableSpeculativeTestingInner;
		mRepeatUntilReductionFails = builder.mRepeatUntilReductionFailsInner;
	}
	
	/**
	 * @param variantGeneratorFactory
	 *            Required variant generator factory function.
	 * @return new Builder instance to set optional attributes
	 */
	public static Builder builder(final IVariantGeneratorFactory variantGeneratorFactory) {
		return new Builder(variantGeneratorFactory);
	}
	
	/**
	 * @return New Builder instance to set optional attributes.
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
		return mDisableSpeculativeTesting;
	}
	
	/**
	 * More detailed information about what this pass does.
	 *
	 * @return description
	 */
	public String getDescription() {
		return mDescription;
	}
	
	/**
	 * A pass can specify a preferred minimizer to use.
	 *
	 * @return the preferred minimizer to use
	 */
	public Optional<IMinimizer> getMinimizer() {
		return Optional.ofNullable(mMinimizer);
	}
	
	/**
	 * The name to use to refer to this pass in the generated logger/console output.
	 *
	 * @return name of the pass
	 */
	public String getName() {
		return mName;
	}
	
	/**
	 * The actual reduction algorithm is accessed using a variant generator.
	 *
	 * @return the factory function to create the underlying variant generator
	 */
	public IVariantGeneratorFactory getVariantGeneratorFactory() {
		return mVariantGeneratorFactory;
	}
	
	/**
	 * @return Whether a pass should be repeated until no more reduction succeeds.
	 */
	public boolean repeatUntilReductionFails() {
		return mRepeatUntilReductionFails;
	}
	
	/**
	 * Builder pattern class.
	 */
	public static final class Builder {
		private String mNameInner = "<unnamed pass>";
		private String mDescriptionInner = "<no description>";
		private IVariantGeneratorFactory mVariantGeneratorFactoryInner;
		private IMinimizer mMinimizerInner;
		private boolean mDisableSpeculativeTestingInner;
		private boolean mRepeatUntilReductionFailsInner;
		
		/**
		 * @param other
		 *            Pass description.
		 */
		public Builder(final PassDescription other) {
			mNameInner = other.mName;
			mDescriptionInner = other.mDescription;
			mVariantGeneratorFactoryInner = other.mVariantGeneratorFactory;
			mMinimizerInner = other.mMinimizer;
			mDisableSpeculativeTestingInner = other.mDisableSpeculativeTesting;
			mRepeatUntilReductionFailsInner = other.mRepeatUntilReductionFails;
		}
		
		/**
		 * @param variantGeneratorFactory
		 *            Variant generator factory.
		 */
		public Builder(final IVariantGeneratorFactory variantGeneratorFactory) {
			mVariantGeneratorFactoryInner = variantGeneratorFactory;
		}
		
		/**
		 * @return New pass description.
		 */
		public PassDescription build() {
			return new PassDescription(this);
		}
		
		/**
		 * @param description
		 *            Description of the pass.
		 * @return this builder
		 */
		public Builder description(final String description) {
			mDescriptionInner = description;
			return this;
		}
		
		/**
		 * @param disableSpeculativeTesting
		 *            Flag to disable speculative testing.
		 * @return this builder
		 */
		public Builder disableSpeculativeTesting(final boolean disableSpeculativeTesting) {
			mDisableSpeculativeTestingInner = disableSpeculativeTesting;
			return this;
		}
		
		/**
		 * @param minimizer
		 *            Minimizer of the pass.
		 * @return this builder
		 */
		public Builder minimizer(final IMinimizer minimizer) {
			mMinimizerInner = minimizer;
			return this;
		}
		
		/**
		 * @param name
		 *            Name of the pass.
		 * @return this builder
		 */
		public Builder name(final String name) {
			mNameInner = name;
			return this;
		}
		
		/**
		 * @param repeatUntilReductionFails
		 *            Flag to repeat the same pass until no reduction occurs.
		 * @return this builder
		 */
		public Builder repeatUntilReductionFails(final boolean repeatUntilReductionFails) {
			mRepeatUntilReductionFailsInner = repeatUntilReductionFails;
			return this;
		}
		
		/**
		 * @param variantGeneratorFactory
		 *            A function to create a new variant generator instance.
		 * @return this builder
		 */
		public Builder variantGeneratorFactory(final IVariantGeneratorFactory variantGeneratorFactory) {
			mVariantGeneratorFactoryInner = variantGeneratorFactory;
			return this;
		}
	}
}
