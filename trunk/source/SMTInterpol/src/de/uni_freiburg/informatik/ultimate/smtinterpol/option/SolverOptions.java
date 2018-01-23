/*
 * Copyright (C) 2014 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.option;

import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.Transformations.AvailableTransformations;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol.CheckType;

/**
 * Options specific to the solver but independent of the front end.  To speed up
 * several tasks we provide caches for some of the options.
 * @author Juergen Christ
 */
public class SolverOptions {

	private final LongOption mTimeout;
	private final BooleanOption mProduceProofs;
	private final LongOption mRandomSeed;
	private final BooleanOption mInterpolantCheckMode;
	private final BooleanOption mProduceInterpolants;
	private final BooleanOption mModelCheckMode;
	private final EnumOption<AvailableTransformations> mProofTrans;
	private final BooleanOption mModelsPartial;
	private final EnumOption<CheckType> mCheckType;
	private final BooleanOption mSimpIps;
	private final BooleanOption mArrayInterpolation;
	private final BooleanOption mProofCheckMode;
	private final EnumOption<CheckType> mSimpCheckType;

	public static final String TIMEOUT = ":timeout";
	public static final String RANDOM_SEED = ":random-seed";
	public static final String MODELS_PARTIAL = ":models-partial";
	public static final String MODEL_CHECK_MODE = ":model-check-mode";
	public static final String PRODUCE_PROOFS = ":produce-proofs";
	public static final String PROOF_TRANSFORMATION = ":proof-transformation";
	public static final String PROOF_CHECK_MODE = ":proof-check-mode";
	public static final String PRODUCE_INTERPOLANTS = ":produce-interpolants";
	public static final String INTERPOLANT_CHECK_MODE = ":interpolant-check-mode";
	public static final String SIMPLIFY_INTERPOLANTS = ":simplify-interpolants";
	public static final String ARRAY_INTERPOLATION = ":array-interpolation";
	public static final String CHECK_TYPE = ":check-type";
	public static final String SIMPLIFY_CHECK_TYPE = ":simplify-check-type";

	SolverOptions(final OptionMap options, final LogProxy logger) {
		mTimeout = new LongOption(0, true, "Soft timeout in milliseconds for "
				+ "individual check-sat calls.  Values <= 0 deactivate the "
				+ "timeout.");
		mProduceProofs = new BooleanOption(false, false,
				"Produce proofs for unsatisfiable formulas.");
		mRandomSeed = new LongOption(Config.RANDOM_SEED,
				true, "Seed for the internal pseudo-random number generator.");
		mInterpolantCheckMode = new BooleanOption(
				false, false, "Check generated interpolants.");
		mProduceInterpolants = new BooleanOption(
				false, false, "Enable interpolant production.");
		mModelCheckMode = new BooleanOption(false, true,
				"Check satisfiable formulas against the produced model.");
		mProofTrans = new EnumOption<AvailableTransformations>(
				AvailableTransformations.NONE, true,
				AvailableTransformations.class,
				"Algorithm used to transform the resolution proof tree.");
		mModelsPartial = new BooleanOption(false, true, "Don't totalize models.");
		mCheckType = new EnumOption<CheckType>(CheckType.FULL, true,
				CheckType.class, "Strength of check used in check-sat command.");
		mSimpIps = new BooleanOption(false, true,
				"Apply strong context simplification to generated interpolants.");
		mArrayInterpolation = new BooleanOption(true, true, "Support interpolation for array theory lemmas.");
		mProofCheckMode = new BooleanOption(false,
				false, "Check the produced proof for unsatisfiable formulas.");
		mSimpCheckType = new EnumOption<CheckType>(CheckType.QUICK, true,
				CheckType.class, "Strength of checks used by the strong context"
				+ " simplifier used in the simplify command");

		// general standard compliant options
		options.addOption(":verbosity", new VerbosityOption(logger));
		options.addOption(TIMEOUT, mTimeout);
		options.addOption(RANDOM_SEED, mRandomSeed);
		options.addOption(":produce-assertions", new BooleanOption(false, false,
				"Store asserted formulas for later retrieval."));
		options.addAlias(":interactive-mode", ":produce-assertions");
		// model options
		options.addOption(":produce-models", new BooleanOption(false, true,
				"Produce models for satisfiable formulas"));
		options.addOption(MODELS_PARTIAL, mModelsPartial);
		options.addOption(MODEL_CHECK_MODE, mModelCheckMode);
		options.addOption(":produce-assignments", new BooleanOption(false,
				false, "Produce assignments of named Boolean terms for "
				+ "satisfiable formulas"));

		// proof options
		options.addOption(PRODUCE_PROOFS, mProduceProofs);
		options.addOption(PROOF_TRANSFORMATION, mProofTrans);
		options.addOption(PROOF_CHECK_MODE, mProofCheckMode);

		// interpolant options
		options.addOption(PRODUCE_INTERPOLANTS, mProduceInterpolants);
		options.addOption(INTERPOLANT_CHECK_MODE, mInterpolantCheckMode);
		options.addOption(SIMPLIFY_INTERPOLANTS, mSimpIps);
		options.addOption(ARRAY_INTERPOLATION, mArrayInterpolation);

		// unsat core options
		options.addOption(":produce-unsat-cores", new BooleanOption(
				false, false, "Enable production of unsatisfiable cores."));
		options.addOption(":unsat-core-check-mode", new BooleanOption(
				false, false, "Check generated unsat cores"));

		// unsat assumptions options
		options.addOption(":produce-unsat-assumptions", new BooleanOption(
				false, false, "Enable production of unsatisfiable assumptions."));
		options.addOption(":unsat-assumptions-check-mode", new BooleanOption(
				false, false, "Check generated unsat assumptions"));

		// general non-standard options
		options.addOption(CHECK_TYPE, mCheckType);

		// simplifier options
		options.addOption(SIMPLIFY_CHECK_TYPE, mSimpCheckType);
		options.addOption(":simplify-repeatedly", new BooleanOption(true, true,
				"Simplify until the fixpoint is reached."));

		options.addOption(":global-declarations", new BooleanOption(false, false,
				"Make all declared and defined symbols global.  Global symbols survive pop operations."));
	}

	@SuppressWarnings("unchecked")
	SolverOptions(final OptionMap options) {
		mTimeout = (LongOption) options.getOption(TIMEOUT);
		mProduceProofs = (BooleanOption) options.getOption(PRODUCE_PROOFS);
		mRandomSeed = (LongOption) options.getOption(RANDOM_SEED);
		mInterpolantCheckMode = (BooleanOption) options.getOption(INTERPOLANT_CHECK_MODE);
		mProduceInterpolants = (BooleanOption) options.getOption(PRODUCE_INTERPOLANTS);
		mModelCheckMode = (BooleanOption) options.getOption(MODEL_CHECK_MODE);
		mProofTrans = (EnumOption<AvailableTransformations>) options.getOption(PROOF_TRANSFORMATION);
		mModelsPartial = (BooleanOption) options.getOption(MODELS_PARTIAL);
		mCheckType = (EnumOption<CheckType>) options.getOption(CHECK_TYPE);
		mSimpIps = (BooleanOption) options.getOption(SIMPLIFY_INTERPOLANTS);
		mArrayInterpolation = (BooleanOption) options.getOption(ARRAY_INTERPOLATION);
		mProofCheckMode = (BooleanOption) options.getOption(PROOF_CHECK_MODE);
		mSimpCheckType = (EnumOption<CheckType>) options.getOption(SIMPLIFY_CHECK_TYPE);
	}

	public final CheckType getCheckType() {
		return mCheckType.getValue();
	}

	public final void setCheckType(final CheckType newCheckType) {
		mCheckType.set(newCheckType);
	}

	public final boolean isInterpolantCheckModeActive() {
		return mInterpolantCheckMode.getValue();
	}

	public final boolean isModelCheckModeActive() {
		return mModelCheckMode.getValue();
	}

	public final boolean isModelsPartial() {
		return mModelsPartial.getValue();
	}

	public final boolean isProduceInterpolants() {
		return mProduceInterpolants.getValue();
	}

	public final boolean isProduceProofs() {
		return mProduceProofs.getValue();
	}

	public final boolean isProofCheckModeActive() {
		return mProofCheckMode.getValue();
	}

	public final AvailableTransformations getProofTransformation() {
		return mProofTrans.getValue();
	}

	public final long getRandomSeed() {
		return mRandomSeed.getValue();
	}

	public final boolean isSimplifyInterpolants() {
		return mSimpIps.getValue();
	}

	public final long getTimeout() {
		return mTimeout.getValue();
	}

	public CheckType getSimplifierCheckType() {
		return mSimpCheckType.getValue();
	}

}
