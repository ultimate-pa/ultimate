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

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.Transformations.AvailableTransformations;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol.CheckType;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol.ProofMode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory.InstantiationMethod;

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
	private final BooleanOption mProofCheckMode;
	private final EnumOption<CheckType> mSimpCheckType;
	private final EnumOption<ProofMode> mProofLevel;
	private final EnumOption<InstantiationMethod> mInstantiationMethod;
	private final OptionMap mOptions;

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
		mProofTrans = new EnumOption<>(
				AvailableTransformations.NONE, true,
				AvailableTransformations.class,
				"Algorithm used to transform the resolution proof tree.");
		mModelsPartial = new BooleanOption(false, true, "Don't totalize models.");
		mCheckType = new EnumOption<>(CheckType.FULL, true,
				CheckType.class, "Strength of check used in check-sat command.");
		mSimpIps = new BooleanOption(false, true,
				"Apply strong context simplification to generated interpolants.");
		mProofCheckMode = new BooleanOption(false,
				false, "Check the produced proof for unsatisfiable formulas.");
		mSimpCheckType = new EnumOption<>(CheckType.QUICK, true,
				CheckType.class, "Strength of checks used by the strong context"
				+ " simplifier used in the simplify command");
		mInstantiationMethod = new EnumOption<>(InstantiationMethod.E_MATCHING_CONFLICT, false,
				InstantiationMethod.class, "Quantifier Theory: Method to instantiate quantified formulas.");
		mProofLevel = new EnumOption<>(ProofMode.NONE, false, ProofMode.class, "Proof level.");

		// general standard compliant options
		options.addOption(SMTLIBConstants.VERBOSITY, new VerbosityOption(logger));
		options.addOption(SMTInterpolConstants.TIMEOUT, mTimeout);
		options.addOption(SMTLIBConstants.RANDOM_SEED, mRandomSeed);
		options.addOption(SMTLIBConstants.PRODUCE_ASSERTIONS, new BooleanOption(false, false,
				"Store asserted formulas for later retrieval."));
		options.addAlias(SMTLIBConstants.INTERACTIVE_MODE, SMTLIBConstants.PRODUCE_ASSERTIONS);
		// model options
		options.addOption(SMTLIBConstants.PRODUCE_MODELS, new BooleanOption(false, true,
				"Produce models for satisfiable formulas"));
		options.addOption(SMTInterpolConstants.MODELS_PARTIAL, mModelsPartial);
		options.addOption(SMTInterpolConstants.MODEL_CHECK_MODE, mModelCheckMode);
		options.addOption(SMTLIBConstants.PRODUCE_ASSIGNMENTS, new BooleanOption(false,
				false, "Produce assignments of named Boolean terms for "
				+ "satisfiable formulas"));

		// proof options
		options.addOption(SMTLIBConstants.PRODUCE_PROOFS, mProduceProofs);
		options.addOption(SMTInterpolConstants.PROOF_TRANSFORMATION, mProofTrans);
		options.addOption(SMTInterpolConstants.PROOF_CHECK_MODE, mProofCheckMode);
		options.addOption(SMTInterpolConstants.PROOF_LEVEL, mProofLevel);

		// interpolant options
		options.addOption(SMTInterpolConstants.PRODUCE_INTERPOLANTS, mProduceInterpolants);
		options.addOption(SMTInterpolConstants.INTERPOLANT_CHECK_MODE, mInterpolantCheckMode);
		options.addOption(SMTInterpolConstants.SIMPLIFY_INTERPOLANTS, mSimpIps);

		// unsat core options
		options.addOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, new BooleanOption(
				false, false, "Enable production of unsatisfiable cores."));
		options.addOption(SMTInterpolConstants.UNSAT_CORE_CHECK_MODE, new BooleanOption(
				false, false, "Check generated unsat cores"));

		// unsat assumptions options
		options.addOption(SMTLIBConstants.PRODUCE_UNSAT_ASSUMPTIONS, new BooleanOption(
				false, false, "Enable production of unsatisfiable assumptions."));
		options.addOption(SMTInterpolConstants.UNSAT_ASSUMPTIONS_CHECK_MODE, new BooleanOption(
				false, false, "Check generated unsat assumptions"));

		// general non-standard options
		options.addOption(SMTInterpolConstants.CHECK_TYPE, mCheckType);
		options.addOption(SMTInterpolConstants.EPR, new BooleanOption(false, false,
				"Assume formula is in EPR fragment. This give an error if the formula is outside EPR."));
		options.addOption(SMTInterpolConstants.INSTANTIATION_METHOD, mInstantiationMethod);
		options.addOption(SMTInterpolConstants.UNKNOWN_TERM_DAWGS, new BooleanOption(true, false,
				"Quantifier Theory: Use fourth instance value UNKNOWN_TERM as default in literal dawgs."));
		options.addOption(SMTInterpolConstants.PROPAGATE_UNKNOWN_TERMS, new BooleanOption(false, false,
				"Quantifier Theory: Allow propagation on atoms with non-existing term."));
		options.addOption(SMTInterpolConstants.PROPAGATE_UNKNOWN_AUX, new BooleanOption(false, false,
				"Quantifier Theory: Allow propagation on atoms with non-existing @AUX applications."));

		// simplifier options
		options.addOption(SMTInterpolConstants.SIMPLIFY_CHECK_TYPE, mSimpCheckType);
		options.addOption(SMTInterpolConstants.SIMPLIFY_REPEATEDLY, new BooleanOption(true, true,
				"Simplify until the fixpoint is reached."));

		options.addOption(SMTLIBConstants.GLOBAL_DECLARATIONS, new BooleanOption(false, false,
				"Make all declared and defined symbols global.  Global symbols survive pop operations."));
		mOptions = options;
	}

	@SuppressWarnings("unchecked")
	SolverOptions(final OptionMap options) {
		mTimeout = (LongOption) options.getOption(SMTInterpolConstants.TIMEOUT);
		mProduceProofs = (BooleanOption) options.getOption(SMTLIBConstants.PRODUCE_PROOFS);
		mRandomSeed = (LongOption) options.getOption(SMTLIBConstants.RANDOM_SEED);
		mInterpolantCheckMode = (BooleanOption) options.getOption(SMTInterpolConstants.INTERPOLANT_CHECK_MODE);
		mProduceInterpolants = (BooleanOption) options.getOption(SMTInterpolConstants.PRODUCE_INTERPOLANTS);
		mModelCheckMode = (BooleanOption) options.getOption(SMTInterpolConstants.MODEL_CHECK_MODE);
		mProofTrans = (EnumOption<AvailableTransformations>) options.getOption(SMTInterpolConstants.PROOF_TRANSFORMATION);
		mModelsPartial = (BooleanOption) options.getOption(SMTInterpolConstants.MODELS_PARTIAL);
		mCheckType = (EnumOption<CheckType>) options.getOption(SMTInterpolConstants.CHECK_TYPE);
		mSimpIps = (BooleanOption) options.getOption(SMTInterpolConstants.SIMPLIFY_INTERPOLANTS);
		mProofCheckMode = (BooleanOption) options.getOption(SMTInterpolConstants.PROOF_CHECK_MODE);
		mSimpCheckType = (EnumOption<CheckType>) options.getOption(SMTInterpolConstants.SIMPLIFY_CHECK_TYPE);
		mProofLevel = (EnumOption<ProofMode>) options.getOption(SMTInterpolConstants.PROOF_LEVEL);
		mInstantiationMethod =
				(EnumOption<InstantiationMethod>) options.getOption(SMTInterpolConstants.INSTANTIATION_METHOD);
		mOptions = options;
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

	public final ProofMode getProofMode() {
		ProofMode level = mProofLevel.getValue();
		if (level == ProofMode.NONE) {
			if (isProduceProofs() || isProofCheckModeActive()) {
				level = ProofMode.LOWLEVEL;
			} else if (isProduceInterpolants() || (Boolean) mOptions.get(SMTLIBConstants.PRODUCE_UNSAT_CORES)) {
				level = ProofMode.CLAUSES;
			}
		}
		return level;
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

	public InstantiationMethod getInstantiationMethod() {
		return mInstantiationMethod.getValue();
	}

}
