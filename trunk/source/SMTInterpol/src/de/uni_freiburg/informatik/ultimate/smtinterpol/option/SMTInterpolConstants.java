/*
 * Copyright (C) 2020 University of Freiburg
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

/**
 * Define the SMTInterpol specific constants / options.
 *
 * @author Jochen Hoenicke
 */
public interface SMTInterpolConstants {

	/** Diff function symbol name for arrays. */
	public String DIFF = "@diff";

	// BitVector extensions
	public String NAT2BV = "nat2bv";
	public String BV2NAT = "bv2nat";
	public String INTAND = "intand";
	public String INTSHL = "intshl";

	public String PRINT_TERMS_CSE = ":print-terms-cse";
	public String CONTINUE_ON_ERROR = ":continue-on-error";
	public String TIMEOUT = ":timeout";
	public String PRODUCE_INTERPOLANTS = ":produce-interpolants";
	public String MODELS_PARTIAL = ":models-partial";
	public String PROOF_TRANSFORMATION = ":proof-transformation";
	public String MODEL_CHECK_MODE = ":model-check-mode";
	public String PROOF_CHECK_MODE = ":proof-check-mode";
	public String PROOF_LEVEL = ":proof-level";
	public String INTERPOLANT_CHECK_MODE = ":interpolant-check-mode";
	public String UNSAT_CORE_CHECK_MODE = ":unsat-core-check-mode";
	public String UNSAT_ASSUMPTIONS_CHECK_MODE = ":unsat-assumptions-check-mode";
	public String SIMPLIFY_INTERPOLANTS = ":simplify-interpolants";
	public String CHECK_TYPE = ":check-type";
	public String SIMPLIFY_CHECK_TYPE = ":simplify-check-type";
	public String EPR = ":epr";
	public String INSTANTIATION_METHOD = ":instantiation-method";
	public String UNKNOWN_TERM_DAWGS = ":unknown-term-dawgs";
	public String PROPAGATE_UNKNOWN_TERMS = ":propagate-unknown-terms";
	public String PROPAGATE_UNKNOWN_AUX = ":propagate-unknown-aux";
	public String SIMPLIFY_REPEATEDLY = ":simplify-repeatedly";
}
