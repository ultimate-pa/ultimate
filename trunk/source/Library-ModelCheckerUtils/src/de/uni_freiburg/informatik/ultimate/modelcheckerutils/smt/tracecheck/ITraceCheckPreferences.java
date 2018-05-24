/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;

/**
 * {@link ITraceCheckPreferences} describes types that provide all options that are of interest to the various
 * {@link ITraceCheck} implementations.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface ITraceCheckPreferences {

	/**
	 * Unsatisfiable core mode.
	 */
	public enum UnsatCores {
		IGNORE, STATEMENT_LEVEL, CONJUNCT_LEVEL
	}

	/**
	 * Code block assertion order. Determines in which order the different codeblocks of a trace are asserted during a
	 * trace check.
	 */
	public enum AssertCodeBlockOrder {
		/**
		 * Assert all codeblocks at once.
		 */
		NOT_INCREMENTALLY,

		/**
		 * Assert in two steps. First, assert all codeblocks that do not occur in the first loop of the trace. Second,
		 * assert the rest.
		 */
		OUTSIDE_LOOP_FIRST1,

		/**
		 * Assert codeblocks according to their "depth". Codeblocks outside of loops have depth 0, codeblocks within a
		 * loop have depth i + 1 where i is the depth of the loop codeblock.
		 *
		 * Assert all codeblocks in the order of their depth starting with depth 0.
		 */
		OUTSIDE_LOOP_FIRST2,

		/**
		 * Similar to {@link AssertCodeBlockOrder#OUTSIDE_LOOP_FIRST2}, but in reverse order (start with the deepest
		 * codeblocks).
		 */
		INSIDE_LOOP_FIRST1,

		/**
		 * Similar to {@link AssertCodeBlockOrder#OUTSIDE_LOOP_FIRST2} and
		 * {@link AssertCodeBlockOrder#INSIDE_LOOP_FIRST1} in that it also uses the depth of a codeblock. This setting
		 * alternates between depths, starting with depth 0, then asserting the maximal depth, then depth 1, etc.
		 */
		MIX_INSIDE_OUTSIDE,

		/**
		 * Assert in two steps: First terms with small constants (currently, terms that contain constants smaller than
		 * 10), then the rest.
		 */
		TERMS_WITH_SMALL_CONSTANTS_FIRST
	}

	boolean getUseSeparateSolverForTracechecks();

	AssertCodeBlockOrder getAssertCodeBlocksOrder();

	IToolchainStorage getToolchainStorage();

	IUltimateServiceProvider getUltimateServices();

	String getPathOfDumpedScript();

	boolean getDumpSmtScriptToFile();

	boolean getUseWeakestPreconditionForPathInvariants();

	boolean getUseAbstractInterpretation();

	boolean getUseVarsFromUnsatCore();

	boolean getUseNonlinearConstraints();

	IIcfg<?> getIcfgContainer();

	boolean getUseLiveVariables();

	UnsatCores getUnsatCores();

	SimplificationTechnique getSimplificationTechnique();

	XnfConversionTechnique getXnfConversionTechnique();

	CfgSmtToolkit getCfgSmtToolkit();

	boolean collectInterpolantStatistics();

	boolean computeCounterexample();

}