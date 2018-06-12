/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter.NlaHandling;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminationSettings;

/**
 * {@link ILassoRankerPreferences} describes all preferences that are required for performing a LassoRanker analysis.
 * These values are constant for the lifetime of the {@link LassoAnalysis} object.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Jan Leike
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public interface ILassoRankerPreferences {
	/**
	 * Should the polyhedra for stem and loop be made integral for integer programs? (Not yet implemented.)
	 */
	public boolean isComputeIntegralHull();

	/**
	 * Enable the LassoPartitioneer that splits lassos into multiple independent components?
	 */
	public boolean isEnablePartitioneer();

	/**
	 * Add annotations to terms for debugging purposes
	 */
	public boolean isAnnotateTerms();

	/**
	 * If true, we use an external tool to solve the constraints. If false, we use SMTInterpol to solve the constraints.
	 */
	public boolean isExternalSolver();

	/**
	 * What shell command should be used to call the external smt solver?
	 */
	public String getExternalSolverCommand();

	/**
	 * Write SMT solver script to file.
	 */
	public boolean isDumpSmtSolverScript();

	/**
	 * Path to which the SMT solver script is written.
	 */
	public String getPathOfDumpedScript();

	/**
	 * Base name (without path) of the file to which the SMT solver script is written.
	 */
	public String getBaseNameOfDumpedScript();

	/**
	 * Overapproximate the result of RewriteArrays by dropping all conjuncts that are not-equals relations of indices.
	 * If the lasso does not contain arrays, this option has no effect. Otherwise setting this to true is unsound for
	 * nontermination analysis.
	 */
	public boolean isOverapproximateArrayIndexConnection();

	/**
	 * Defines what the {@link InequalityConverter} does while processing a (Sub-) Term that is nonlinear.
	 */
	public NlaHandling getNlaHandling();

	/**
	 * Use Matthias' (true) or Franks (false) map elimination implementation
	 */
	public boolean isUseOldMapElimination();

	public boolean isMapElimAddInequalities();

	public boolean isMapElimOnlyTrivialImplicationsIndexAssignment();

	public boolean isMapElimOnlyTrivialImplicationsArrayWrite();

	public boolean isMapElimOnlyIndicesInFormula();

	/**
	 * Emulate push/pop using reset and re-asserting and re-declaring.
	 */
	public boolean isFakeNonIncrementalScript();

	/**
	 * Calls the {@link Consumer#accept(Object)} method for each setting with a string describing this settings' value.
	 *
	 * @param consumer
	 *            The consumer.
	 */
	default void feedSettingsString(final Consumer<String> consumer) {
		consumer.accept("Compute integeral hull: " + isComputeIntegralHull());
		consumer.accept("Enable LassoPartitioneer: " + isEnablePartitioneer());
		consumer.accept("Term annotations enabled: " + isAnnotateTerms());
		consumer.accept("Use exernal solver: " + isExternalSolver());
		consumer.accept("SMT solver command: " + getExternalSolverCommand());
		consumer.accept("Dump SMT script to file: " + isDumpSmtSolverScript());
		consumer.accept("Path of dumped script: " + getPathOfDumpedScript());
		consumer.accept("Filename of dumped script: " + getBaseNameOfDumpedScript());
		consumer.accept("MapElimAlgo: " + (isUseOldMapElimination() ? "Matthias" : "Frank"));
	}

	/**
	 * Construct Settings for building a solver.
	 *
	 * @param filenameDumpedScript
	 *            basename (without path and file ending) of the SMT script that is dumped if dumpSmtSolverScript is set
	 *            to true
	 * @return a Settings object that allows us to build a new solver.
	 */
	default SolverSettings getSolverConstructionSettings(final String filenameDumpedScript) {
		final long timeoutSmtInterpol = 365 * 24 * 60 * 60 * 1000L;
		return new SolverSettings(isFakeNonIncrementalScript(), isExternalSolver(), getExternalSolverCommand(),
				timeoutSmtInterpol, null, isDumpSmtSolverScript(), getPathOfDumpedScript(), filenameDumpedScript);
	}

	default MapEliminationSettings getMapEliminationSettings(final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		return new MapEliminationSettings(isMapElimAddInequalities(), isMapElimOnlyTrivialImplicationsIndexAssignment(),
				isMapElimOnlyTrivialImplicationsArrayWrite(), isMapElimOnlyIndicesInFormula(), simplificationTechnique,
				xnfConversionTechnique);
	}
}