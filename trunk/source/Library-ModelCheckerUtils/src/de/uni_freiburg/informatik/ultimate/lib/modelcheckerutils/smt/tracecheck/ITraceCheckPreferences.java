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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier.ScoringMethod;

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
	public enum AssertCodeBlockOrderType {
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
		 * Similar to {@link AssertCodeBlockOrderType#OUTSIDE_LOOP_FIRST2}, but in reverse order (start with the deepest
		 * codeblocks).
		 */
		INSIDE_LOOP_FIRST1,

		/**
		 * Similar to {@link AssertCodeBlockOrderType#OUTSIDE_LOOP_FIRST2} and
		 * {@link AssertCodeBlockOrderType#INSIDE_LOOP_FIRST1} in that it also uses the depth of a codeblock. This
		 * setting alternates between depths, starting with depth 0, then asserting the maximal depth, then depth 1,
		 * etc.
		 */
		MIX_INSIDE_OUTSIDE,

		/**
		 * Assert in two steps: First terms with small constants (currently, terms that contain constants smaller than
		 * 10), then the rest.
		 */
		TERMS_WITH_SMALL_CONSTANTS_FIRST,

		/**
		 * Use the SMT feature heuristic together with additional parameters.
		 */
		SMT_FEATURE_HEURISTIC
	}

	public enum SmtFeatureHeuristicPartitioningType {
		FIXED_NUM_PARTITIONS, THRESHOLD
	}

	/**
	 * Container that holds all settings related to {@link AssertCodeBlockOrderType}.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public class AssertCodeBlockOrder {

		public static final SmtFeatureHeuristicPartitioningType DEF_PARTITIONING_STRATEGY =
				SmtFeatureHeuristicPartitioningType.FIXED_NUM_PARTITIONS;
		public static final ScoringMethod DEF_SCORING_METHOD = ScoringMethod.NUM_FUNCTIONS;
		public static final int DEF_NUM_PARTITIONS = 4;
		public static final double DEF_SCORE_THRESHOLD = 0.75;
		public static final AssertCodeBlockOrder NOT_INCREMENTALLY =
				new AssertCodeBlockOrder(AssertCodeBlockOrderType.NOT_INCREMENTALLY);

		private final AssertCodeBlockOrderType mAssertCodeBlockOrderType;
		private final SmtFeatureHeuristicPartitioningType mSmtFeatureHeuristicPartitioningType;
		private final ScoringMethod mSmtFeatureHeuristicScoringMethod;
		private final int mSmtFeatureHeuristicNumPartitions;
		private final double mSmtFeatureHeuristicThreshold;

		public AssertCodeBlockOrder(final AssertCodeBlockOrderType assertCodeBlockOrderType) {
			mAssertCodeBlockOrderType = assertCodeBlockOrderType;
			mSmtFeatureHeuristicPartitioningType = DEF_PARTITIONING_STRATEGY;
			mSmtFeatureHeuristicScoringMethod = DEF_SCORING_METHOD;
			mSmtFeatureHeuristicNumPartitions = DEF_NUM_PARTITIONS;
			mSmtFeatureHeuristicThreshold = DEF_SCORE_THRESHOLD;
		}

		public AssertCodeBlockOrder(final AssertCodeBlockOrderType assertCodeBlockOrderType,
				final SmtFeatureHeuristicPartitioningType smtFeatureHeuristicPartitioningType,
				final ScoringMethod smtFeatureHeuristicScoringMethod, final int smtFeatureHeuristicNumPartitions,
				final double smtFeatureHeuristicThreshold) {
			mAssertCodeBlockOrderType = assertCodeBlockOrderType;
			mSmtFeatureHeuristicPartitioningType = smtFeatureHeuristicPartitioningType;
			mSmtFeatureHeuristicScoringMethod = smtFeatureHeuristicScoringMethod;
			mSmtFeatureHeuristicNumPartitions = smtFeatureHeuristicNumPartitions;
			mSmtFeatureHeuristicThreshold = smtFeatureHeuristicThreshold;
		}

		public AssertCodeBlockOrderType getAssertCodeBlockOrderType() {
			return mAssertCodeBlockOrderType;
		}

		public SmtFeatureHeuristicPartitioningType getSmtFeatureHeuristicPartitioningType() {
			return mSmtFeatureHeuristicPartitioningType;
		}

		public ScoringMethod getSmtFeatureHeuristicScoringMethod() {
			return mSmtFeatureHeuristicScoringMethod;
		}

		public int getSmtFeatureHeuristicNumPartitions() {
			return mSmtFeatureHeuristicNumPartitions;
		}

		public double getSmtFeatureHeuristicThreshold() {
			return mSmtFeatureHeuristicThreshold;
		}

		@Override
		public String toString() {
			if (mAssertCodeBlockOrderType != AssertCodeBlockOrderType.SMT_FEATURE_HEURISTIC) {
				return mAssertCodeBlockOrderType.toString();
			}
			switch (mSmtFeatureHeuristicPartitioningType) {
			case FIXED_NUM_PARTITIONS:
				return String.format("%s (partitioning type %s, %s partitions)", mAssertCodeBlockOrderType.toString(),
						mSmtFeatureHeuristicPartitioningType.toString(),
						String.valueOf(mSmtFeatureHeuristicNumPartitions));
			case THRESHOLD:
				return String.format("%s (partitioning type %s, threshold %s)", mAssertCodeBlockOrderType.toString(),
						mSmtFeatureHeuristicPartitioningType.toString(), String.valueOf(mSmtFeatureHeuristicThreshold));
			default:
				return String.format("%s (unknown partitioning type %s)", mAssertCodeBlockOrderType.toString(),
						mSmtFeatureHeuristicPartitioningType.toString());
			}
		}

	}

	boolean getUseSeparateSolverForTracechecks();

	AssertCodeBlockOrder getAssertCodeBlockOrder();

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

	CfgSmtToolkit getCfgSmtToolkit();

	boolean collectInterpolantStatistics();

	boolean computeCounterexample();

}