/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Mostafa Mahmoud Amin
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CodeCheck plug-in.
 *
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.Checker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.RedirectionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

public final class CodeCheckSettings {

	private String mDotGraphPath = "";
	private InterpolationTechnique mInterpolationMode = InterpolationTechnique.ForwardPredicates;
	private PredicateUnification mPredicateUnification = PredicateUnification.PER_VERIFICATION;
	private EdgeCheckOptimization mEdgeCheckOptimization = EdgeCheckOptimization.NONE;
	private Checker mChecker = Checker.ULTIMATE;
	private boolean mMemoizeNormalEdgeChecks = true;
	private boolean mMemoizeReturnEdgeChecks = true;
	private int mIterations = -1;
	private RedirectionStrategy mRedirectionStrategy = RedirectionStrategy.No_Strategy;
	private boolean mDefaultRedirection = true;
	private boolean mRemoveFalseNodes = false;
	private boolean mCheckSatisfiability = false;
	private boolean mUseInterpolantconsolidation = true;
	private boolean mUseSeparateSolverForTracechecks = true;
	private SolverMode mChooseSeparateSolverForTracechecks;
	private String mSeparateSolverForTracechecksCommand;
	private String mSeparateSolverForTracechecksTheory;
	private boolean mUseLiveVariables;
	private UnsatCores mUseUnsatCores;
	private boolean mUseFallbackForSeparateSolverForTracechecks;
	private boolean mUseAbstractInterpretation;

	public String getSeparateSolverForTracechecksCommand() {
		return mSeparateSolverForTracechecksCommand;
	}

	public void setSeparateSolverForTracechecksCommand(final String separateSolverForTracechecksCommand) {
		mSeparateSolverForTracechecksCommand = separateSolverForTracechecksCommand;
	}

	public boolean isUseFallbackForSeparateSolverForTracechecks() {
		return mUseFallbackForSeparateSolverForTracechecks;
	}

	public void
			setUseFallbackForSeparateSolverForTracechecks(final boolean useFallbackForSeparateSolverForTracechecks) {
		mUseFallbackForSeparateSolverForTracechecks = useFallbackForSeparateSolverForTracechecks;
	}

	public UnsatCores getUseUnsatCores() {
		return mUseUnsatCores;
	}

	public void setUseUnsatCores(final UnsatCores useUnsatCores) {
		mUseUnsatCores = useUnsatCores;
	}

	public boolean isUseLiveVariables() {
		return mUseLiveVariables;
	}

	public void setUseLiveVariables(final boolean useLiveVariables) {
		mUseLiveVariables = useLiveVariables;
	}

	public String getSeparateSolverForTracechecksTheory() {
		return mSeparateSolverForTracechecksTheory;
	}

	public void setSeparateSolverForTracechecksTheory(final String separateSolverForTracechecksTheory) {
		mSeparateSolverForTracechecksTheory = separateSolverForTracechecksTheory;
	}

	public SolverMode getChooseSeparateSolverForTracechecks() {
		return mChooseSeparateSolverForTracechecks;
	}

	public void setChooseSeparateSolverForTracechecks(final SolverMode chooseSeparateSolverForTracechecks) {
		mChooseSeparateSolverForTracechecks = chooseSeparateSolverForTracechecks;
	}

	public boolean isUseSeparateSolverForTracechecks() {
		return mUseSeparateSolverForTracechecks;
	}

	public void setUseSeparateSolverForTracechecks(final boolean useSeparateSolverForTracechecks) {
		mUseSeparateSolverForTracechecks = useSeparateSolverForTracechecks;
	}

	public boolean isUseInterpolantconsolidation() {
		return mUseInterpolantconsolidation;
	}

	public void setUseInterpolantconsolidation(final boolean useInterpolantconsolidation) {
		mUseInterpolantconsolidation = useInterpolantconsolidation;
	}

	public boolean isCheckSatisfiability() {
		return mCheckSatisfiability;
	}

	public void setCheckSatisfiability(final boolean checkSatisfiability) {
		mCheckSatisfiability = checkSatisfiability;
	}

	public boolean isRemoveFalseNodes() {
		return mRemoveFalseNodes;
	}

	public void setRemoveFalseNodes(final boolean removeFalseNodes) {
		mRemoveFalseNodes = removeFalseNodes;
	}

	public boolean isDefaultRedirection() {
		return mDefaultRedirection;
	}

	public void setDefaultRedirection(final boolean defaultRedirection) {
		mDefaultRedirection = defaultRedirection;
	}

	public RedirectionStrategy getRedirectionStrategy() {
		return mRedirectionStrategy;
	}

	public void setRedirectionStrategy(final RedirectionStrategy redirectionStrategy) {
		mRedirectionStrategy = redirectionStrategy;
	}

	public int getIterations() {
		return mIterations;
	}

	public void setIterations(final int iterations) {
		mIterations = iterations;
	}

	public boolean isMemoizeReturnEdgeChecks() {
		return mMemoizeReturnEdgeChecks;
	}

	public void setMemoizeReturnEdgeChecks(final boolean memoizeReturnEdgeChecks) {
		mMemoizeReturnEdgeChecks = memoizeReturnEdgeChecks;
	}

	public boolean isMemoizeNormalEdgeChecks() {
		return mMemoizeNormalEdgeChecks;
	}

	public void setMemoizeNormalEdgeChecks(final boolean memoizeNormalEdgeChecks) {
		mMemoizeNormalEdgeChecks = memoizeNormalEdgeChecks;
	}

	public Checker getChecker() {
		return mChecker;
	}

	public void setChecker(final Checker checker) {
		mChecker = checker;
	}

	public EdgeCheckOptimization getEdgeCheckOptimization() {
		return mEdgeCheckOptimization;
	}

	public void setEdgeCheckOptimization(final EdgeCheckOptimization edgeCheckOptimization) {
		mEdgeCheckOptimization = edgeCheckOptimization;
	}

	public PredicateUnification getPredicateUnification() {
		return mPredicateUnification;
	}

	public void setPredicateUnification(final PredicateUnification predicateUnification) {
		mPredicateUnification = predicateUnification;
	}

	public InterpolationTechnique getInterpolationMode() {
		return mInterpolationMode;
	}

	public void setInterpolationMode(final InterpolationTechnique interpolationMode) {
		mInterpolationMode = interpolationMode;
	}

	public String getDotGraphPath() {
		return mDotGraphPath;
	}

	public void setDotGraphPath(final String dotGraphPath) {
		mDotGraphPath = dotGraphPath;
	}

	public void setUseAbstractInterpretation(final boolean bool) {
		mUseAbstractInterpretation = bool;
	}

	public boolean getUseAbstractInterpretation() {
		return mUseAbstractInterpretation;
	}

}
