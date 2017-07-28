/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult.Equality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class IncrementalEqualityAnalyzer {
	private final ILogger mLogger;
	private final Term mTerm;
	private final Script mScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final ReplacementVarFactory mRepvarFactory;
	private final ModifiableTransFormula mTransFormula;

	private final Set<Doubleton<Term>> mDistinctDoubletons = new LinkedHashSet<>();
	private final Set<Doubleton<Term>> mEqualDoubletons = new LinkedHashSet<>();
	private final Set<Doubleton<Term>> mUnknownDoubletons = new LinkedHashSet<>();
	/**
	 * Doubletons that we do not check because they do not occur in the formula.
	 */
	private final Set<Doubleton<Term>> mIgnoredDoubletons = new LinkedHashSet<>();

	private final EqualityAnalysisResult mInvariantEqualitiesBefore;
	private final EqualityAnalysisResult mInvariantEqualitiesAfter;

	private final boolean mUseArrayIndexSupportingInvariants = true;
	
	private final ManagedScript mMgdScript = null;

	public IncrementalEqualityAnalyzer(final Term term, final Set<Doubleton<Term>> doubletons, final IIcfgSymbolTable symbolTable,
			final ModifiableTransFormula tf, final EqualityAnalysisResult invariantEqualitiesBefore,
			final EqualityAnalysisResult invariantEqualitiesAfter, final ILogger logger,
			final ReplacementVarFactory replacementVarFactory, final ManagedScript mgdScript) {
		super();
		mLogger = logger;
		mTerm = term;
		mSymbolTable = symbolTable;
		mRepvarFactory = replacementVarFactory;
		mScript = mgdScript.getScript();
		mTransFormula = tf;
		mInvariantEqualitiesBefore = invariantEqualitiesBefore;
		mInvariantEqualitiesAfter = invariantEqualitiesAfter;
		final Set<Doubleton<Term>> allDoubletons = doubletons;

		final Term termWithAdditionalInvariants;

	}
	
	
	public void startAnalysis(final Term context) {
		// TODO: do assert an locking on-demand
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		mMgdScript.assertTerm(this, context);
	}
	
	public Equality checkEquality(final Term lhs, final Term rhs) {
		mMgdScript.push(this, 1);
		return null;
		
	}
	
	
	public void finishAnalysis() {
		mMgdScript.pop(this, 1);
		mMgdScript.unlock(this);
	}
}

