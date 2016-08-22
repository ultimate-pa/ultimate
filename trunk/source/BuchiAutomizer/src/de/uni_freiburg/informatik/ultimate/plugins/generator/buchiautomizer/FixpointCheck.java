/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoChecker.SynthesisResult;

public class FixpointCheck {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final ModifiableGlobalVariableManager mModifiableGlobalVariableManager;
	private final String mProcedureHonda;
	private final TransFormula mStem;
	private final TransFormula mLoop;
	
	public FixpointCheck(final IUltimateServiceProvider services, final ILogger logger, final ManagedScript managedScript,
			final ModifiableGlobalVariableManager modifiableGlobalVariableManager, final String procedureHonda, final TransFormula stem,
			final TransFormula loop) {
		super();
		mServices = services;
		mLogger = logger;
		mManagedScript = managedScript;
		mModifiableGlobalVariableManager = modifiableGlobalVariableManager;
		mProcedureHonda = procedureHonda;
		mStem = stem;
		mLoop = loop;
	}

	
	private void doSomething() {
		mManagedScript.lock(this);
		final Map<Term, Term> substitutionMappingStem = constructSubtitutionMapping(mStem, this::getConstantAtInit, this::getConstantAtHonda);
		final Map<Term, Term> substitutionMappingLoop = constructSubtitutionMapping(mLoop, this::getConstantAtHonda, this::getConstantAtHonda);
		final Term renamedStem = new Substitution(mManagedScript, substitutionMappingStem).transform(mStem.getFormula());
		final Term renamedLoop = new Substitution(mManagedScript, substitutionMappingStem).transform(mLoop.getFormula());
		mManagedScript.push(this, 1);
		mManagedScript.echo(this, new QuotedObject("Start fixpoint check"));
		mManagedScript.assertTerm(this, renamedStem);
		mManagedScript.assertTerm(this, renamedLoop);
		final LBool lbool = mManagedScript.checkSat(this);
		SynthesisResult result;
		switch (lbool) {
		case SAT:
			result = SynthesisResult.NONTERMINATING;
			break;
		case UNKNOWN:
			result = SynthesisResult.UNKNOWN;
			break;
		case UNSAT:
			result = SynthesisResult.UNKNOWN;
			break;
		default:
			break;
		}
		
	}

	private IProgramVar replaceOldByNonOld(final IProgramVar pv) {
		if (pv.isOldvar()) {
			return ((IProgramOldVar) pv).getNonOldVar();
		} else {
			return pv;
		}
	}
	
	private Map<Term, Term> constructSubtitutionMapping(final TransFormula tf, final IConstantMapper before, final IConstantMapper after) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			substitutionMapping.put(entry.getValue(), before.getConstant(entry.getKey()));
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			substitutionMapping.put(entry.getValue(), after.getConstant(entry.getKey()));
		}
		for (final TermVariable auxVar : tf.getAuxVars()) {
			substitutionMapping.put(auxVar, SmtUtils.termVariable2constant(mManagedScript.getScript(), auxVar, false));
		}
		return substitutionMapping;
	}
	
	
	private Term getConstantAtInit(final IProgramVar pv) {
		final IProgramVar updated = replaceOldByNonOld(pv);
		return updated.getDefaultConstant();
	}
	
	private Term getConstantAtHonda(final IProgramVar pv) {
		final boolean wasModifiedByStem = mStem.getAssignedVars().contains(pv);
		
		final IProgramVar updated;
		if (pv.isOldvar()) {
			final IProgramNonOldVar nonOld = ((IProgramOldVar) pv).getNonOldVar();
			if (mModifiableGlobalVariableManager.isModifiable(nonOld, mProcedureHonda)) {
				updated = pv;
			} else {
				updated = nonOld;
			}
		} else {
			updated = pv;
		}
		if (wasModifiedByStem) {
			return updated.getPrimedConstant();
		} else {
			return updated.getDefaultConstant();
		}
	}
	
	
	@FunctionalInterface
	public interface IConstantMapper {
		public Term getConstant(final IProgramVar key);
	}
}
