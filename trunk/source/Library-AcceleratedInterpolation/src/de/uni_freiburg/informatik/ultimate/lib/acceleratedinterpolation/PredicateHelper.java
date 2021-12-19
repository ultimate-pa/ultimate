
/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class PredicateHelper<LETTER extends IIcfgTransition<?>> {
	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;

	public PredicateHelper(final IPredicateUnifier predicateUnifier,
			final PredicateTransformer<Term, IPredicate, TransFormula> predTransformer, final ILogger logger,
			final ManagedScript script, final IUltimateServiceProvider services) {
		mPredicateUnifier = predicateUnifier;
		mPredTransformer = predTransformer;
		mScript = script;
		mLogger = logger;
		mServices = services;
	}

	public UnmodifiableTransFormula traceToTf(final List<LETTER> trace) {
		final List<UnmodifiableTransFormula> tfs = new ArrayList<>();
		for (final LETTER l : trace) {
			tfs.add(l.getTransformula());
		}
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mScript, false, false, false,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.SIMPLIFY_DDA, tfs);
	}

	public List<UnmodifiableTransFormula> traceToListOfTfs(final List<LETTER> trace) {
		final List<UnmodifiableTransFormula> tfs = new ArrayList<>();
		for (final LETTER l : trace) {
			tfs.add(l.getTransformula());
		}
		return tfs;
	}

	/**
	 * replace variables in term with its default termvariables, needed for {@link IPredicate} creation
	 *
	 * @param t
	 * @return
	 */
	public Term normalizeTerm(final UnmodifiableTransFormula t) {
		final HashMap<Term, Term> subMap = new HashMap<>();
		final Term tTerm = t.getFormula();

		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();

		for (final Entry<IProgramVar, TermVariable> outVar : t.getOutVars().entrySet()) {
			subMap.put(outVar.getValue(), outVar.getKey().getTermVariable());
			outVars.put(outVar.getKey(), outVar.getKey().getTermVariable());
		}
		for (final Entry<IProgramVar, TermVariable> inVar : t.getInVars().entrySet()) {
			subMap.put(inVar.getValue(), inVar.getKey().getTermVariable());
			inVars.put(inVar.getKey(), inVar.getKey().getTermVariable());
		}
		final PureSubstitution sub = new PureSubstitution(mScript, subMap);
		final Term newTerm = sub.transform(tTerm);
		return newTerm;
	}

	/**
	 * replace variables in term with its default termvariables, needed for {@link IPredicate} creation
	 *
	 * @param tf
	 * @return
	 */
	public UnmodifiableTransFormula normalizeTerm(final Term t, final UnmodifiableTransFormula tf,
			final Boolean fresh) {
		final HashMap<Term, Term> subMap = new HashMap<>();
		final Term tTerm = t;

		final Map<IProgramVar, TermVariable> inVars;
		final Map<IProgramVar, TermVariable> outVars;

		final Term newTerm;
		if (fresh) {
			inVars = new HashMap<>();
			outVars = new HashMap<>();
			for (final Entry<IProgramVar, TermVariable> outVar : tf.getOutVars().entrySet()) {
				final TermVariable newTV;
				newTV = mScript.constructFreshCopy(outVar.getKey().getTermVariable());
				subMap.put(outVar.getValue(), newTV);
				outVars.put(outVar.getKey(), newTV);
			}
			for (final Entry<IProgramVar, TermVariable> inVar : tf.getInVars().entrySet()) {
				final TermVariable newTV;
				newTV = mScript.constructFreshCopy(inVar.getKey().getTermVariable());
				subMap.put(inVar.getValue(), newTV);
				inVars.put(inVar.getKey(), newTV);
			}
			final PureSubstitution sub = new PureSubstitution(mScript, subMap);
			newTerm = sub.transform(tTerm);
		} else {
			inVars = new HashMap<>(tf.getInVars());
			outVars = new HashMap<>(tf.getOutVars());
			newTerm = tTerm;
		}
		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, true, Collections.emptySet(), true,
				Collections.emptySet(), false);
		tfb.setFormula(newTerm);
		tfb.addAuxVarsButRenameToFreshCopies(tf.getAuxVars(), mScript);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mScript);
	}

	/**
	 * To make a given loopacceleration reflexive, create disjunction of acceleration and conjunction of equalities
	 * between in and out vars
	 *
	 * @param t
	 * @param acceleration
	 * @return
	 */
	public Term makeReflexive(final Term t, final UnmodifiableTransFormula acceleration) {
		final Map<IProgramVar, TermVariable> invars = acceleration.getInVars();
		final Map<IProgramVar, TermVariable> outvars = acceleration.getOutVars();
		final List<Term> equalities = new ArrayList<>();
		for (final Entry<IProgramVar, TermVariable> invar : invars.entrySet()) {
			final IProgramVar var = invar.getKey();
			final TermVariable invarTV = invar.getValue();
			final TermVariable outvarTV = outvars.get(var);
			final Term equality = SmtUtils.binaryEquality(mScript.getScript(), invarTV, outvarTV);
			equalities.add(equality);
		}
		final Term conjunct = SmtUtils.and(mScript.getScript(), equalities);
		return SmtUtils.or(mScript.getScript(), t, conjunct);
	}

	public boolean predContainsTfVar(final IPredicate predicate, final UnmodifiableTransFormula tf) {
		final Set<IProgramVar> predVars = predicate.getVars();
		final Set<IProgramVar> tfInVars = tf.getInVars().keySet();
		final Set<IProgramVar> tfOutVars = tf.getOutVars().keySet();
		for (final IProgramVar pv : predVars) {
			if (tfInVars.contains(pv) || tfOutVars.contains(pv)) {
				return true;
			}
		}
		return false;
	}
}
