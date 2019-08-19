/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.FormulaToEqDisjunctiveConstraintConverter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class TransFormulaConverterCache {

	private final EqConstraintFactory<EqNode> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;

	private final Map<TransFormula, EqTransitionRelation> mTransformulaToEqTransitionRelationCache =
			new HashMap<>();

	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final VPDomainSettings mVPDomainSettings;

	public TransFormulaConverterCache(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory,
			final EqConstraintFactory<EqNode> eqConstraintFactory,
			final VPDomainSettings settings) {

		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
		mEqConstraintFactory = eqConstraintFactory;
		mMgdScript = mgdScript;
		mServices = services;
		mVPDomainSettings = settings;
	}

	/**
	 * Crashes if transition relation has not been constructed, yet.
	 *
	 * @param tf
	 * @return
	 */
	public EqTransitionRelation getTransitionRelationForTransformula(final TransFormula tf) {
		final EqTransitionRelation result = mTransformulaToEqTransitionRelationCache.get(tf);
		if (result == null) {
			throw new AssertionError();
		}
		return result;
	}

	public EqTransitionRelation getOrConstructEqTransitionRelationFromTransformula(final TransFormula tf) {
		EqTransitionRelation result = mTransformulaToEqTransitionRelationCache.get(tf);
		if (result == null) {
			result = convertTransformulaToEqTransitionRelation(tf);
			mTransformulaToEqTransitionRelationCache.put(tf, result);
		}
		return result;
	}

	private EqTransitionRelation convertTransformulaToEqTransitionRelation(final TransFormula tf) {
		final EqDisjunctiveConstraint<EqNode> constraint =
				new FormulaToEqDisjunctiveConstraintConverter(mServices, mMgdScript, mEqConstraintFactory,
						mEqNodeAndFunctionFactory, tf.getFormula()).getResult();

		assert !mVPDomainSettings.isCheckTransitionAbstractionCorrectness()
			|| transformulaImpliesResultConstraint(tf, constraint);

		return new EqTransitionRelation(constraint, tf);
	}

	protected Pair<Term, Term> makeShiftVariableSubstitution(final ManagedScript mgdScript, final TransFormula tf,
			final EqDisjunctiveConstraint<EqNode> resultConstraint) {

		final Map<Term, Term> substitutionMapping = new HashMap<>();

		for (final Entry<IProgramVar, TermVariable> iv : tf.getOutVars().entrySet()) {
			substitutionMapping.put(iv.getValue(), iv.getKey().getPrimedConstant());
		}
		for (final Entry<IProgramVar, TermVariable> iv : tf.getInVars().entrySet()) {
			substitutionMapping.put(iv.getValue(), iv.getKey().getDefaultConstant());
		}
		for (final TermVariable auxVar : tf.getAuxVars()) {
			final Term auxVarConst = ProgramVarUtils.getAuxVarConstant(mgdScript, auxVar);
			substitutionMapping.put(auxVar, auxVarConst);
		}

		final Substitution subs = new Substitution(mgdScript, substitutionMapping);
		final Term rcClosed= subs.transform(resultConstraint.getTerm(mgdScript.getScript()));

		assert rcClosed.getFreeVars().length == 0;

		final Term tfClosed = ((UnmodifiableTransFormula) tf).getClosedFormula();


//		final Set<Term> literalTerms = resultConstraint.getAllLiteralNodes().stream()
//				.map(node -> node.getTerm())
//				.collect(Collectors.toSet());
//		final List<Term> nontheoryLiteralDisequalities =
//				CongruenceClosureSmtUtils.createDisequalityTermsForNonTheoryLiterals(mgdScript.getScript(),
//						literalTerms);

		// we have to stregthen the transFormula with the disequalities between the "literals" we introduced ourselves
//		Term literalDisequalities = mEqNodeAndFunctionFactory.getNonTheoryLiteralDisequalities();
		final Term literalDisequalities =
				mEqConstraintFactory.getWeqCcManager().getNonTheoryLiteralDisequalitiesIfNecessary();
		final Term ante = SmtUtils.and(mgdScript.getScript(), tfClosed,
//				SmtUtils.and(mgdScript.getScript(), nontheoryLiteralDisequalities));
//				SmtUtils.and(mgdScript.getScript(), literalDisequalities));
				literalDisequalities);

		return new Pair<>(ante, rcClosed);
	}

	private boolean transformulaImpliesResultConstraint(final TransFormula tf,
			final EqDisjunctiveConstraint<EqNode> constraint) {
		mMgdScript.lock(this);
		mMgdScript.echo(this, new QuotedObject("Start implication check"));
		mMgdScript.push(this, 1);
		final Pair<Term, Term> anteAndSucc = makeShiftVariableSubstitution(mMgdScript, tf, constraint);

		final boolean result = implicationCheck(anteAndSucc.getFirst(), anteAndSucc.getSecond());

		mMgdScript.pop(this, 1);
		mMgdScript.echo(this, new QuotedObject("End implication check"));
		mMgdScript.unlock(this);

		return result;
	}

	protected boolean implicationCheck(final Term ante, final Term succ) {
		final ManagedScript mgdScript = mMgdScript;

		mgdScript.assertTerm(this, ante);
		mgdScript.assertTerm(this, Util.not(mgdScript.getScript(), succ));

		final LBool result = mgdScript.checkSat(this);
		if (result != LBool.UNSAT) {
			assert false;
		}
		return result == LBool.UNSAT;
	}

	/**
	 *
	 * @return all EqTransitionRelations that have been computed so far
	 */
	public Collection<EqTransitionRelation> getAllTransitionRelations() {
		return Collections.unmodifiableCollection(mTransformulaToEqTransitionRelationCache.values());
	}
}
