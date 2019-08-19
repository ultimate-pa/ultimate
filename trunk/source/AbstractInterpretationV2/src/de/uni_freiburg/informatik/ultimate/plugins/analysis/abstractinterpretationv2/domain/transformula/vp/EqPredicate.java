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

import java.util.Collections;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqPredicate implements IPredicate {

	private final EqDisjunctiveConstraint<EqNode> mConstraint;
	private final String[] mProcedures;
	private final Set<IProgramVar> mVars;
	private final Term mClosedFormula;
	private final Term mFormula;
	private EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;

	public EqPredicate(final EqDisjunctiveConstraint<EqNode> constraint, final Set<IProgramVar> vars,
			final String[] procedures, final IIcfgSymbolTable symbolTable, final ManagedScript mgdScript,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory) {
		assert vars != null;
		assert vars.stream().allMatch(Objects::nonNull);
		mConstraint = constraint;
		mVars = vars;
		mProcedures = procedures;

		final Term constraintFormula = constraint.getTerm(mgdScript.getScript());
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(constraintFormula, mgdScript.getScript(),
				symbolTable);

//		final Term literalDisequalities = getLiteralDisequalities(constraint, mgdScript);
//		final Term literalDisequalities = eqNodeAndFunctionFactory.getNonTheoryLiteralDisequalities();
		final Term literalDisequalities = mConstraint.getFactory()
				.getWeqCcManager().getNonTheoryLiteralDisequalitiesIfNecessary();

		mClosedFormula = SmtUtils.and(mgdScript.getScript(), literalDisequalities, tvp.getClosedFormula());
		mFormula = SmtUtils.and(mgdScript.getScript(), literalDisequalities, tvp.getFormula());
	}



	public EqPredicate(final Term formula, final Set<IProgramVar> vars, final String[] procedures,
			final IIcfgSymbolTable symbolTable, final ManagedScript mgdScript,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory, final EqConstraintFactory<EqNode> eqConstraintFactory) {
		mConstraint = null;
		assert vars.stream().allMatch(Objects::nonNull);
		mVars = vars;
		mProcedures = procedures;

		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;


		final Term acc = formula;
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(acc, mgdScript.getScript(), symbolTable);

//		final Term literalDisequalities = getLiteralDisequalities(constraint, mgdScript);

//		final Term literalDisequalities = SmtUtils.and(mgdScript.getScript(),
//				CongruenceClosureSmtUtils.createDisequalityTermsForNonTheoryLiterals(mgdScript.getScript(),
//						collectLiteralsInFormula(formula)));
//		final Term literalDisequalities = eqNodeAndFunctionFactory.getNonTheoryLiteralDisequalities();;
		final Term literalDisequalities =
				eqConstraintFactory.getWeqCcManager().getNonTheoryLiteralDisequalitiesIfNecessary();

		mClosedFormula = SmtUtils.and(mgdScript.getScript(), literalDisequalities, tvp.getClosedFormula());
		mFormula = SmtUtils.and(mgdScript.getScript(), literalDisequalities, tvp.getFormula());
//		mClosedFormula = tvp.getClosedFormula();
//		mFormula = tvp.getFormula();

	}

	private Set<Term> collectLiteralsInFormula(final Term formula) {
		final Predicate<Term> pred = term -> term instanceof ConstantTerm
				|| mEqNodeAndFunctionFactory.getNonTheoryLiterals().contains(term);
		return new SubTermFinder(pred).findMatchingSubterms(formula);
	}

//	@Deprecated
//	private Term getLiteralDisequalities(final EqDisjunctiveConstraint<EqNode> constraint,
//			final ManagedScript mgdScript) {
//		final Term literalDisequalities = SmtUtils.and(mgdScript.getScript(),
//				CongruenceClosureSmtUtils.createDisequalityTermsForNonTheoryLiterals(
//						mgdScript.getScript(),
//						constraint.getAllLiteralNodes().stream()
//							.map(node -> node.getTerm()).collect(Collectors.toSet())));
//		return literalDisequalities;
//	}


	@Override
	public String[] getProcedures() {
		return mProcedures;
	}

	@Override
	public Set<IProgramVar> getVars() {
		return Collections.unmodifiableSet(mVars);
	}

	public EqDisjunctiveConstraint<EqNode> getEqConstraint() {
		assert mConstraint != null;
		return mConstraint;
	}


	@Override
	public String toString() {
		if (mConstraint != null) {
			return mConstraint.toString();
		} else {
			return mFormula.toString();
		}
	}

	public String toLogString() {
		if (mConstraint != null) {
			return mConstraint.toLogString();
		} else {
			return mFormula.toString();
		}
	}


	@Override
	public Term getFormula() {
		return mFormula;
	}

	@Override
	public Term getClosedFormula() {
		return mClosedFormula;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mConstraint == null) ? 0 : mConstraint.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final EqPredicate other = (EqPredicate) obj;
		if (mConstraint == null) {
			if (other.mConstraint != null) {
				return false;
			}
		} else if (!mConstraint.equals(other.mConstraint)) {
			return false;
		}
		return true;
	}
}
