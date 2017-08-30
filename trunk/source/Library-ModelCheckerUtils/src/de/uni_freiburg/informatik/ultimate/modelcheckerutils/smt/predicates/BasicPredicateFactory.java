/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Factory for construction of {@link IPredicate}s with unique serial numbers. Sometimes we need different
 * {@link IPredicate} objects with the same formulas. The serial number ensures that {@link IPredicate}s can be
 * different, can be used as a hash code and ease debugging.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class BasicPredicateFactory {

	protected static final Set<IProgramVar> EMPTY_VARS = Collections.emptySet();
	protected static final String[] NO_PROCEDURE = new String[0];

	protected final IIcfgSymbolTable mSymbolTable;
	protected final Script mScript;
	protected final SimplificationTechnique mSimplificationTechnique;
	protected final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * Serial numbers for predicates start with 1, because 0 is reserved for the axioms.
	 */
	protected int mSerialNumberCounter = 1;

	protected final IUltimateServiceProvider mServices;
	protected final ManagedScript mMgdScript;
	protected final ILogger mLogger;
	protected final Term mDontCareTerm;
	protected final Term mEmptyStackTerm;

	public BasicPredicateFactory(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mDontCareTerm = new AuxiliaryTerm("don't care");
		mEmptyStackTerm = new AuxiliaryTerm("emptyStack");
		mSymbolTable = symbolTable;
		mMgdScript = mgdScript;
		mScript = mgdScript.getScript();
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
	}

	protected Term getDontCareTerm() {
		return mDontCareTerm;
	}

	protected int constructFreshSerialNumber() {
		return mSerialNumberCounter++;
	}

	/**
	 * Returns true iff each free variables corresponds to a BoogieVar or will be quantified. Throws an Exception
	 * otherwise.
	 */
	private boolean checkIfValidPredicate(final Term term, final Set<TermVariable> quantifiedVariables) {
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar bv = mSymbolTable.getProgramVar(tv);
			if (bv == null) {
				if (!quantifiedVariables.contains(tv)) {
					throw new AssertionError("Variable " + tv + " does not corresponds to a BoogieVar, and is"
							+ " not quantified, hence this formula cannot" + " define a predicate: " + term);
				}
			}
		}
		return true;
	}

	public boolean isDontCare(final IPredicate pred) {
		return pred.getFormula() == mDontCareTerm;
	}

	public boolean isDontCare(final Term term) {
		return term == mDontCareTerm;
	}

	public BasicPredicate newPredicate(final Term term) {
		final TermVarsProc termVarsProc = constructTermVarsProc(term);
		final BasicPredicate predicate = new BasicPredicate(constructFreshSerialNumber(), termVarsProc.getProcedures(),
				termVarsProc.getFormula(), termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return predicate;
	}

	protected TermVarsProc constructTermVarsProc(final Term term) {
		final TermVarsProc termVarsProc;
		if (term == mDontCareTerm) {
			termVarsProc = constructDontCare();
		} else {
			termVarsProc = TermVarsProc.computeTermVarsProc(term, mScript, mSymbolTable);
		}
		return termVarsProc;
	}

	private TermVarsProc constructDontCare() {
		return new TermVarsProc(mDontCareTerm, EMPTY_VARS, NO_PROCEDURE, mDontCareTerm);
	}

	public DebugPredicate newDebugPredicate(final String debugMessage) {
		return new DebugPredicate(debugMessage, constructFreshSerialNumber(), mDontCareTerm);
	}

	public IPredicate newBuchiPredicate(final Set<IPredicate> inputPreds) {
		final Term conjunction = andTerm(inputPreds, SimplificationTechnique.NONE);
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(conjunction, mScript, mSymbolTable);
		return new BuchiPredicate(constructFreshSerialNumber(), tvp.getProcedures(), tvp.getFormula(), tvp.getVars(),
				tvp.getClosedFormula(), inputPreds);
	}

	public IPredicate and(final IPredicate... preds) {
		return and(Arrays.asList(preds));
	}
	
	public IPredicate and(final SimplificationTechnique st, final IPredicate... preds) {
		return and(st, Arrays.asList(preds));
	}

	public IPredicate and(final Collection<IPredicate> preds) {
		return newPredicate(andTerm(preds, SimplificationTechnique.NONE));
	}
	
	public IPredicate and(final SimplificationTechnique st, final Collection<IPredicate> preds) {
		return newPredicate(andTerm(preds, st));
	}

	public IPredicate or(final boolean withSimplifyDDA, final IPredicate... preds) {
		return newPredicate(orTerm(withSimplifyDDA, Arrays.asList(preds)));
	}

	public IPredicate or(final boolean withSimplifyDDA, final Collection<IPredicate> preds) {
		return newPredicate(orTerm(withSimplifyDDA, preds));
	}

	public IPredicate not(final IPredicate p) {
		return newPredicate(notTerm(p));
	}

	private Term orTerm(final boolean withSimplifyDDA, final Collection<IPredicate> preds) {
		Term term = mScript.term("false");
		for (final IPredicate p : preds) {
			if (isDontCare(p)) {
				return mDontCareTerm;
			}
			term = SmtUtils.or(mScript, term, p.getFormula());
		}
		if (withSimplifyDDA) {
			term = SmtUtils.simplify(mMgdScript, term, mServices, mSimplificationTechnique);
		}
		return term;
	}

	private Term andTerm(final Collection<IPredicate> preds, final SimplificationTechnique st) {
		Term term = mScript.term("true");
		for (final IPredicate p : preds) {
			if (isDontCare(p)) {
				return mDontCareTerm;
			}
			term = SmtUtils.and(mScript, term, p.getFormula());
		}
		if (st != SimplificationTechnique.NONE) {
			return SmtUtils.simplify(mMgdScript, term, mServices, st);
		}
		return term;
	}

	private Term notTerm(final IPredicate p) {
		if (isDontCare(p)) {
			return mDontCareTerm;
		}
		return SmtUtils.not(mScript, p.getFormula());
	}

	private static final class AuxiliaryTerm extends Term {

		private final String mName;

		private AuxiliaryTerm(final String name) {
			super(0);
			mName = name;
		}

		@Override
		public Sort getSort() {
			throw new UnsupportedOperationException("Auxiliary term has no sort");
		}

		@Override
		public void toStringHelper(final ArrayDeque<Object> todo) {
			throw new UnsupportedOperationException("Auxiliary term must not be subterm of other terms");
		}

		@Override
		public TermVariable[] getFreeVars() {
			throw new UnsupportedOperationException("Auxiliary term has no vars");
		}

		@Override
		public Theory getTheory() {
			throw new UnsupportedOperationException("Auxiliary term has no theory");
		}

		@Override
		public String toString() {
			return mName;
		}

		@Override
		public String toStringDirect() {
			return mName;
		}

		@Override
		public int hashCode() {
			throw new UnsupportedOperationException("Auxiliary term must not be contained in any collection");
		}
	}

}