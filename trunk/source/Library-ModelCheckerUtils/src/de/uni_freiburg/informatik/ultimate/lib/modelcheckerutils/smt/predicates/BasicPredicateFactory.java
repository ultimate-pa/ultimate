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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Factory for construction of {@link IPredicate}s that can also construct nontrivial predicates.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class BasicPredicateFactory extends SmtFreePredicateFactory {

	protected static final Set<IProgramVar> EMPTY_VARS = Collections.emptySet();
	protected static final String[] NO_PROCEDURE = new String[0];

	protected final IIcfgSymbolTable mSymbolTable;
	protected final Script mScript;

	protected final IUltimateServiceProvider mServices;
	protected final ManagedScript mMgdScript;
	protected final ILogger mLogger;

	public BasicPredicateFactory(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSymbolTable = symbolTable;
		mMgdScript = mgdScript;
		mScript = mgdScript.getScript();
	}

	public BasicPredicate newPredicate(final Term term) {
		assert term == mDontCareTerm
				|| UltimateNormalFormUtils.respectsUltimateNormalForm(term) : "Term not in UltimateNormalForm";
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

	public IPredicate newBuchiPredicate(final Set<IPredicate> inputPreds) {
		final Term conjunction = andTermFromPreds(inputPreds, SimplificationTechnique.NONE);
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
		return and(SimplificationTechnique.NONE, preds);
	}

	public IPredicate and(final SimplificationTechnique st, final Collection<IPredicate> preds) {
		return newPredicate(andTermFromPreds(preds, st));
	}

	public IPredicate or(final IPredicate... preds) {
		return or(Arrays.asList(preds));
	}

	public IPredicate or(final SimplificationTechnique st, final IPredicate... preds) {
		return or(st, Arrays.asList(preds));
	}

	public IPredicate or(final Collection<IPredicate> preds) {
		return or(SimplificationTechnique.NONE, preds);
	}

	public IPredicate or(final SimplificationTechnique st, final Collection<IPredicate> preds) {
		return newPredicate(orTermFromPreds(preds, st));
	}

	public IPredicate not(final IPredicate p) {
		return newPredicate(notTerm(p));
	}

	public IPredicate andT(final Term... terms) {
		return andT(Arrays.asList(terms));
	}

	public IPredicate andT(final SimplificationTechnique st, final Term... terms) {
		return andT(st, Arrays.asList(terms));
	}

	public IPredicate andT(final Collection<Term> terms) {
		return andT(SimplificationTechnique.NONE, terms);
	}

	public IPredicate andT(final SimplificationTechnique st, final Collection<Term> terms) {
		return newPredicate(andTerm(terms, st));
	}

	public IPredicate orT(final Term... terms) {
		return orT(Arrays.asList(terms));
	}

	public IPredicate orT(final SimplificationTechnique st, final Term... terms) {
		return orT(st, Arrays.asList(terms));
	}

	public IPredicate orT(final Collection<Term> terms) {
		return orT(SimplificationTechnique.NONE, terms);
	}

	public IPredicate orT(final SimplificationTechnique st, final Collection<Term> terms) {
		return newPredicate(orTerm(terms, st));
	}

	private Term orTermFromPreds(final Collection<IPredicate> preds, final SimplificationTechnique st) {
		return xJunctTermFromPreds(preds, st, SmtUtils::or, this::getFalse);
	}

	private Term andTermFromPreds(final Collection<IPredicate> preds, final SimplificationTechnique st) {
		return xJunctTermFromPreds(preds, st, SmtUtils::and, this::getTrue);
	}

	private Term xJunctTermFromPreds(final Collection<IPredicate> preds, final SimplificationTechnique st,
			final BiFunction<Script, Collection<Term>, Term> funCreateXJunct,
			final Supplier<Term> funGetNeutralElement) {
		final List<Term> terms = preds.stream().map(IPredicate::getFormula).collect(Collectors.toList());
		return xJunctTerm(terms, st, funCreateXJunct, funGetNeutralElement);
	}

	private Term orTerm(final Collection<Term> preds, final SimplificationTechnique st) {
		return xJunctTerm(preds, st, SmtUtils::or, this::getFalse);
	}

	private Term andTerm(final Collection<Term> preds, final SimplificationTechnique st) {
		return xJunctTerm(preds, st, SmtUtils::and, this::getTrue);
	}

	private Term xJunctTerm(final Collection<Term> terms, final SimplificationTechnique st,
			final BiFunction<Script, Collection<Term>, Term> funCreateXJunct,
			final Supplier<Term> funGetNeutralElement) {
		if (terms.stream().anyMatch(this::isDontCare)) {
			return mDontCareTerm;
		}
		if (terms.isEmpty()) {
			return funGetNeutralElement.get();
		}

		final Term xJunct = funCreateXJunct.apply(mScript, terms);
		if (st != SimplificationTechnique.NONE) {
			return SmtUtils.simplify(mMgdScript, xJunct, mServices, st);
		}
		return xJunct;
	}

	private Term notTerm(final IPredicate p) {
		if (isDontCare(p)) {
			return mDontCareTerm;
		}
		return SmtUtils.not(mScript, p.getFormula());
	}

	private Term getTrue() {
		return mScript.term("true");
	}

	private Term getFalse() {
		return mScript.term("false");
	}

}