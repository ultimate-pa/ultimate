/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcBodyVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.IcfgToChcConcurrent.IHcReplacementVar;

public class HornClauseBuilder {
	private final ManagedScript mManagedScript;
	private final HcSymbolTable mSymbolTable;
	private final PredicateInfo mHeadPredicate;

	private final Map<TermVariable, Term> mSubstitution = new HashMap<>();
	private final List<HcPredicateSymbol> mBodyPreds = new ArrayList<>();
	private final List<List<Term>> mBodyArgs = new ArrayList<>();
	private final List<Term> mConstraints = new ArrayList<>();
	private final Set<HcVar> mBodyVars = new HashSet<>();

	public HornClauseBuilder(final ManagedScript mgdScript, final HcSymbolTable symbolTable,
			final PredicateInfo headPredicate) {
		mManagedScript = mgdScript;
		mSymbolTable = symbolTable;
		mHeadPredicate = headPredicate;
	}

	public HornClauseBuilder(final ManagedScript mgdScript, final HcSymbolTable symbolTable) {
		this(mgdScript, symbolTable, null);
	}

	public HcBodyVar getFreshBodyVar(final Object identifier, final Sort sort) {
		// TODO Using the number of bodyVars as index is a hack!
		// TODO suitable parameters for getOrConstructBodyVar
		final HcBodyVar auxVar = mSymbolTable.getOrConstructBodyVar(null, mBodyVars.size(), sort, identifier);
		mBodyVars.add(auxVar);
		return auxVar;
	}

	public HcBodyVar getBodyVar(final IHcReplacementVar variable) {
		// TODO suitable parameters for getOrConstructBodyVar
		final var result = mSymbolTable.getOrConstructBodyVar(null, -1, variable.getSort(), variable);
		mBodyVars.add(result);
		return result;
	}

	public HcHeadVar getHeadVar(final IHcReplacementVar variable) {
		// TODO
		assert mHeadPredicate.hasParameter(variable);
		return null;
	}

	public void sameBodyHeadVar(final IHcReplacementVar variable) {
		mSubstitution.put(getBodyVar(variable).getTermVariable(), getHeadVar(variable).getTerm());
	}

	public List<Term> getDefaultBodyArgs(final PredicateInfo predicate) {
		return IntStream.range(0, predicate.getParamCount())
				.mapToObj(i -> getBodyVar(predicate.getParameter(i)).getTerm())
				.collect(Collectors.toCollection(ArrayList::new));
	}

	public void addBodyPredicate(final PredicateInfo predicate, final List<Term> arguments) {
		mBodyPreds.add(predicate.getPredicate());
		mBodyArgs.add(arguments);
	}

	public void addConstraint(final Term term) {
		mConstraints.add(term);
	}

	public HornClause build() {
		final var constraint = getSubstitutedConstraint();

		final var substitutedBodyArgs = new ArrayList<List<Term>>(mBodyArgs.size());
		for (final var args : mBodyArgs) {
			substitutedBodyArgs.add(args.stream().map(this::substitute).collect(Collectors.toList()));
		}

		return new HornClause(mManagedScript, mSymbolTable, constraint, mBodyPreds, substitutedBodyArgs, mBodyVars);
	}

	private Term substitute(final Term term) {
		if (mSubstitution.isEmpty()) {
			return term;
		}
		return Substitution.apply(mManagedScript, mSubstitution, term);
	}

	private Term getSubstitutedConstraint() {
		if (mConstraints.isEmpty()) {
			return null;
		}
		return substitute(SmtUtils.and(mManagedScript.getScript(), mConstraints));
	}
}
