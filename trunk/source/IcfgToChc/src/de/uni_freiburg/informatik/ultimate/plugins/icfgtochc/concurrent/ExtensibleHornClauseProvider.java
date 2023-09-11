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

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class ExtensibleHornClauseProvider {
	protected final ManagedScript mManagedScript;
	protected final Script mScript;
	protected final HcSymbolTable mSymbolTable;

	public ExtensibleHornClauseProvider(final ManagedScript mgdScript, final HcSymbolTable symbolTable) {
		mManagedScript = mgdScript;
		mScript = mgdScript.getScript();
		mSymbolTable = symbolTable;
	}

	protected final HornClauseBuilder createBuilder(final PredicateInfo headPredicate, final String comment) {
		return new HornClauseBuilder(mManagedScript, mSymbolTable, Objects.requireNonNull(headPredicate), comment);
	}

	protected final HornClauseBuilder createBuilder(final String comment) {
		return new HornClauseBuilder(mManagedScript, mSymbolTable, comment);
	}

	protected abstract List<HornClauseBuilder> buildAllClauses();

	public final List<HornClause> getClauses() {
		return buildAllClauses().stream().map(HornClauseBuilder::build)
				.filter(c -> !SmtUtils.isFalseLiteral(c.getConstraintFormula())).collect(Collectors.toList());
	}

	protected final Term numeral(final long n) {
		return mScript.numeral(BigInteger.valueOf(n));
	}

	protected Sort getIntSort() {
		return SmtSortUtils.getIntSort(mScript);
	}

	protected Sort getBoolSort() {
		return SmtSortUtils.getBoolSort(mScript);
	}
}
