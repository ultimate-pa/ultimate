/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms;

import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Transform Boolean Term into disjunctive normal form.
 *
 * @author heizmann@informatik.uni-freiburg.de
 */

public class DnfTransformer extends XnfTransformer {

	public DnfTransformer(final ManagedScript script, final IUltimateServiceProvider services) {
		this(script, services, a -> false);
	}

	public DnfTransformer(final ManagedScript script, final IUltimateServiceProvider services,
			final Function<Integer, Boolean> funAbortIfExponential) {
		super(script, services, false, funAbortIfExponential);
	}

	@Override
	protected NnfTransformerHelper getNnfTransformerHelper(final IUltimateServiceProvider services) {
		return new DnfTransformerHelper(services);
	}

	protected class DnfTransformerHelper extends XnfTransformerHelper {

		protected DnfTransformerHelper(final IUltimateServiceProvider services) {
			super(services);
		}

		@Override
		public String innerConnectiveSymbol() {
			return "and";
		}

		@Override
		public String outerConnectiveSymbol() {
			return "or";
		}

		@Override
		public String innerJunctionName() {
			return "conjuction";
		}

		@Override
		public String outerJunctionName() {
			return "disjunction";
		}

		@Override
		public Term innerConnective(final Script script, final List<Term> params) {
			final Term result = SmtUtils.and(mScript, params);
			return result;
		}

		@Override
		public Term outerConnective(final Script script, final List<Term> params) {
			final Term result = SmtUtils.or(mScript, params);
			return result;
		}

		@Override
		public Term[] getOuterJuncts(final Term term) {
			return SmtUtils.getDisjuncts(term);
		}

	}

}
