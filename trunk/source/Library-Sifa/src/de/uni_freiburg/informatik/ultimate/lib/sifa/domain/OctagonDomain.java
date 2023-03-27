/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.RewriteEqualityTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.OctagonRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * Octagon abstract domain, based on A. Miné's "The octagon abstract domain"
 * (https://www-apr.lip6.fr/~mine/publi/article-mine-ast01.pdf).
 *
 * Octagons are a weakly relational abstract domain and store constraints of the form "±x ± y ≤ c" for numerical (ints
 * and reals) variables x, y and a constant c. Boolean variables are stored separately, using the non-relation powerset
 * domain. Other types (bit-vectors for instance) are not supported.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class OctagonDomain extends StateBasedDomain<OctagonState> {
	public OctagonDomain(final ILogger logger, final SymbolicTools tools, final int maxDisjuncts,
			final Supplier<IProgressAwareTimer> timeout) {
		super(tools, maxDisjuncts, logger, timeout, new OctagonStateProvider(tools.getScript()));
	}

	private static class OctagonStateProvider implements IStateProvider<OctagonState> {
		private final Script mScript;
		private final TermTransformer mTermTransformer;

		public OctagonStateProvider(final Script script) {
			mScript = script;
			mTermTransformer = new RewriteEqualityTransformer(script);
		}

		@Override
		public OctagonState toState(final Term[] conjuncts) {
			final List<OctagonRelation> octRelations = new ArrayList<>();
			final Set<Term> vars = new HashSet<>();
			for (final Term conjunct : conjuncts) {
				final PolynomialRelation polynomial = PolynomialRelation.of(mScript, conjunct);
				if (polynomial == null) {
					continue;
				}
				final OctagonRelation octRel = OctagonRelation.from(polynomial);
				if (octRel == null) {
					continue;
				}
				octRelations.add(octRel);
				vars.add(octRel.getVar1());
				vars.add(octRel.getVar2());
			}
			boolean allVarsAreInt = true;
			final Map<Term, Integer> varToIndex = new HashMap<>();
			vars.stream().sorted((x, y) -> x.toString().compareTo(y.toString()))
					.forEach(x -> varToIndex.put(x, varToIndex.size()));
			final OctagonMatrix resultMatrix = new OctagonMatrix(varToIndex.size());
			for (final OctagonRelation octRel : octRelations) {
				allVarsAreInt &= !SmtSortUtils.isRealSort(octRel.getVar1().getSort());
				resultMatrix.processRelation(octRel, varToIndex);
			}
			return new OctagonState(varToIndex, resultMatrix, allVarsAreInt);
		}

		@Override
		public OctagonState getTopState() {
			return OctagonState.TOP;
		}

		@Override
		public Term preprocessTerm(final Term term) {
			// TODO consider removing boolean sub-terms before computing DNF as we don't use the boolean terms anyways
			return mTermTransformer.transform(term);
		}
	}
}
