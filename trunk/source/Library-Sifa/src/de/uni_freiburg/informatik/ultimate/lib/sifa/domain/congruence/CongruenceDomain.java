/*
 * Copyright (C) 2026 Max Lehr
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.StateBasedDomain;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Congruence abstract domain, based on Bagnara, Roberto & Dobson, Katy & Hill, Patricia & Mundell, Matthew &
 * Zaffanella, Enea "Grids: A Domain for Analyzing the Distribution of Numerical Values"
 * (https://www.researchgate.net/publication/221495908_Grids_A_Domain_for_Analyzing_the_Distribution_of_Numerical_Values)
 * and Dobson, Katy "Grid Domains for Analysing Software"
 * (https://www.researchgate.net/publication/265115063_Grid_Domains_for_Analysing_Software)
 *
 *
 * The congruence domain stores constraints of the form "∑ a_i * x_i = c" and "∑ a_i * x_i ≡b c" for numerical (ints and
 * reals) variables x_i and constants a_i, b and c. It uses a dual representation system where the constraint
 * representation uses vectors to directly represent the constraints and the generator representation storing vectors
 * that generate the space of the valid variable assignments.
 *
 * @author Max Lehr
 *
 */
public class CongruenceDomain extends StateBasedDomain<CongruenceState> {

	public CongruenceDomain(final SymbolicTools tools, final int maxDisjuncts, final ILogger logger,
			final Supplier<IProgressAwareTimer> timeout) {
		super(tools, maxDisjuncts, logger, timeout, new CongruenceStateProvider(tools.getScript()));
	}

	private static class CongruenceStateProvider implements IStateProvider<CongruenceState> {

		private final Script mScript;

		public CongruenceStateProvider(final Script script) {
			mScript = script;
		}

		@Override
		public CongruenceState toState(final Term[] conjuncts) {
			final List<EqualityRelation> equalityRelations = new ArrayList<>();
			final List<ModuloRelation> moduloRelations = new ArrayList<>();
			for (final Term conjunct : conjuncts) {

				if (CongruenceUtil.containsMod(conjunct)) {
					// Test for ModuloRelation
					final ModuloRelation conjunctModuloRelation = ModuloRelation.of(conjunct, mScript);
					if (conjunctModuloRelation != null) {
						moduloRelations.add(conjunctModuloRelation);
					}
				} else {
					// Otherwise test for EqualityRelation
					final EqualityRelation conjunctEqualityRelation = EqualityRelation.of(conjunct, mScript);
					if (conjunctEqualityRelation != null) {
						equalityRelations.add(conjunctEqualityRelation);
					}
				}
			}
			return CongruenceState.fromRelations(equalityRelations, moduloRelations);
		}

		@Override
		public CongruenceState getTopState() {
			return CongruenceState.TOP;
		}

		@Override
		public Term preprocessTerm(final Term term) {
			return term;
		}

	}

}