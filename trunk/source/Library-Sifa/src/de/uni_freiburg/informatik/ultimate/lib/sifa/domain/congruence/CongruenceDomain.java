package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

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
			final Set<Term> vars = new HashSet<>();
			for (final Term conjunct : conjuncts) {

				if (CongruenceUtil.containsMod(conjunct)) {
					// Test for ModuloRelation
					final ModuloRelation conjunctModuloRelation = ModuloRelation.of(conjunct, mScript);
					if (conjunctModuloRelation != null) {
						moduloRelations.add(conjunctModuloRelation);
						vars.addAll(conjunctModuloRelation.getVars());
					}
				} else {
					// Otherwise test for EqualityRelation
					final EqualityRelation conjunctEqualityRelation = EqualityRelation.of(conjunct, mScript);
					if (conjunctEqualityRelation != null) {
						equalityRelations.add(conjunctEqualityRelation);
						vars.addAll(conjunctEqualityRelation.getVars());
					}
				}

			}
			final Map<Term, Integer> varToIndex = new HashMap<>();
			int freeIndex = 1;
			for (final Term var : vars) {
				varToIndex.put(var, freeIndex);
				freeIndex++;
			}

			final List<RationalVector> equalities = new ArrayList<>();
			final List<RationalVector> congruences = new ArrayList<>();
			for (final EqualityRelation equalityRelation : equalityRelations) {
				equalities.add(CongruenceUtil.getVector(equalityRelation, varToIndex));
			}
			for (final ModuloRelation moduloRelation : moduloRelations) {
				congruences.add(CongruenceUtil.getVector(moduloRelation, varToIndex));
			}

			final var vectorLength = varToIndex.size() + 1;

			// Add that 1 % 1 = 0
			congruences.add(RationalVector.getUnitVector(0, vectorLength).negate());

			return new CongruenceState(varToIndex, new ConstraintRepresentation(equalities, congruences, vectorLength));
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