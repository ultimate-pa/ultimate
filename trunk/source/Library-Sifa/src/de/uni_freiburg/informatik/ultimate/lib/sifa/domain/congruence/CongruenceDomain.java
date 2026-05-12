package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.StateBasedDomain;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class CongruenceDomain extends StateBasedDomain<CongruenceState> {

	public CongruenceDomain(final SymbolicTools tools, final int maxDisjuncts, final ILogger logger,
			final Supplier<IProgressAwareTimer> timeout) {
		super(tools, maxDisjuncts, logger, timeout, new CongruenceStateProvider(tools.getScript()));
		// TODO Auto-generated constructor stub
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

				// Test for ModuloRelation
				final List<ModuloRelation> conjunctModuloRelations = ModuloRelation.of(conjunct, mScript);
				if (conjunctModuloRelations != null) {
					moduloRelations.addAll(conjunctModuloRelations);
					for (final ModuloRelation conjunctModuloRelation : conjunctModuloRelations) {
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

			final List<MatrixQ128> equalities = new ArrayList<>();
			final List<MatrixQ128> congruences = new ArrayList<>();
			for (final EqualityRelation equalityRelation : equalityRelations) {
				equalities.add(equalityRelation.getVector(varToIndex));
			}
			for (final ModuloRelation moduloRelation : moduloRelations) {
				congruences.add(moduloRelation.getVector(varToIndex));
			}

			final var vectorLength = varToIndex.size() + 1;

			// Add that 1 % 1 = 0
			final List<Integer> list = new ArrayList<>(Collections.nCopies(vectorLength, 0));
			list.set(0, -1);
			congruences.add(CongruenceUtil.getRowVectorFromIntList(list));

			return new CongruenceState(varToIndex, new ConstraintRepresentation(equalities, congruences, vectorLength));
		}

		@Override
		public CongruenceState getTopState() {
			return CongruenceState.TOP;
		}

		@Override
		public Term preprocessTerm(final Term term) {
			// TODO Auto-generated method stub
			return term;
		}

	}

}