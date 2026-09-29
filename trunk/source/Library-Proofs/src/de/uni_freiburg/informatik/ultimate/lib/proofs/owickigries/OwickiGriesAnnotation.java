/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.IProof;
import de.uni_freiburg.informatik.ultimate.lib.proofs.ThreadModularPrePostSpecification;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * An Owicki/Gries annotation of a concurrent program. Serves as proof of the program's correctness.
 *
 * We primarily use Owicki/Gries annotations for Petri programs. However, they can also be used for other models of
 * concurrent programs, such as ICFGs with fork and join edges.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <T>
 *            The type of transitions in the program model. In Petri programs, this is the type of Petri net
 *            transitions; in interprocedural CFGs, it's the type of CFG edges.
 * @param <P>
 *            The type of places, or program locations, in the program model
 * @param <M>
 *            The type of "markings", i.e., control configurations of the entire concurrent program
 */
public class OwickiGriesAnnotation<T, P, M extends Iterable<P>> implements IProof {

	/**
	 * The specification proven by this annotation.
	 */
	private final ThreadModularPrePostSpecification<P, M> mSpecification;

	/**
	 * The possible interferences between transitions and places.
	 *
	 * Strictly speaking, this is not part of the proof but merely information about the concurrency and synchronization
	 * of the program. But, as it is needed most of the time when we are working with the proof, and it needs to be
	 * backtranslated in a similar manner as the proof, we include it here.
	 */
	private final IPossibleInterferences<T, P> mPossibleInterferences;

	/**
	 * A symbol table containing both the program symbols and the ghost variables in the annotation.
	 */
	private final IIcfgSymbolTable mSymbolTable;

	/**
	 * "omega" - maps a place to a predicate that holds whenever the place has a token.
	 */
	private final Map<P, IPredicate> mAnnotationMap;

	/**
	 * "gamma" - annotates transitions with assignments of ghost variables.
	 */
	private final Map<T, GhostUpdate> mGhostUpdateMap;

	/**
	 * The ghost variables used by the annotation, mapped to their initial values.
	 */
	private final Map<IProgramVar, Term> mGhostsAndInitialValues;

	/**
	 * Creates a new Owicki/Gries annotation.
	 *
	 * @param specification
	 *            The specification proven by this Owicki/Gries annotation.
	 * @param possibleInterferences
	 *            The possible interferences accounted for by this Owicki/Gries annotation
	 * @param symbolTable
	 *            A symbol table for the annotation, which includes the program variables as well as the ghost variables
	 * @param annotationMap
	 *            The mapping from places to formulas.
	 * @param ghostsAndInitialValues
	 *            The ghost variables used by the annotation, mapped to their initial values.
	 * @param ghostUpdateMap
	 *            The annotation of transitions with ghost assignments.
	 */
	public OwickiGriesAnnotation(final ThreadModularPrePostSpecification<P, M> specification,
			final IPossibleInterferences<T, P> possibleInterferences, final IIcfgSymbolTable symbolTable,
			final Map<P, IPredicate> annotationMap, final Map<IProgramVar, Term> ghostsAndInitialValues,
			final Map<T, GhostUpdate> ghostUpdateMap) {
		assert ghostsAndInitialValues.values().stream().flatMap(t -> Arrays.stream(t.getFreeVars()))
				.allMatch(v -> ghostsAndInitialValues.keySet().stream().noneMatch(gv -> gv.getTermVariable().equals(v)))
				: "Ghost variables initializations must not refer to other ghost variables";

		assert ghostUpdateMap.values().stream()
				.allMatch(u -> ghostsAndInitialValues.keySet().containsAll(u.getAssignedVariables()))
				: "Only updates to ghost variables allowed";

		mSpecification = specification;
		mPossibleInterferences = possibleInterferences;

		mSymbolTable = symbolTable;
		mAnnotationMap = annotationMap;
		mGhostsAndInitialValues = ghostsAndInitialValues;
		mGhostUpdateMap = ghostUpdateMap;
	}

	public IIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	public Map<P, IPredicate> getAnnotationMap() {
		return Collections.unmodifiableMap(mAnnotationMap);
	}

	public Map<T, GhostUpdate> getGhostUpdateMap() {
		return Collections.unmodifiableMap(mGhostUpdateMap);
	}

	public Set<IProgramVar> getGhostVariables() {
		return Collections.unmodifiableSet(mGhostsAndInitialValues.keySet());
	}

	public Map<IProgramVar, Term> getInitialGhostValues() {
		return Collections.unmodifiableMap(mGhostsAndInitialValues);
	}

	public long size() {
		final long initSize = mGhostsAndInitialValues.entrySet().stream()
				.collect(Collectors.summingLong(x -> new DAGSize().size(x.getValue())));
		final long formulaSize = mAnnotationMap.entrySet().stream()
				.collect(Collectors.summingLong(x -> new DAGSize().size(x.getValue().getFormula())));
		final long assignSize = mGhostUpdateMap.values().stream().collect(Collectors.summingLong(GhostUpdate::size));
		return initSize + formulaSize + assignSize;
	}

	@Override
	public String toString() {
		final var sb = new StringBuilder();

		sb.append("Assertions:\n");
		appendEntries(sb, mAnnotationMap);

		sb.append("\nGhost Variables (and initial values):\n");
		appendEntries(sb, mGhostsAndInitialValues);

		sb.append("\nGhost Updates:\n");
		appendEntries(sb, mGhostUpdateMap);

		return sb.toString();
	}

	private static void appendEntries(final StringBuilder sb, final Map<?, ?> map) {
		int len = 0;
		for (final var key : map.keySet()) {
			len = Integer.max(len, Objects.toString(key).length());
		}
		for (final var entry : map.entrySet()) {
			final String keyStr = String.format("%-" + len + "s", entry.getKey());
			sb.append('\t').append(keyStr).append("  :  ").append(entry.getValue()).append('\n');
		}
	}

	@Override
	public ThreadModularPrePostSpecification<P, M> getSpecification() {
		return mSpecification;
	}

	public IPossibleInterferences<T, P> getPossibleInterferences() {
		return mPossibleInterferences;
	}
}
