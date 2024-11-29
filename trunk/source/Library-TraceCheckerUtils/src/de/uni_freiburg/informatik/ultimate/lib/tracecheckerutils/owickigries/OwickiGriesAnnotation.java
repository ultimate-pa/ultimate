/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries;

import java.util.Arrays;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * An Owicki/Gries annotation of a concurrent program. Serves as proof of the program's correctness.
 *
 * We primarily use Owicki/Gries annotations for Petri programs. However, they can also be used for other models of
 * concurrent programs, such as interprocedural CFGs.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <T>
 *            The type of transitions in the program model. In Petri programs, this is the type of Petri net
 *            transitions; in interprocedural CFGs, it's the type of CFG edges.
 * @param <P>
 *            The type of places, or program locations, in the program model
 */
public class OwickiGriesAnnotation<T, P> {
	/**
	 * A symbol table containing both the program symbols and the ghost variables in the annotation.
	 */
	private final IIcfgSymbolTable mSymbolTable;

	/**
	 * "omega" - maps a place to a predicate that holds whenever the place has a token.
	 */
	private final Map<P, IPredicate> mFormulaMapping;

	/**
	 * "gamma" - annotates transitions with assignments of ghost variables.
	 */
	private final Map<T, GhostUpdate> mAssignmentMapping;

	/**
	 * Set of ghost variables used by the annotation.
	 */
	private final Set<IProgramVar> mGhostVariables;

	/**
	 * Initial assignment of ghost variables.
	 */
	private final Map<IProgramVar, Term> mGhostInitAssignment;

	/**
	 * Creates a new Owicki/Gries annotation.
	 *
	 * @param net
	 *            The Petri program that is annotated.
	 * @param symbolTable
	 *            A symbol table for the annotation, which includes the program variables as well as the ghost variables
	 * @param formulaMapping
	 *            The mapping from places to formulas.
	 * @param ghostVariables
	 *            The set of ghost variables used by the annotation.
	 * @param ghostInitAssignment
	 *            The initial assignment of ghost variables.
	 * @param assignmentMapping
	 *            The annotation of transitions with ghost assignments.
	 */
	public OwickiGriesAnnotation(final IIcfgSymbolTable symbolTable, final Map<P, IPredicate> formulaMapping,
			final Set<IProgramVar> ghostVariables, final Map<IProgramVar, Term> ghostInitAssignment,
			final Map<T, GhostUpdate> assignmentMapping) {
		assert ghostInitAssignment.keySet().stream()
				.allMatch(ghostVariables::contains) : "Initial value only allowed for ghost variables";

		// TODO should we allow more here? e.g. any term that does not itself contain a ghost variable?
		// TODO we cannot allow all terms there are, otherwise we might have contradictions: a==!b and b==a
		// TODO (or, depending how we interpret it, the values depend on an order between ghost initializations)
		// assert ghostInitAssignment.values().stream().allMatch(
		// v -> v.getFreeVars().length == 0) : "Initial values must be literal terms without free variables";
		assert ghostInitAssignment.values().stream().flatMap(t -> Arrays.stream(t.getFreeVars()))
				.allMatch(v -> ghostVariables.stream().noneMatch(gv -> gv.getTermVariable()
						.equals(v))) : "Ghost variables initializations must not refer to other ghost variables";

		assert assignmentMapping.values().stream().allMatch(
				u -> ghostVariables.containsAll(u.getAssignedVariables())) : "Only updates to ghost variables allowed";

		mSymbolTable = symbolTable;
		mFormulaMapping = formulaMapping;
		mGhostVariables = ghostVariables;
		mGhostInitAssignment = ghostInitAssignment;
		mAssignmentMapping = assignmentMapping;
	}

	public IIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	public Map<P, IPredicate> getFormulaMapping() {
		return mFormulaMapping;
	}

	public Map<T, GhostUpdate> getAssignmentMapping() {
		return mAssignmentMapping;
	}

	public Set<IProgramVar> getGhostVariables() {
		return mGhostVariables;
	}

	public Map<IProgramVar, Term> getGhostAssignment() {
		return mGhostInitAssignment;
	}

	public long size() {
		final DAGSize sizeComputation = new DAGSize();
		final long initSize = mGhostInitAssignment.entrySet().stream()
				.collect(Collectors.summingLong(x -> sizeComputation.size(x.getValue())));
		final long formulaSize = mFormulaMapping.entrySet().stream()
				.collect(Collectors.summingLong(x -> sizeComputation.size(x.getValue().getFormula())));
		final long assignSize = mAssignmentMapping.values().stream().collect(Collectors.summingLong(GhostUpdate::size));
		return initSize + formulaSize + assignSize;
	}

	@Override
	public String toString() {
		final var sb = new StringBuilder();

		sb.append("Assertions:\n");
		appendEntries(sb, mFormulaMapping);

		sb.append("\nGhost Variables (and initial values):\n");
		appendEntries(sb, mGhostInitAssignment);

		sb.append("\nGhost Updates:\n");
		appendEntries(sb, mAssignmentMapping);

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
}
