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

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * An Owicki/Gries annotation of a Petri program. Serves as proof of the program's correctness.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <LETTER>
 *            The type of program statements
 * @param <PLACE>
 *            The type of places in the Petri program
 */
public class OwickiGriesAnnotation<LETTER, PLACE> {

	/**
	 * The annotated Petri program.
	 */
	private final IPetriNet<LETTER, PLACE> mPetriNet;

	/**
	 * A symbol table containing both the program symbols and the ghost variables in the annotation.
	 */
	private final IIcfgSymbolTable mSymbolTable;

	/**
	 * "omega" - maps a place to a predicate that holds whenever the place has a token.
	 */
	private final Map<PLACE, IPredicate> mFormulaMapping;

	/**
	 * "gamma" - annotates transitions with assignments of ghost variables.
	 */
	private final Map<Transition<LETTER, PLACE>, UnmodifiableTransFormula> mAssignmentMapping;

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
	 * @param formulaMapping
	 *            The mapping from places to formulas.
	 * @param assignmentMapping
	 *            The annotation of transitions with ghost assignments.
	 * @param ghostVariables
	 *            The set of ghost variables used by the annotation.
	 * @param ghostInitAssignment
	 *            The initial assignment of ghost variables.
	 * @param net
	 *            The Petri program that is annotated.
	 * @param symbolTable
	 *            A symbol table for the annotation.
	 */
	public OwickiGriesAnnotation(final Map<PLACE, IPredicate> formulaMapping,
			final Map<Transition<LETTER, PLACE>, UnmodifiableTransFormula> assignmentMapping,
			final Set<IProgramVar> ghostVariables, final Map<IProgramVar, Term> ghostInitAssignment,
			final IPetriNet<LETTER, PLACE> net, final IIcfgSymbolTable symbolTable) {

		assert ghostInitAssignment.keySet().stream()
				.allMatch(ghostVariables::contains) : "Initial value only allowed for ghost variables";

		mFormulaMapping = formulaMapping;
		mAssignmentMapping = assignmentMapping;
		mGhostVariables = ghostVariables;
		mGhostInitAssignment = ghostInitAssignment;
		mPetriNet = net;
		mSymbolTable = symbolTable;
	}

	public IPetriNet<LETTER, PLACE> getPetriNet() {
		return mPetriNet;
	}

	public IIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	public Map<PLACE, IPredicate> getFormulaMapping() {
		return mFormulaMapping;
	}

	public Map<Transition<LETTER, PLACE>, UnmodifiableTransFormula> getAssignmentMapping() {
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
		final long assignSize = mAssignmentMapping.entrySet().stream()
				.collect(Collectors.summingLong(x -> sizeComputation.size(x.getValue().getFormula())));
		return initSize + formulaSize + assignSize;
	}
}
