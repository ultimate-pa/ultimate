/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE BoogieAST Library.
 *
 * The ULTIMATE BoogieAST Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogieAST Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieAST Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieAST Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogieAST Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import java.util.Arrays;
import java.util.Collections;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVariableCollector.LeftHandSideOccurrence;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public final class MustAssignAnalysis {
	private MustAssignAnalysis() {
		// static class
	}

	public static Set<LeftHandSideOccurrence> mustAssign(final Statement stmt) {
		return switch (stmt) {
		case final AssertStatement assertStmt -> Collections.emptySet();
		case final AssumeStatement assumeStmt -> Collections.emptySet();
		case final BreakStatement breakStmt -> Collections.emptySet();
		case final ForkStatement forkStmt -> Collections.emptySet();
		case final GotoStatement gotoStmt -> Collections.emptySet();
		case final Label label -> Collections.emptySet();
		case final ReturnStatement returnStmt -> Collections.emptySet();

		// Statements that directly assign
		case final AssignmentStatement assignStmt -> getVariables(assignStmt.getLhs());
		case final CallStatement callStmt -> getVariables(callStmt.getLhs());
		case final HavocStatement havocStmt -> getVariables(havocStmt.getIdentifiers());
		case final JoinStatement joinStmt -> getVariables(joinStmt.getLhs());

		case final IfStatement ifStmt ->
				DataStructureUtils.intersection(mustAssign(ifStmt.getThenPart()), mustAssign(ifStmt.getElsePart()));

		// In case of 0 iterations, nothing is assigned.
		case final WhileStatement whileStmt -> Collections.emptySet();

		case final AtomicStatement atomicStmt -> mustAssign(atomicStmt.getBody());
		};
	}

	public static Set<LeftHandSideOccurrence> mustAssign(final Statement[] statements) {
		return Arrays.stream(statements).flatMap(stmt -> mustAssign(stmt).stream()).collect(Collectors.toSet());
	}

	private static <T extends LeftHandSide> Set<LeftHandSideOccurrence> getVariables(final T[] leftHandSides) {
		return Arrays.stream(leftHandSides).map(MustAssignAnalysis::getVariable)
				.collect(Collectors.toUnmodifiableSet());
	}

	private static LeftHandSideOccurrence getVariable(final LeftHandSide lhs) {
		return switch (lhs) {
		case final VariableLHS vlhs -> new LeftHandSideOccurrence(vlhs.getIdentifier(),
				vlhs.getDeclarationInformation(), (BoogieType) vlhs.getType());
		case final ArrayLHS alhs -> getVariable(alhs.getArray());
		case final StructLHS slhs -> getVariable(slhs.getStruct());
		};
	}
}
