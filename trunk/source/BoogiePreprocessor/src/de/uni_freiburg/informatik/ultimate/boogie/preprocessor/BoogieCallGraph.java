/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Computes call graph for Boogie programs.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class BoogieCallGraph {

	private HashRelation<String, String> mCallGraph;

	public BoogieCallGraph(final Unit unit) {
		this(unit.getDeclarations());
	}

	public BoogieCallGraph(final Declaration[] declarations) {
		constructCallGraph(declarations);
	}

	/**
	 * Return a set that contains this procedure and all procedures that are recursively called by this procedure.
	 */
	public Set<String> computeCallClosure(final String start) {
		final Set<String> result = new HashSet<>();
		if (mCallGraph.getDomain().contains(start)) {
			final ArrayDeque<String> worklist = new ArrayDeque<>();
			worklist.add(start);
			result.add(start);
			while (!worklist.isEmpty()) {
				final String elem = worklist.remove();
				final Set<String> callees = mCallGraph.getImage(elem);
				for (final String callee : callees) {
					final boolean modified = result.add(callee);
					if (modified) {
						worklist.add(callee);
					}
				}
			}
		}
		return result;
	}

	private void constructCallGraph(final Declaration[] declarations) {
		for (final Declaration decl : declarations) {
			if (decl instanceof Procedure) {
				final Procedure proc = (Procedure) decl;
				if (proc.getBody() != null) {
					processStatementList(proc.getIdentifier(), proc.getBody().getBlock());
				}
			}
		}
	}

	private void processStatementList(final String currentProcedure, final Statement[] block) {
		for (final Statement st : block) {
			if (st instanceof GotoStatement) {
				// do nothing
			} else if (st instanceof Label) {
				// do nothing
			} else if (st instanceof CallStatement) {
				processCallStatement(currentProcedure, (CallStatement) st);
			} else if (st instanceof AssignmentStatement) {
				// do nothing
			} else if (st instanceof AssumeStatement) {
				// do nothing
			} else if (st instanceof AssertStatement) {
				// do nothing
			} else if (st instanceof HavocStatement) {
				// do nothing
			} else if (st instanceof ReturnStatement) {
				// do nothing
			} else if (st instanceof BreakStatement) {
				// do nothing
			} else if (st instanceof IfStatement) {
				processStatementList(currentProcedure, ((IfStatement) st).getThenPart());
				processStatementList(currentProcedure, ((IfStatement) st).getElsePart());
			} else if (st instanceof WhileStatement) {
				processStatementList(currentProcedure, ((WhileStatement) st).getBody());
			} else if (st instanceof ForkStatement) {
				// do nothing
			} else if (st instanceof JoinStatement) {
				// do nothing
			} else if (st instanceof AtomicStatement) {
				processStatementList(currentProcedure, ((AtomicStatement) st).getBody());
			} else {
				throw new AssertionError("Unsuppored " + st);
			}
		}

	}

	private void processCallStatement(final String currentProcedure, final CallStatement st) {
		mCallGraph.addPair(currentProcedure, st.getMethodName());
	}

}
